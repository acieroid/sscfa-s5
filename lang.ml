open Prelude
open Shared
open Env
open Store
open Lattice

let gc = ref true

module D = Delta
module S = Ljs_syntax
module O = Obj_val
module F = Frame

module type Lang_signature =
sig
  type exp
  val string_of_exp : exp -> string

  (** A configuration is like a state, but can contain more information, such as
      a stack summary. This is what will be contained in the state graph. *)
  type conf
  val string_of_conf : conf -> string
  module ConfOrdering : BatInterfaces.OrderedType with type t = conf

  (** Global information that can be useful. It remains constant throughout the
      evaluation, and is passed to the step function at each step. It can for
      example be used to model a global environment and/or store *)
  type global

  (** The frame is what the stack is made up from *)
  type frame
  val string_of_frame : frame -> string
  module FrameOrdering : BatInterfaces.OrderedType with type t = frame

  (** A frame can be either pushed on or popped off the stack. A transition can
      also leave the stack unchange *)
  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged
  module StackChangeOrdering : BatInterfaces.OrderedType with type t = stack_change
  val string_of_stack_change : stack_change -> string

  (** The injection function injects an expression into an initial
      configuration. It can take a previous configuration as argument,
      to extract some useful information from it (eg. the environment/store).
      It should also construct the global value that will be passed to the step
      function. *)
  val inject : exp -> conf option -> conf * global

  (** The step function steps from one configuratino to the next. It takes a
      potential (configuration, frame) pair that respectively represents the
      previous configuration and the top of the stack. It also takes the global
      value as argument, but can't modify this global value. It should return
      a list of new configurations, paired with the corresponding stack change.
   *)
  val step : conf -> global -> (conf * frame) option -> (stack_change * conf) list
end

module LJS =
struct
  type exp = S.exp
  let string_of_exp = string_of_exp

  type frame = F.t
  let string_of_frame = F.to_string

  type v = F.value (* shorthand *)

  type control =
    | Exp of S.exp
    | Prop of S.prop
    | PropVal of O.prop
    | Val of F.value
    | Frame of (control * F.t)
    | Exception of F.exc

  let string_of_control = function
    | Exp exp -> "Exp(" ^ (string_of_exp exp) ^ ")"
    | Prop prop -> "Prop(" ^ (string_of_prop prop) ^ ")"
    | Val v -> "Val(" ^ (F.string_of_value v) ^ ")"
    | PropVal v -> "PropVal(" ^ (O.string_of_prop v) ^ ")"
    | Frame (exp, f) -> "Frame(" ^ (F.to_string f) ^ ")"
    | Exception (`Break (l, _)) -> "Break(" ^ l ^ ")"
    | Exception (`Throw v) -> "Throw(" ^ (F.string_of_value v) ^ ")"

  type state = {
    control : control;
    env : Env.t;
    vstore : ValueStore.t;
    ostore : ObjectStore.t;
    time : Time.t;
  }

  let string_of_state state =
    (*    Printf.sprintf "Env: %d, VStore: %d, OStore: %d"
          (Env.size state.env) (ValueStore.size state.vstore) (ObjectStore.size state.ostore) *)
    (string_of_control state.control)

  let compare_state state state' =
    order_concat [lazy (Pervasives.compare state.control state'.control);
                  lazy (Env.compare state.env state'.env);
                  lazy (ValueStore.compare state.vstore state'.vstore);
                  lazy (ObjectStore.compare state.ostore state'.ostore);
                  lazy (Time.compare state.time state'.time)]

  type global = {
    genv : Env.t;
    gvstore : ValueStore.t;
    gostore : ObjectStore.t;
  }

  module GCStackSummary =
  struct
    (* Stack summary used for garbage collection  *)
    type t = AddressSet.t
    let empty = AddressSet.empty
    let compare = AddressSet.compare
    let to_string ss = "[" ^ (BatString.concat ", "
                                (BatList.map Address.to_string
                                   (AddressSet.elements ss))) ^ "]"

    let push (ss : t) (global : global) (f : F.t) =
      AddressSet.union ss (Frame.touch f global.genv)
  end
  module MCFAStackSummary =
  struct
    (* Stack summary used for [m = 1]-CFA addresses *)
    type t = { last : F.t option; mtime : K1Time.t }
    let empty = { last = None; mtime = K1Time.initial }
    let compare ss ss' =
      order_concat [lazy (K1Time.compare ss.mtime ss'.mtime);
                    lazy (BatOption.compare ~cmp:F.compare ss.last ss'.last)]
    let push (ss : t) (global : global) (f : F.t) =
      {last = Some f;
       mtime = match ss.last with
         | Some (F.AppFun (p, [], _))
         | Some (F.AppArgs (p, _, _, [], _)) ->
           print_endline ("Push " ^ (Pos.string_of_pos p));
           K1Time.tick p ss.mtime
         | _ -> begin match f with
           | F.RestoreEnv (p, _) ->
             print_endline ("Push2 " ^ (Pos.string_of_pos p));
             K1Time.tick p ss.mtime
           | _ -> ss.mtime
           end}
  end
  module StackSummary =
  struct
    type t = GCStackSummary.t * MCFAStackSummary.t
    let empty = (GCStackSummary.empty, MCFAStackSummary.empty)
    let compare (g, m) (g', m') =
      order_concat [lazy (GCStackSummary.compare g g');
                    lazy (MCFAStackSummary.compare m m')]
    let push (g, m) global f =
      (GCStackSummary.push g global f, MCFAStackSummary.push m global f)
  end

  type conf = state * StackSummary.t

  let string_of_conf (state, ss) = string_of_state state

  let compare_conf (state, ss) (state', ss') =
    order_comp (compare_state state state') (StackSummary.compare ss ss')

  let which_env id env env' : Env.t =
    if Env.contains id env then
      env
    else if Env.contains id env' then
      env'
    else begin
      print_endline ("Identifier cannot be resolved: " ^ id);
      raise Not_found
    end

  let which_ostore (a : Address.t) (ostore : ObjectStore.t) (ostore' : ObjectStore.t)
    : ObjectStore.t =
    if ObjectStore.contains a ostore then
      ostore
    else if ObjectStore.contains a ostore' then
      ostore'
    else begin
      print_endline ("Object lives at an unreachable address: " ^
                     (Address.to_string a));
      raise Not_found
    end

  let ostore_set a obj ostore ostore' : ObjectStore.t =
    if ObjectStore.contains a ostore then
      (* Object already in the state store, update it *)
      ObjectStore.set a obj ostore
    else if ObjectStore.contains a ostore' then
      (* Object is only in the global store, add the modified object to the
         state store, using a join as it is a new object in this store *)
      ObjectStore.join a obj ostore
    else begin
      print_endline ("Cannot set object at unreachable location: " ^
                     (Address.to_string a));
      raise Not_found
    end

  let which_vstore (a : Address.t) (vstore : ValueStore.t) (vstore' : ValueStore.t)
    : ValueStore.t =
    if ValueStore.contains a vstore then
      vstore
    else if ValueStore.contains a vstore' then
      vstore'
    else begin
      print_endline ("Value lives at an unreachable address: " ^
                     (Address.to_string a));
      raise Not_found
    end

  (** Isolate garbage collection specific functions *)
  module GC =
  struct

    let touch vstore ostore global v =
      let rec aux acc visited_objs : AValue.t -> AddressSet.t = function
        | `Null | `True | `False | `BoolT | `Num _ | `NumT
        | `Str _ | `StrT | `Undef | `Bot -> acc
        | `Clos (env, args, exp) ->
          AddressSet.union acc (Env.range env)
        (* Initially, it was the following two lines, but as a closure's
           environment only contains its free variable, it is simpler to do as
           it is done now *)
        (* (Frame.addresses_of_vars (IdSet.diff (S.free_vars exp)
                                        (IdSet.from_list args)) env) *)
        | `Obj a -> if AddressSet.mem a visited_objs then
            acc
          else
            if ObjectStore.contains a ostore then
              match ObjectStore.lookup a ostore with
              | `Obj obj -> aux_obj (AddressSet.add a acc) (AddressSet.add a visited_objs) obj
              | `ObjT -> failwith "touch: an object was too abtsract"
            else if ObjectStore.contains a global.gostore then
              (* ignore addresses in the global store, as they are not
                 reclaimable and can't point to reclaimable addresses *)
              acc
            else begin
              print_endline ("GC reached a non-reachable address: " ^
                             (Address.to_string a));
              raise Not_found
            end
        | `ClosT | `ObjT | `Top -> failwith "touch: a value was too abstract"
      and aux_obj acc visited_objs ((attrs, props) : O.t) =
        aux_obj_props (List.fold_left AddressSet.union acc
                         [aux acc visited_objs attrs.O.code;
                          aux acc visited_objs attrs.O.proto;
                          aux acc visited_objs attrs.O.primval;
                          aux acc visited_objs attrs.O.klass;
                          aux acc visited_objs attrs.O.extensible])
          visited_objs
          (IdMap.bindings props)
      and aux_obj_props acc visited_objs props =
        match props with
        | [] -> acc
        | (_, O.Data ({O.value = v; O.writable = w}, enum, config)) :: props ->
          aux_obj_props (List.fold_left AddressSet.union acc
                           [aux acc visited_objs v;
                            aux acc visited_objs w;
                            aux acc visited_objs enum;
                            aux acc visited_objs config]) visited_objs props
        | (_, O.Accessor ({O.getter = g; O.setter = s}, enum, config)) :: props ->
          aux_obj_props (List.fold_left AddressSet.union acc
                           [aux acc visited_objs g;
                            aux acc visited_objs s;
                            aux acc visited_objs enum;
                            aux acc visited_objs config]) visited_objs props in
      match v with
      | #AValue.t as v -> aux AddressSet.empty AddressSet.empty v
      | `StackObj obj -> aux_obj AddressSet.empty AddressSet.empty obj

    let rec control_root control env vstore ostore global
      : AddressSet.t = match control with
      | Exp e -> Frame.addresses_of_vars (S.free_vars e) env global.genv
      | Prop (S.Data ({S.value = v; _}, _, _)) ->
        Frame.addresses_of_vars (S.free_vars v) env global.genv
      | Prop (S.Accessor ({S.getter = g; S.setter = s}, _, _)) ->
        Frame.addresses_of_vars (IdSet.union (S.free_vars g) (S.free_vars s))
          env global.genv
      | Frame (control, frame) ->
        AddressSet.union (control_root control env vstore ostore global)
          (Frame.touch frame global.genv)
      | Val v -> touch vstore ostore global v
      | PropVal (O.Data ({O.value = v1; O.writable = v2}, enum, config) as prop)
      | PropVal (O.Accessor ({O.getter = v1; O.setter = v2}, enum, config) as prop) ->
        Frame.addresses_of_vals (Frame.vals_of_prop prop)
      | Exception (`Break (_, v))
      | Exception (`Throw v) ->
        Frame.addresses_of_vals [v]

    let root (state, (ss, _)) global : AddressSet.t =
      AddressSet.union ss (control_root state.control state.env
                             state.vstore state.ostore global)

    let touching_rel1 (vstore : ValueStore.t) (ostore : ObjectStore.t)
        (global : global) (addr : Address.t)
      : AddressSet.t = let v = match addr with
      | `ObjAddress _ -> `Obj addr
      | `VarAddress _ ->
        let store = which_vstore addr vstore global.gvstore in
        ((ValueStore.lookup addr store) :> v)
      in
      touch vstore ostore global v

    let touching_rel vstore ostore global addr =
      let rec aux todo acc =
        if AddressSet.is_empty todo then
          acc
        else
          let a = AddressSet.choose todo in
          if AddressSet.mem a acc then
            aux (AddressSet.remove a todo) acc
          else
            let addrs = touching_rel1 vstore ostore global a in
            aux (AddressSet.remove a (AddressSet.union addrs todo))
              (AddressSet.add a acc)
      in
      aux (AddressSet.singleton addr) AddressSet.empty

    let reachable ((state, ss) : conf) (global : global) : AddressSet.t =
      let r = root (state, ss) global in
      AddressSet.fold (fun a acc ->
          AddressSet.union acc (touching_rel state.vstore state.ostore global a))
        r AddressSet.empty

    let gc ((state, ss) : conf) (global : global) : conf =
      let r = reachable (state, ss) global in
      ({state with
        vstore = ValueStore.restrict r state.vstore;
        ostore = ObjectStore.restrict r state.ostore},
       ss)
  end

  type stack_change =
    | StackPop of F.t
    | StackPush of F.t
    | StackUnchanged

  let compare_stack_change g1 g2 = match (g1, g2) with
    | StackPop f1, StackPop f2 -> F.compare f1 f2
    | StackPush f1, StackPush f2 -> F.compare f1 f2
    | StackUnchanged, StackUnchanged -> 0
    | StackPop _, _ -> 1
    | _, StackPop _ -> -1
    | StackPush _, StackUnchanged -> 1
    | StackUnchanged, _ -> -1

  let string_of_stack_change = function
    | StackPush f -> "+" ^ (F.to_string f)
    | StackPop f -> "-" ^ (F.to_string f)
    | StackUnchanged -> "e"

  module FrameOrdering = F

  module ConfOrdering = struct
    type t = conf
    let compare = compare_conf
  end

  module StackChangeOrdering = struct
    type t = stack_change
    let compare = compare_stack_change
  end

  let alloc_var (p : Pos.t) (id : string) _ ((state, (_, ss)) : conf) =
    (* m-CFA *)
    Address.alloc_var p id ss.MCFAStackSummary.mtime
    (* k-CFA *)
    (* Address.alloc_var p id state.time *)

  let alloc_obj (p : Pos.t) (id : string) _ ((state, (_, ss)) : conf) =
    (* m-CFA *)
    Address.alloc_obj p id ss.MCFAStackSummary.mtime
    (* k-CFA *)
    (* Address.alloc_obj p id state.time *)

  let alloc_if_necessary (p : Pos.t) ((state, _) as conf : conf) id = function
    | #AValue.t as v -> (state.ostore, v)
    | `StackObj obj ->
      let a = alloc_obj p id obj conf in
      let ostore' = ObjectStore.join a (`Obj obj) state.ostore in
      (ostore', `Obj a)

  let inject (exp : S.exp) (c : conf option) : (conf * global) =
    let empty = { control = Exp exp; env = Env.empty; vstore = ValueStore.empty;
                  ostore = ObjectStore.empty; time = Time.initial } in
    let empty_global = { genv = Env.empty; gvstore = ValueStore.empty;
                         gostore = ObjectStore.empty } in
    (empty, StackSummary.empty),
    BatOption.map_default
      (fun (init, ss) ->
         (* Perform GC to get rid of all non-needed values in the global
            env/store *)
         let (init', _) = GC.gc ({init with control = Exp exp}, ss) empty_global in
         {genv = init'.env; gvstore = init'.vstore; gostore = init'.ostore})
      empty_global c

  let rec get_prop obj prop ostore global = match obj with
    | `Obj a ->
      let store = which_ostore a ostore global.gostore in
      begin match ObjectStore.lookup a store with
        | `Obj ({O.proto = pvalue; _}, props) ->
          begin try Some (IdMap.find prop props)
            with Not_found -> get_prop (pvalue :> v) prop ostore global
          end
        | `ObjT -> failwith "get_prop: too abstracted"
      end
    | `StackObj ({O.proto = pvalue; _}, props) ->
      begin try Some (IdMap.find prop props)
        with Not_found -> get_prop (pvalue :> v) prop ostore global
      end
    | `ObjT -> failwith "get_prop: too abstracted"
    | `Null -> None
    | #AValue.t as v -> failwith ("get_prop on non-object: " ^ (AValue.to_string v))

  (** Do the selection of parameters that will be used in timestamps (for
      parameter sensitive addresses) *)
  let select_params args : (string * PSTime.v) list =
    let f (n, v) = match v with
        | #PSTime.v as v' -> Some (n, v')
        | _ -> None in
    BatList.filter_map f args

  let rec apply_fun (p : Pos.t) f args ((state, ss) as conf : conf) (global : global)
    : (S.exp * state) = match f with
    | `Clos (env', args', body) ->
      if (List.length args) != (List.length args') then
        (* This is *not* about Javascript closures, as an arity mismatch when
           applying a function in Javascript does not lead to an error. However,
           such a mismatch should not happen in S5 code, and that is why this
           is an internal error *)
        failwith "Arity mismatch"
      else
        let alloc_arg v name (vstore, ostore, env) =
          let (ostore', v') = alloc_if_necessary p conf name v in
          let conf' = ({state with ostore = ostore'}, ss) in
          let a = alloc_var p name v' conf' in
          (ValueStore.join a v' vstore,
           ostore',
           Env.extend name a env) in
        let (vstore', ostore', env') =
          BatList.fold_right2 alloc_arg args args' (state.vstore, state.ostore, env') in
        (body, {state with env = env'; vstore = vstore'; ostore = ostore';
                           (* k-CFA *)
                           time = Time.tick (S.pos_of body) state.time
                           (* Parameter-sensitive k-CFA *)
                           (* time = Time.tick ((S.pos_of body),
                                             select_params (BatList.combine args' args))
                               state.time *)})
    | `ClosT -> failwith "Closure too abstracted"
    | `Obj a ->
      let store = which_ostore a state.ostore global.gostore in
      begin match ObjectStore.lookup a store with
        | `Obj ({O.code = `Clos f; _}, _) ->
          apply_fun p (`Clos f) args conf global
        | `ObjT -> failwith "Applied too abstracted object"
        (* TODO: should this be an S5 error or a JS error? *)
        | _ -> failwith "Applied object without code attribute"
      end
    | `ObjT -> failwith "Object too abstracted when applying function"
    | `StackObj ({O.code = `Clos f; _}, _) ->
      apply_fun p (`Clos f) args conf global
    | `StackObj _ -> failwith "Applied object without code attribute"
    (* TODO: S5 or JS error? *)
    | _ -> failwith "Applied non-function"

  let apply_frame (v : v) (frame : frame) ((state, ss) as conf : conf) (global : global)
    : state list = match frame with
    | F.Let (p, id, body, env') ->
      let a = alloc_var p id id conf in
      let env'' = Env.extend id a env' in
      let ostore', v' = alloc_if_necessary p conf id v in
      let vstore' = ValueStore.join a v' state.vstore in
      [{state with control = Exp body; env = env''; vstore = vstore'; ostore = ostore'}]
    (* ObjectAttrs of string * O.t * (string * S.exp) list * (string * prop) list * Env.t *)
    | F.ObjectAttrs (p, name, obj, [], [], env') ->
      let ostore', v' = alloc_if_necessary p conf name v in
      let obj' = O.set_attr_str obj name v' in
      [{state with control = Val (`StackObj obj'); env = env'; ostore = ostore' }]
    | F.ObjectAttrs (p, name, obj, [], (name', prop) :: props, env') ->
      let ostore', v' = alloc_if_necessary p conf name v in
      let obj' = O.set_attr_str obj name v' in
      [{state with control = Frame (Prop prop, F.ObjectProps (p, name', obj', props, env'));
                   ostore = ostore'; env = env'}]
    | F.ObjectAttrs (p, name, obj, (name', attr) :: attrs, props, env') ->
      let ostore', v' = alloc_if_necessary p conf name v in
      let obj' = O.set_attr_str obj name v' in
      [{state with control = Frame (Exp attr, F.ObjectAttrs (p, name', obj', attrs, props, env'));
                   ostore = ostore'; env = env'}]
    (* PropData of (O.data * AValue.t * AValue.t) * Env.t *)
    | F.PropData (p, (data, enum, config), env') ->
      let ostore', v' = alloc_if_necessary p conf "propdata" v in
      [{state with control = PropVal (O.Data ({data with O.value = v'},
                                              enum, config));
                   ostore = ostore'; env = env'}]
    (* PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t *)
    | F.PropAccessor (p, None, (accessor, enum, config), env') ->
      let ostore', v' = alloc_if_necessary p conf "propacc-set" v in
      [{state with control = PropVal (O.Accessor ({accessor with O.setter = v'},
                                                  enum, config));
                   ostore = ostore'; env = env'}]
    | F.PropAccessor (p, Some exp, (accessor, enum, config), env') ->
      let ostore', v' = alloc_if_necessary p conf "propacc-get" v in
      [{state with control = Frame (Exp exp, (F.PropAccessor
                                                (S.pos_of exp, None,
                                                 ({accessor with O.getter = v'},
                                                  enum, config), env')));
                   ostore = ostore'; env = env'}]
    | F.Seq (exp, env') ->
      [{state with control = Exp exp; env = env'}]
    | F.AppFun (p, [], env') ->
      let (exp, state') = apply_fun p v [] conf global in
      [{state' with control = Exp exp}]
    | F.AppFun (p, arg :: args, env') ->
      [{state with control = Frame (Exp arg, (F.AppArgs (p, v, [], args, env')));
                   env = env'}]
    | F.AppArgs (p, f, vals, [], env') ->
      let args = BatList.rev (v :: vals) in
      let (exp, state') = apply_fun p f args conf global in
      [{state' with control = Exp exp}]
    | F.AppArgs (p, f, vals, arg :: args, env') ->
      [{state with control = Frame (Exp arg, (F.AppArgs (p, f, v :: vals, args, env')));
                   env = env'}]
    | F.Op1App (p, op, env') ->
      (* TODO: we should avoid allocating for op1 and op2 *)
      let ostore', v' = alloc_if_necessary p conf ("op1-" ^ op) v in
      [{state with control = Val ((D.op1 ostore' global.gostore op v') :> v);
                   ostore = ostore'; env = env'}]
    | F.Op2Arg (p, op, arg2, env') ->
      [{state with control = Frame (Exp arg2, (F.Op2App (p, op, v, env')));
                   env = env'}]
    | F.Op2App (p, op, arg1, env') ->
      (* TODO: we should avoid allocating for op1 and op2 *)
      let ostore', arg1' = alloc_if_necessary p conf ("op2-" ^ op ^ "arg1") arg1 in
      let conf' = ({state with ostore = ostore'}, ss) in
      let ostore'', arg2' = alloc_if_necessary p conf' ("op2-" ^ op ^ "arg2") v in
      [{state with control = Val ((D.op2 ostore'' global.gostore op arg1' arg2') :> v);
                   ostore = ostore''; env = env'}]
    | F.If (cons, alt, env') -> begin match v with
        | `True -> [{state with control = Exp cons; env = env'}]
        | `BoolT | `Top -> [{state with control = Exp cons; env = env'};
                            {state with control = Exp alt; env = env'}]
        | _ -> [{state with control = Exp alt; env = env'}]
      end
    | F.GetFieldObj (p, field, body, env') ->
      [{state with control = Frame (Exp field, F.GetFieldField (p, v, body, env'));
                   env = env'}]
    | F.GetFieldField (p, obj, body, env') ->
      [{state with control = Frame (Exp body, F.GetFieldBody (p, obj, v, env'));
                   env = env'}]
    | F.GetFieldBody (p, obj, field, env') ->
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match get_prop (`Obj a) s state.ostore global with
            | Some (O.Data ({O.value = v; _}, _, _)) ->
              [{state with control = Val (v :> v); env = env'}]
            | Some (O.Accessor ({O.getter = g; _}, _, _)) ->
              let (body, state') = apply_fun p (g :> v) [obj; v] conf global in
              [{state' with control = Frame (Exp body, F.RestoreEnv (p, env'))}]
            | None -> [{state with control = Val `Undef; env = env'}]
          end
        | `Obj _, `StrT ->
          (* We can handle this case more precisely by returning a state for
             each possible value of a field in this object *)
          [{state with control = Val `Top; env = env'}]
        | `ObjT, _ -> failwith "GetFieldBody: object too abstracted"
        | o, s -> failwith ("GetFieldBody on a non-object or non-string field: " ^
                            (F.string_of_value o) ^ ", " ^ (F.string_of_value s))
      end
    | F.SetFieldObj (p, field, newval, body, env') ->
      [{state with control = Frame (Exp field, F.SetFieldField (p, v, newval, body, env'));
                   env = env'}]
    | F.SetFieldField (p, obj, newval, body, env') ->
      [{state with control = Frame (Exp newval, F.SetFieldNewval (p, obj, v, body, env'));
                   env = env'}]
    | F.SetFieldNewval (p, obj, field, body, env') ->
      [{state with control = Frame (Exp body, F.SetFieldArgs (p, obj, field, v, env'));
                   env = env'}]
    | F.SetFieldArgs (p, obj_, field, newval, env') ->
      (* TODO: allow objects to contain objects that don't live in the store *)
      let body = v in
      let ostore', obj = alloc_if_necessary p conf "setfieldargs-o" obj_ in
      let state = {state with ostore = ostore'} in
      let conf = (state, ss) in
      begin match obj, field with
        | `Obj a, `Str s ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | `Obj ({O.extensible = extensible; _} as attrs, props) ->
              begin match get_prop obj s state.ostore global with
                | Some (O.Data ({O.writable = `True; _}, enum, config)) ->
                  let (enum, config) = if O.has_prop (attrs, props) (`Str s) then
                      (enum, config)
                    else
                      (`True, `True) in
                  let ostore', newval' = alloc_if_necessary p conf ("setfieldargs" ^ s) newval in
                  let newobj = O.set_prop (attrs, props) s
                      (O.Data ({O.value = newval'; O.writable = `True},
                               enum, config)) in
                  let ostore'' = ostore_set a (`Obj newobj) state.ostore global.gostore in
                  [{state with control = Val (newval :> v); env = env'; ostore = ostore''}]
                | Some (O.Data _)
                | Some (O.Accessor ({O.setter = `Undef; _}, _, _)) ->
                  [{state with control = Exception (`Throw (`Str "uwritable-field"))}]
                | Some (O.Accessor ({O.setter = setter; _}, _, _)) ->
                  let (exp, state') = apply_fun p (setter :> v) [obj; body] conf global in
                  [{state' with control = Frame (Exp exp, F.RestoreEnv (p, env'))}]
                | None ->
                  let t =
                    let ostore', newval' = alloc_if_necessary p conf ("setfieldargs" ^ s) newval in
                    let newobj = O.set_prop (attrs, props) s
                        (O.Data ({O.value = newval'; O.writable = `True},
                                 `True, `True)) in
                    let ostore'' = ostore_set a (`Obj newobj) state.ostore global.gostore in
                    {state with control = Val (newval' :> v); env = env'; ostore = ostore''} in
                  let f = {state with control = Val `Undef} in
                  match Delta.prim_to_bool extensible with
                  | `True -> [t]
                  | `False -> [f]
                  | `BoolT -> [t; f]
              end
            | `ObjT -> failwith "SetFieldArgs: object too abstracted"
          end
        | `StackObj _, _ -> failwith "TODO: SetFieldArgs on a stack object"
        | v1, v2 -> failwith ("SetFieldArgs on a non-object or non-string: " ^
                               (F.string_of_value v1) ^ ", " ^ (F.string_of_value v2))
      end
    | F.GetAttrObj (pattr, field, env') ->
      [{state with control = Frame (Exp field, F.GetAttrField (pattr, v, env'));
                   env = env'}]
    | F.GetAttrField (pattr, obj, env') ->
      begin match obj, v with
        | `Obj a, `Str s ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | `Obj o -> let attr = O.get_attr o pattr (`Str s) in
              [{state with control = Val (attr :> v); env = env'}]
            | `ObjT -> failwith "GetAttrField: object too abstracted"
          end
        | `StackObj obj, `Str s ->
          let attr = O.get_attr obj pattr (`Str s) in
          [{state with control = Val (attr :> v); env = env'}]
        | `Obj _, `StrT | `StackObj _, `StrT ->
          failwith "GetAttrField with a top string as field"
        | `ObjT, _ -> failwith "GetAttrField on a top object"
        | _ -> failwith "GetAttrField on a non-object or non-string"
      end
    | F.SetAttrObj (p, pattr, field, newval, env') ->
      [{state with control = Frame (Exp field, F.SetAttrField (p, pattr, v,
                                                               newval, env'));
                   env = env'}]
    | F.SetAttrField (p, pattr, obj, newval, env') ->
      [{state with control = Frame (Exp newval, F.SetAttrNewval (p, pattr, obj,
                                                                 v, env'));
                   env = env'}]
    | F.SetAttrNewval (p, pattr, obj_, field, env') ->
      let ostore', obj = alloc_if_necessary p conf "setattrnewvalobj" obj_ in
      let conf' = ({state with ostore = ostore'}, ss) in
      let ostore'', newval = alloc_if_necessary p conf' "setattrnewvalv" v in
      begin match obj, field with
        | `Obj a, `Str s ->
          let store = which_ostore a ostore'' global.gostore in
          begin match ObjectStore.lookup a store with
            | `Obj o ->
              let newobj = O.set_attr o pattr s newval in
              let ostore''' = ostore_set a (`Obj newobj) ostore'' global.gostore in
              [{state with control = Val `True; env = env'; ostore = ostore'''}]
            | `ObjT -> failwith "SetAttrNewval: object too abstracted"
          end
        | `ObjT, _ -> failwith "SetAttrNewval: object too abstracted"
        | _ -> failwith "SetAttrNewval on a non-object or non-string attribute"
      end
    | F.GetObjAttr (oattr, env') -> begin match v with
        | `Obj a ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | `Obj obj -> [{state with control = Val ((O.get_obj_attr obj oattr) :> v); env = env'}]
            | `ObjT ->
              (* TODO: Could be more precise here *)
              [{state with control = Val `Top; env = env'}]
          end
        | `ObjT -> failwith "GetObjAttr: object too abstracted"
        | _ -> failwith "GetObjAttr on a non-object"
      end
    | F.SetObjAttr (p, oattr, newval, env') ->
      [{state with control = Frame (Exp newval, F.SetObjAttrNewval (p, oattr, v, env'));
                   env = env'}]
    | F.SetObjAttrNewval (p, oattr, obj, env') ->
      let helper attrs v' = match oattr, v' with
        | S.Proto, `Obj _ | S.Proto, `Null -> {attrs with O.proto = v'}
        | S.Proto, _ -> failwith "Cannot update proto without an object or null"
        | S.Extensible, `True | S.Extensible, `False | S.Extensible, `BoolT ->
          { attrs with O.extensible = v'}
        | S.Extensible, _ -> failwith "Cannot update extensible without a boolean"
        | S.Code, _ -> failwith "Cannot update code"
        | S.Primval, _ -> {attrs with O.primval = v'}
        | S.Klass, _ -> failwith "Cannot update klass" in
      begin match obj with
        | `Obj a ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | `Obj (attrs, props) ->
              let ostore', v' = alloc_if_necessary p conf
                  ("setobjattrnewval-" ^ (S.string_of_oattr oattr)) v in
              let newobj = (helper attrs v', props) in
              let ostore'' = ostore_set a (`Obj newobj) ostore' global.gostore in
              [{state with control = Val (v' :> v);
                           ostore = ostore''; env = env'}]
            | `ObjT -> failwith "SetObjAttrNewval: object too abstract"
          end
        | `StackObj _ ->
          (* TODO: this object lives on the stack and will not be returned by
             this operation, it is therefore not reachable. Is this expected? *)
          [{state with control = Val v; env = env'}]
        | `ObjT -> failwith "SetObjAttrNewval: object too abstracted"
        | _ -> failwith "SetObjAttrNewval on a non-object"
      end
    | F.OwnFieldNames (p, env') -> begin match v with
        | `Obj a ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | `Obj (_, props) ->
              let add_name n x m =
                IdMap.add (string_of_int x)
                  (O.Data ({O.value = `Str n; O.writable = `False}, `False, `False))
                  m in
              let namelist = IdMap.fold (fun k v l -> (k :: l)) props [] in
              let props = BatList.fold_right2 add_name namelist
                  (iota (List.length namelist)) IdMap.empty in
              let d = (float_of_int (List.length namelist)) in
              let final_props =
                IdMap.add "length"
                  (O.Data ({O.value = `Num d; O.writable = `False}, `False, `False))
                  props in
              let obj' = (O.d_attrsv , final_props) in
              let addr = alloc_obj p "obj" obj' conf in
              let ostore' = ObjectStore.join addr (`Obj obj') state.ostore in
              [{state with control = Val (`Obj addr); ostore = ostore'}]
            | `ObjT -> failwith "OwnFieldNames: object too abstracted"
          end
        | `ObjT -> failwith "OwnFieldNames: object too abstracted"
        | _ -> failwith "OwnFieldNames on a non-object"
      end
    | F.DeleteFieldObj (field, env') ->
      [{state with control = Frame (Exp field, F.DeleteFieldField (v, env'))}]
    | F.DeleteFieldField (obj, env') ->
      begin match obj, v with
        | `Obj a, `Str s ->
          if ObjectStore.contains a state.ostore then
            begin match ObjectStore.lookup a state.ostore with
              | `Obj obj ->
                if O.has_prop obj (`Str s) then
                  let t =
                    let newobj = O.remove_prop obj (`Str s) in
                    let ostore' = ObjectStore.set a (`Obj newobj) state.ostore in
                    {state with control = Val `True; env = env'; ostore = ostore'} in
                  let f =
                    {state with control = Exception (`Throw (`Str "unconfigurable-delete"));
                                env = env'} in
                  match O.lookup_prop obj (`Str s) with
                  | O.Data (_, _, b) | O.Accessor (_, _, b) ->
                    begin match Delta.prim_to_bool b with
                      | `True -> [t]
                      | `False -> [f]
                      | `BoolT -> [t; f]
                    end
                else
                  [{state with control = Val `False; env = env'}]
              | `ObjT -> failwith "DeleteFieldField: object too abstracted"
            end
          else if ObjectStore.contains a global.gostore then
            failwith "DeleteFieldField: cannot update object in the global store"
          else
            failwith ("DeleteFieldField: no object found at address " ^
                      (Address.to_string a))
        | `StackObj obj, `Str s ->
          (* This stack object will not be reachable when this is reached *)
          if O.has_prop obj (`Str s) then
            let t = {state with control = Val `True; env = env'} in
            let f = {state with control = Exception (`Throw (`Str "unconfigurable-delete"));
                                env = env'} in
            match O.lookup_prop obj (`Str s) with
            (* TODO: BoolT *)
            | O.Data (_, _, b) | O.Accessor (_, _, b) ->
              begin match Delta.prim_to_bool b with
              | `True -> [t]
              | `False -> [f]
              | `BoolT -> [t; f]
              end
          else
            [{state with control = Val `False; env = env'}]
        | v1, v2 -> failwith ("DeleteFieldField on a non-object or non-string: " ^ (F.string_of_value v1) ^ ", " ^ (F.string_of_value v2))
      end
    | F.Rec (p, name, a, body, env') ->
      let ostore', v' = alloc_if_necessary p conf ("rec-" ^ name) v in
      let vstore' = ValueStore.set a v' state.vstore in
      [{state with control = Exp body;
                   vstore = vstore'; ostore = ostore'; env = env'}]
    | F.SetBang (p, name, a, env') ->
      let ostore', v' = alloc_if_necessary p conf ("setbang-" ^ name) v in
      let vstore' = ValueStore.set a v' state.vstore in
      [{state with control = Val (v' :> v);
                   vstore = vstore'; ostore = ostore'; env = env'}]
    | F.Label (_, env') ->
      [{state with env = env'}]
    | F.Break (lab, env') ->
      [{state with control = Exception (`Break (lab, v)); env = env'}]
    | F.Throw env' ->
      [{state with control = Exception (`Throw v); env = env'}]
    | F.TryCatch (_, _, env') ->
      (* No exception has been caught, continue normal execution *)
      [{state with control = Val v; env = env'}]
    | F.TryCatchHandler (p, exc, env') ->
      (* Exception should be handled by the handler *)
      let (body, state') = apply_fun p v [exc] conf global in
      [{state' with control = Frame (Exp body, F.RestoreEnv (p, env'))}]
    | F.TryFinally (finally, env') ->
      (* No exception, execute the finally *)
      [{state with control = Exp finally; env = env'}]
    | F.TryFinallyExc (exc, env') ->
      (* Finally has been executed, rethrow the exception *)
      [{state with control = Exception exc; env = env'}]
    | F.RestoreEnv (_, env') ->
      [{state with control = Val v; env = env'}]
    | F.ObjectProps _ ->
      failwith "apply_frame should not handle ObjectProps frame!"

  let apply_frame_prop v frame ((state, ss) as conf : conf) (global : global)
    : state = match frame with
    (* ObjectProps of string * O.t * (string * prop) list * Env.t *)
    | F.ObjectProps (p, name, obj, [], env') ->
      let obj' = O.set_prop obj name v in
      let a = alloc_obj p name obj' conf in
      let ostore' = ObjectStore.join a (`Obj obj') state.ostore in
      {state with control = Val (`Obj a); env = env'; ostore = ostore'}
    | F.ObjectProps (p, name, obj, (name', prop) :: props, env') ->
      let obj' = O.set_prop obj name v in
      {state with control = Frame (Prop prop, F.ObjectProps (p, name', obj', props, env'));
                  env = env'}
    | f -> failwith ("apply_frame_prop should not handle a non-ObjectProps frame: " ^
                     (string_of_frame f))

  let apply_frame_exc e (frame : frame) ((state, ss) : conf) (global : global)
    : state = match e, frame with
    | `Break (label, v), F.Label (l, env') ->
      {state with control = Val v; env = env'}
    | `Break b, F.TryFinally (finally, env') ->
      {state with control = Frame (Exp finally, F.TryFinallyExc (`Break b, env'));
                  env = env'}
    | `Break _, _ -> state
    | `Throw v, F.TryCatch (p, handler, env') ->
      {state with control = Frame (Exp handler, F.TryCatchHandler (p, v, env'));
                  env = env'}
    | `Throw v, F.TryFinally (finally, env') ->
      {state with control = Frame (Exp finally, F.TryFinallyExc (`Throw v, env'));
                  env = env'}
    | `Throw _, _ -> state

  let rec is_atomic = function
    | S.Null _ | S.Undefined _ | S.String _ | S.Num _
    | S.True _ | S.False _ | S.Id _ | S.Lambda _ ->
      true
    (* TODO: there are probably other compound expressions that can be
       considered atomic *)
    | S.Hint (_, _, e) -> is_atomic e
    | _ -> false

  let eval_atomic state global = function
    | S.Null _ -> `Null
    | S.Undefined _ -> `Undef
    | S.String (_, s) -> `Str s
    | S.Num (_, n) -> `Num n
    | S.True _ -> `True
    | S.False _ -> `False
    | S.Id (_, id) ->
      (* TODO: It seems that identifiers from the global environment appears by
         magic in the state environment, and it shouldn't be the case. *)
      let a = if Env.contains id state.env then
          Env.lookup id state.env
        else if Env.contains id global.genv then
          Env.lookup id global.genv
        else begin
          print_endline ("Identifier cannot be resolved: " ^ id);
          raise Not_found
        end in
      let store = which_vstore a state.vstore global.gvstore in
      let v = ValueStore.lookup a store in
      (v :> v)
    | S.Lambda (_, args, body) ->
      let free = S.free_vars body in
      let env' = Env.keep free state.env in
      `Clos (env', args, body)
    | e -> failwith ("eval_atomic on a non-atomic expression: " ^
                     (string_of_exp e))

  let unch (control : control) ((state, ss) : conf) =
    [StackUnchanged, ({state with control}, ss)]
  let push (frame : F.t) ((state, ss) as conf : conf) global
    : (stack_change * conf) list =
    match state.control with
    | Exp e when is_atomic e ->
      let v = eval_atomic state global e in
      BatList.map (fun state -> (StackUnchanged, (state, ss)))
        (apply_frame v frame conf global)
    | _ ->
      [StackPush frame, (state, StackSummary.push ss global frame)]

  let step_prop prop ((state, ss) : conf) (global : global)
    : (stack_change * conf) list = match prop with
    | S.Data ({S.value = v; S.writable = w}, enum, config) ->
      push (F.PropData (S.pos_of v,
                        ({O.value = `Undef; O.writable = AValue.bool w},
                         AValue.bool enum, AValue.bool config),
                        state.env))
        ({state with control = Exp v}, ss) global
    | S.Accessor ({S.getter = g; S.setter = s}, enum, config) ->
      push (F.PropAccessor (S.pos_of g,
                            Some s, ({O.getter = `Undef; O.setter = `Undef},
                                     AValue.bool enum, AValue.bool config),
                            state.env))
        ({state with control = Exp g}, ss) global


  (* Inspired from LambdaS5's Ljs_cesk.eval_cesk function *)
  let step_exp (exp : S.exp) ((state, ss) as conf : conf) (global : global)
    : (stack_change * conf) list = match exp with
    | S.Null _ | S.Undefined _ | S.String _ | S.Num _ | S.True _ | S.False _
    | S.Id _ | S.Lambda _ ->
      let v = eval_atomic state global exp in
      unch (Val v) conf
    | S.Hint (_, _, e) ->
      unch (Exp e) conf
    | S.Object (p, attrs, props) ->
      let {S.primval = pexp;
           S.code = cexp;
           S.proto = proexp;
           S.klass = kls;
           S.extensible = ext} = attrs in
      let opt_add name ox xs = match ox with
        | Some x -> (name, x)::xs
        | None -> xs in
      let attrs = [] |>
                  opt_add "proto" proexp |>
                  opt_add "code" cexp |>
                  opt_add "prim" pexp in
      let obj = ({O.code=`Undef; O.proto=`Undef; O.primval=`Undef;
                  O.klass=(`Str kls);
                  O.extensible = AValue.bool ext},
                 IdMap.empty) in
      (* We *need* to tick here, to avoid losing precision when multiple objects
         are defined without funcalls in between (see tests/objs-imprecision.s5)
      *)
      (* k-CFA *)
      let state = {state with time = Time.tick p state.time} in
      (* Parameter-sensitive k-CFA *)
      (* let state = {state with time = Time.tick (p, []) state.time} in *)
      begin match attrs, props with
        | [], [] ->
          unch (Val (`StackObj obj)) (state, ss)
        | [], (prop, exp)::props ->
          push (F.ObjectProps (p, prop, obj, props, state.env))
            ({state with control = Prop exp}, ss) global
        | (attr, exp)::attrs, props ->
          push (F.ObjectAttrs (p, attr, obj, attrs, props, state.env))
            ({state with control = Exp exp}, ss) global
      end
    | S.Let (p, id, exp, body) ->
      (* print_endline ("Let " ^ id ^ " at " ^ (Pos.string_of_pos p)); *)
      push (F.Let (p, id, body, state.env))
        ({state with control = Exp exp}, ss) global
    | S.Seq (p, left, right) ->
      push (F.Seq (right, state.env))
        ({state with control = Exp left}, ss) global
    | S.App (p, f, args) ->
      print_endline ("Apply " ^ (Pos.string_of_pos p));
      push (F.AppFun (p, args, state.env))
        ({state with control = Exp f}, ss) global
    | S.Op1 (p, op, arg) ->
      push (F.Op1App (p, op, state.env))
        ({state with control = Exp arg}, ss) global
    | S.Op2 (p, op, arg1, arg2) ->
      push (F.Op2Arg (p, op, arg2, state.env))
        ({state with control = Exp arg1}, ss) global
    | S.If (p, pred, cons, alt) ->
      push (F.If (cons, alt, state.env))
        ({state with control = Exp pred}, ss) global
    | S.GetField (p, obj, field, body) ->
      push (F.GetFieldObj (p, field, body, state.env))
        ({state with control = Exp obj}, ss) global
    | S.SetField (p, obj, field, newval, body) ->
      push (F.SetFieldObj (p, field, newval, body, state.env))
        ({state with control = Exp obj}, ss) global
    | S.GetAttr (p, pattr, obj, field) ->
      push (F.GetAttrObj (pattr, field, state.env))
        ({state with control = Exp obj}, ss) global
    | S.SetAttr (p, pattr, obj, field, newval) ->
      push (F.SetAttrObj (p, pattr, field, newval, state.env))
        ({state with control = Exp obj}, ss)
        global
    | S.GetObjAttr (p, oattr, obj) ->
      push (F.GetObjAttr (oattr, state.env))
        ({state with control = Exp obj}, ss) global
    | S.SetObjAttr (p, oattr, obj, newval) ->
      push (F.SetObjAttr (p, oattr, newval, state.env))
        ({state with control = Exp obj}, ss) global
    | S.OwnFieldNames (p, obj) ->
      push (F.OwnFieldNames (p, state.env))
        ({state with control = Exp obj}, ss) global
    | S.Rec (p, name, exp, body) ->
      let a = alloc_var p name `Undef conf in
      let env' = Env.extend name a state.env in
      let vstore' = ValueStore.join a `Undef state.vstore in
      push (F.Rec (p, name, a, body, env'))
        ({state with control = Exp exp;
                     env = env';
                     vstore = vstore'}, ss) global
    | S.SetBang (p, id, exp) ->
      let env = which_env id state.env global.genv in
      let a = Env.lookup id env in
      push (F.SetBang (p, id, a, state.env))
        ({state with control = Exp exp}, ss) global
    | S.Label (p, label, body) ->
      push (F.Label (label, state.env))
        ({state with control = Exp body}, ss) global
    | S.Break (p, label, ret) ->
      push (F.Break (label, state.env))
        ({state with control = Exp ret}, ss) global
    | S.Throw (p, exp) ->
      push (F.Throw state.env)
        ({state with control = Exp exp}, ss) global
    | S.TryCatch (p, body, catch) ->
      push (F.TryCatch (p, catch, state.env))
        ({state with control = Exp body}, ss) global
    | S.TryFinally (p, body, finally) ->
      push (F.TryFinally (finally, state.env))
        ({state with control = Exp body}, ss) global
    | S.DeleteField (p, obj, field) ->
      push (F.DeleteFieldObj (field, state.env))
        ({state with control = Exp obj}, ss) global
    | S.Eval _ -> failwith ("Eval not yet handled")

  let step_no_gc ((state, ss) as conf : conf) (global : global)
      (frame : (conf * F.t) option) : (stack_change * conf) list =
    match state.control with
    | Exp e -> step_exp e conf global
    | Prop prop -> step_prop prop conf global
    | Val v -> begin match frame with
        | Some ((_, ss'), frame) ->
          BatList.map (fun state -> (StackPop frame, (state, ss')))
            (apply_frame v frame conf global)
        | None -> []
      end
    | Frame (control', frame) ->
      [StackPush frame, ({state with control = control'},
                         StackSummary.push ss global frame)]
    | PropVal prop -> begin match frame with
        | Some ((state', ss'), frame) ->
          [StackPop frame, (apply_frame_prop prop frame conf global, ss')]
        | None -> []
      end
    | Exception e -> begin match frame with
        | Some ((state', ss'), frame) ->
          [StackPop frame, (apply_frame_exc e frame conf global, ss')]
        | None -> []
      end

  let step conf global =
    step_no_gc (if !gc then GC.gc conf global else conf) global

  let merge ((state, ss) : conf) ((state', _) : conf) : conf =
    ({state with env = Env.merge state.env state'.env;
                 vstore = ValueStore.merge state.vstore state'.vstore;
                 ostore = ObjectStore.merge state.ostore state'.ostore},
     ss)
end
