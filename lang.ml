open Prelude
open Shared
open Env
open Store
open Lattice

let error msg exc =
  print_endline msg;
  raise exc

module D = Delta
module S = Ljs_syntax
module O = Obj_val
module V = Obj_val.Value
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

  val is_value_conf : conf -> bool

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

  type control =
    | Exp of S.exp
    | Prop of string * S.prop
    | PropVal of O.prop
    | Val of V.t
    | Frame of (control * F.t)
    | Exception of F.exc

  let string_of_control = function
    | Exp exp -> "Exp(" ^ (string_of_exp exp) ^ ")"
    | Prop (name, prop) -> "Prop(" ^ name ^ ", " ^ (string_of_prop prop) ^ ")"
    | Val v -> "Val(" ^ (V.to_string v) ^ ")"
    | PropVal v -> "PropVal(" ^ (O.string_of_prop v) ^ ")"
    | Frame (exp, f) -> "Frame(" ^ (F.to_string f) ^ ")"
    | Exception (`Break (l, _)) -> "Break(" ^ l ^ ")"
    | Exception (`Throw v) -> "Throw(" ^ (V.to_string v) ^ ")"

  type state = {
    control : control;
    env : Env.t;
    vstore : ValueStore.t;
    ostore : ObjectStore.t;
    time : Time.t; (* only used for increasing context-sensitivity in some places *)
  }

  let string_of_state (state : state) =
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
    include AddressSet
    let push (ss : t) (global : global) (f : F.t) =
      AddressSet.union ss (Frame.touch f global.genv)
  end
  module StackSummary = GCStackSummary

  type conf = state * StackSummary.t

  let string_of_conf (state, ss) = string_of_state state

  let compare_conf (state, ss) (state', ss') =
    order_comp (compare_state state state') (StackSummary.compare ss ss')

  let which_env id env env' : Env.t =
    if Env.contains id env then
      env
    else if Env.contains id env' then
      env'
    else
      error ("Identifier cannot be resolved: " ^ id) Not_found

  (* TODO: as object addresses are now a set of addresses, this might be more
     tricky than it seems: what if some addresses are in the local store and
     some in the global store? Ideally, they should either all be in the global
     store, or they should all having been copied in the local store *)
  let which_ostore (a : ObjAddressSet.t) (ostore : ObjectStore.t) (ostore' : ObjectStore.t)
    : ObjectStore.t =
    if ObjectStore.contains a ostore then
      ostore
    else if ObjectStore.contains a ostore' then
      ostore'
    else
      error ("Object lives at an unreachable address: " ^
             (ObjAddressSet.to_string a)) Not_found

  let ostore_set a obj ostore ostore' : ObjectStore.t =
    if ObjectStore.contains a ostore then
      (* Object already in the state store, update it *)
      ObjectStore.set a obj ostore
    else if ObjectStore.contains a ostore' then
      (* Object is only in the global store, add the modified object to the
         state store, using a join as it is a new object in this store *)
      ObjectStore.join a obj ostore
    else
      error ("Cannot set object at unreachable location: " ^
             (ObjAddressSet.to_string a)) Not_found

  let which_vstore (a : VarAddress.t) (vstore : ValueStore.t) (vstore' : ValueStore.t)
    : ValueStore.t =
    if ValueStore.contains a vstore then
      vstore
    else if ValueStore.contains a vstore' then
      vstore'
    else
      error ("Value lives at an unreachable address: " ^
             (VarAddress.to_string a)) Not_found

  (** Isolate garbage collection specific functions *)
  module GC =
  struct

    let touch vstore ostore global (v : V.t) =
      let rec aux acc visited_objs : V.t -> AddressSet.t = function
        | `A v -> begin match v with
            | `Null | `True | `False | `BoolT | `Num _ | `NumT
            | `Str _ | `StrT | `Undef | `Bot -> acc
            | `Clos (env, args, exp) ->
              AddressSet.union_vars (Env.range env) acc
            | `Obj a -> if ObjAddressSet.subset a visited_objs then
                acc
              else if ObjectStore.contains a ostore then
                let obj = ObjectStore.lookup a ostore in
                aux_obj (AddressSet.union_objs a acc)
                  (ObjAddressSet.union a visited_objs) obj
              else if ObjectStore.contains a global.gostore then
                (* ignore addresses in the global store, as they are not
                   reclaimable and can't point to reclaimable addresses *)
                acc
              else
                error ("GC reached a non-reachable object address: " ^
                       (ObjAddressSet.to_string a)) Not_found
            | `ClosT | `Top -> failwith ("touch: a value was too abstract: " ^
                                         (AValue.to_string v))
          end
        | `StackObj obj -> aux_obj acc visited_objs obj
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
      aux AddressSet.empty ObjAddressSet.empty v

    let rec control_root control env vstore ostore global
      : AddressSet.t = match control with
      | Exp e ->
        AddressSet.vars (Frame.addresses_of_vars (S.free_vars e)
                           env global.genv)
      | Prop (_, S.Data ({S.value = v; _}, _, _)) ->
        AddressSet.vars (Frame.addresses_of_vars (S.free_vars v) env global.genv)
      | Prop (_, S.Accessor ({S.getter = g; S.setter = s}, _, _)) ->
        AddressSet.vars (Frame.addresses_of_vars (IdSet.union (S.free_vars g)
                                                    (S.free_vars s))
                           env global.genv)
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

    let root ((state, ss) : conf) global : AddressSet.t =
      AddressSet.union ss (control_root state.control state.env
                             state.vstore state.ostore global)

    let touching_rel1_var (vstore : ValueStore.t) (ostore : ObjectStore.t)
        (global : global) (addr : VarAddress.t) : AddressSet.t =
      let store = which_vstore addr vstore global.gvstore in
      let v = ValueStore.lookup addr store in
      touch vstore ostore global (`A v)

    let touching_rel1_obj (vstore : ValueStore.t) (ostore : ObjectStore.t)
        (global : global) (addr : ObjAddress.t) : AddressSet.t =
      touch vstore ostore global (`A (`Obj (ObjAddressSet.singleton addr)))

    let touching_rel vstore ostore global addr =
      let rec aux todo acc =
        if AddressSet.is_empty todo then
          acc
        else match AddressSet.choose todo with
          | `Var a -> if AddressSet.mem_var a acc then
              aux (AddressSet.remove_var a todo) acc
            else
              let addrs = touching_rel1_var vstore ostore global a in
              aux (AddressSet.remove_var a (AddressSet.union addrs todo))
                (AddressSet.add_var a acc)
          | `Obj a -> if AddressSet.mem_obj a acc then
              aux (AddressSet.remove_obj a todo) acc
            else
              let addrs = touching_rel1_obj vstore ostore global a in
              aux (AddressSet.remove_obj a (AddressSet.union addrs todo))
                (AddressSet.add_obj a acc)
      in
      aux (match addr with
          | `Var a -> AddressSet.singleton_var a
          | `Obj a -> AddressSet.singleton_obj a) AddressSet.empty

    let reachable ((state, ss) : conf) (global : global) : AddressSet.t =
      let r = root (state, ss) global in
      AddressSet.fold (fun a acc ->
          AddressSet.union acc (touching_rel state.vstore state.ostore global a))
        r AddressSet.empty

    let gc ((state, ss) : conf) (global : global) : conf =
      if !gc != `NoGC then
        let r = reachable (state, ss) global in
        ({state with
          vstore = ValueStore.restrict (AddressSet.to_vars r) state.vstore;
          ostore = ObjectStore.restrict (AddressSet.to_objs r) state.ostore},
         ss)
      else
        (state, ss)
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

  let alloc_var (p : Pos.t) (id : string) _ ((state, ss) : conf) =
    match state.env.Env.strategy with
    | `MCFA -> VarAddress.alloc p id (`MCFATime state.env.Env.call)
    | `PSKCFA -> VarAddress.alloc p id state.time

  let alloc_obj (p : Pos.t) (id : string) _ ((state, ss) : conf) =
    match state.env.Env.strategy with
    | `MCFA ->
      ObjAddressSet.singleton
        (ObjAddress.alloc p id (`MCFATime state.env.Env.call))
    | `PSKCFA ->
      ObjAddressSet.singleton
        (ObjAddress.alloc p id state.time)

  let alloc_if_necessary (p : Pos.t) ((state, _) as conf : conf) id = function
      | `A v -> (state.ostore, v)
      | `StackObj obj ->
        let a = alloc_obj p id obj conf in
        let ostore' = ObjectStore.join a obj state.ostore in
        (ostore', `Obj a)

  let inject (exp : S.exp) (c : conf option) : (conf * global) =
    let empty = {control = Exp exp; env = Env.empty; vstore = ValueStore.empty;
                 ostore = ObjectStore.empty; time = Time.initial} in
    let empty_global = {genv = Env.empty; gvstore = ValueStore.empty;
                        gostore = ObjectStore.empty} in
    (empty, StackSummary.empty),
    BatOption.map_default
      (fun (init, ss) ->
         (* Perform GC to get rid of all non-needed values in the global
            env/store *)
         let (init', _) = GC.gc ({init with control = Exp exp}, ss) empty_global in
         {genv = init'.env; gvstore = init'.vstore; gostore = init'.ostore})
      empty_global c

  let rec get_prop obj prop ostore global = match obj with
    | `A `Obj a ->
      let store = which_ostore a ostore global.gostore in
      begin match ObjectStore.lookup a store with
        | ({O.proto = pvalue; _}, props) ->
          begin try Some (IdMap.find prop props)
            with Not_found -> get_prop pvalue prop ostore global
          end
      end
    | `StackObj ({O.proto = pvalue; _}, props) ->
      begin try Some (IdMap.find prop props)
        with Not_found -> get_prop pvalue prop ostore global
      end
    | `A `Null -> None
    | `A v -> failwith ("get_prop on non-object: " ^ (AValue.to_string v))

  (** Do the selection of parameters that will be used in timestamps (for
      parameter sensitive addresses) *)
  let select_params (args : (string * V.t) list) : (string * Time.v) list =
    let f ((n, v) : string * V.t) : ((string * Time.v) option) = match v with
      | `A v' ->
        begin match v' with
          | #PSTime.v as v'' -> Some (n, v'')
          | _ -> None
        end
      | _ -> None in
    BatList.filter_map f args

  let rec apply_fun (p : Pos.t) (name : string option) (f : V.t) (args : V.t list)
      ((state, ss) : conf) (global : global) : (S.exp * state) =
    match f with
    | `A `Clos (env', args', body) ->
      if (List.length args) != (List.length args') then
        (* This is *not* about Javascript closures, as an arity mismatch when
           applying a function in Javascript does not lead to an error. However,
           such a mismatch should not happen in S5 code, and that is why this
           is an internal error *)
        failwith "Arity mismatch"
      else
        let alloc_arg v name ((state, ss) as conf) =
          let (ostore', v') = alloc_if_necessary p conf ("arg-" ^ name) v in
          let conf' = ({state with ostore = ostore'}, ss) in
          let a = alloc_var p name v' conf' in
          ({state with ostore = ostore';
                       vstore = ValueStore.join a v' state.vstore;
                       env = Env.extend name a state.env}, ss) in
        let (state', ss) as conf' =
          BatList.fold_right2 alloc_arg args args'
            ({state with env = {env' with Env.call = state.env.Env.call;
                                          Env.strategy = state.env.Env.strategy}}, ss) in
        let alloc =
          if state.env.Env.strategy = `PSKCFA ||
             (BatOption.map_default (fun id -> Env.contains id global.genv)
                false name && not !only_mcfa) then
            (* Improve precision by switching to PS k-CFA *)
            `PSKCFA
          else
            `MCFA in
        Stats.called (BatOption.map_default (fun x -> x) "<anonymous>" name)
          (BatList.map V.to_string args);
        (body, {state' with
                env = Env.set_alloc alloc (Env.call p state'.env);
                time = match alloc with
                  (* | `KCFA -> Time.tick (S.pos_of body) state.time *)
                  | `PSKCFA -> Time.tick ((S.pos_of body),
                                          select_params (BatList.combine args' args))
                                 state.time
                  | `MCFA -> state.time})
    | `A `ClosT -> failwith ("Closure too abstracted when called at " ^
                             (Pos.to_string p))
    | `A `Obj a ->
      let store = which_ostore a state.ostore global.gostore in
      begin match ObjectStore.lookup a store with
        | ({O.code = `A (`Clos f); _}, _) ->
          apply_fun p name (`A (`Clos f)) args (state, ss) global
        (* TODO: should this be an S5 error or a JS error? *)
        | _ -> failwith ("Applied object without code attribute at " ^
                         (Pos.to_string p))
      end
    | `StackObj ({O.code = `A (`Clos f); _}, _) ->
      apply_fun p name (`A (`Clos f)) args (state, ss) global
    | `StackObj _ -> failwith ("Applied object without code attribute: " ^
                               (V.to_string f) ^ " at " ^ (Pos.to_string p))
    (* TODO: S5 or JS error? *)
    | _ -> failwith ("Applied non-function: " ^ (V.to_string f) ^ " at " ^
                     (Pos.to_string p))

  let apply_frame (v : V.t) (frame : frame) ((state, ss) as conf : conf)
      (global : global) : state list = match frame with
    | F.Let (p, id, body, env') ->
      let a = alloc_var p id id conf in
      let env'' = Env.extend id a env' in
      let ostore', v' = alloc_if_necessary p conf ("let-" ^ id) v in
      let vstore' = ValueStore.join a v' state.vstore in
      [{state with control = Exp body; env = env''; vstore = vstore';
                   ostore = ostore'}]
    | F.ObjectAttrs (p, name, obj, [], [], env') ->
      let obj' = O.set_attr_str obj name v in
      [{state with control = Val (`StackObj obj'); env = env'}]
    | F.ObjectAttrs (p, name, obj, [], (name', prop) :: props, env') ->
      let obj' = O.set_attr_str obj name v in
      [{state with control = Frame (Prop (name, prop),
                                    F.ObjectProps (p, name', obj', props, env'));
                   env = env'}]
    | F.ObjectAttrs (p, name, obj, (name', attr) :: attrs, props, env') ->
      let obj' = O.set_attr_str obj name v in
      [{state with control = Frame (Exp attr,
                                    F.ObjectAttrs (p, name', obj', attrs,
                                                   props, env'));
                   env = env'}]
    | F.PropData (p, name, (data, enum, config), env') ->
      [{state with control = PropVal (O.Data ({data with O.value = v},
                                              enum, config));
                   env = env'}]
    | F.PropAccessor (p, name, None, (accessor, enum, config), env') ->
      [{state with control = PropVal (O.Accessor ({accessor with O.setter = v},
                                                  enum, config));
                   env = env'}]
    | F.PropAccessor (p, name, Some exp, (accessor, enum, config), env') ->
      [{state with control = Frame (Exp exp, (F.PropAccessor
                                                (S.pos_of exp, name, None,
                                                 ({accessor with O.getter = v},
                                                  enum, config), env')));
                   env = env'}]
    | F.Seq (exp, env') ->
      [{state with control = Exp exp; env = env'}]
    | F.AppFun (p, exp, [], env') ->
      let (exp, state') = apply_fun p (match exp with
          | S.Id (_, name) -> Some name
          | _ -> None)
          v [] conf global in
      [{state' with control = Exp exp}]
    | F.AppFun (p, exp, arg :: args, env') ->
      [{state with control = Frame (Exp arg, (F.AppArgs (p, exp, v, [], args, env')));
                   env = env'}]
    | F.AppArgs (p, exp, f, vals, [], env') ->
      let args = BatList.rev (v :: vals) in
      let (exp, state') = apply_fun p (match exp with
          | S.Id (_, name) -> Some name
          | _ -> None) f args conf global in
      [{state' with control = Exp exp}]
    | F.AppArgs (p, exp, f, vals, arg :: args, env') ->
      [{state with control = Frame (Exp arg,
                                    (F.AppArgs (p, exp, f, v :: vals, args, env')));
                   env = env'}]
    | F.Op1App (p, op, env') ->
      (* TODO: we should avoid allocating for op1 and op2 *)
      let ostore', v' = alloc_if_necessary p conf ("op1-" ^ op) v in
      [{state with control = Val (`A (D.op1 ostore' global.gostore op v'));
                   ostore = ostore'; env = env'}]
    | F.Op2Arg (p, op, arg2, env') ->
      [{state with control = Frame (Exp arg2, (F.Op2App (p, op, v, env')));
                   env = env'}]
    | F.Op2App (p, op, arg1, env') ->
      (* TODO: we should avoid allocating for op1 and op2 *)
      let ostore', arg1' = alloc_if_necessary p conf ("op2-" ^ op ^ "arg1") arg1 in
      let conf' = ({state with ostore = ostore'}, ss) in
      let ostore'', arg2' = alloc_if_necessary p conf' ("op2-" ^ op ^ "arg2") v in
      [{state with control = Val (`A (D.op2 ostore'' global.gostore op arg1' arg2'));
                   ostore = ostore''; env = env'}]
    | F.If (cons, alt, env') ->
      begin match Delta.prim_to_bool_v v with
        | `True -> [{state with control = Exp cons; env = env'}]
        | `BoolT -> [{state with control = Exp cons; env = env'};
                     {state with control = Exp alt; env = env'}]
        | `False -> [{state with control = Exp alt; env = env'}]
      end
    | F.GetFieldObj (p, field, body, env') ->
      [{state with control = Frame (Exp field, F.GetFieldField (p, v, body, env'));
                   env = env'}]
    | F.GetFieldField (p, obj, body, env') ->
      [{state with control = Frame (Exp body, F.GetFieldBody (p, obj, v, env'));
                   env = env'}]
    | F.GetFieldBody (p, obj, field, env') ->
      begin match obj, field with
        | `A (`Obj _), `A (`Str s)
        | `StackObj _, `A (`Str s) ->
          begin match get_prop obj s state.ostore global with
            | Some (O.Data ({O.value = v; _}, _, _)) ->
              [{state with control = Val v; env = env'}]
            | Some (O.Accessor ({O.getter = g; _}, _, _)) ->
              let (body, state') = apply_fun p None g [obj; v] conf global in
              [{state' with control = Frame (Exp body, F.RestoreEnv (p, env'))}]
            | None -> [{state with control = Val (`A `Undef); env = env'}]
          end
        | `A (`Obj _), `A `StrT ->
          (* We can handle this case more precisely by returning a state for
             each possible value of a field in this object *)
          [{state with control = Val (`A `Top); env = env'}]
        | o, s -> failwith ("GetFieldBody on a non-object or non-string field: " ^
                            (V.to_string o) ^ ", " ^ (V.to_string s))
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
    | F.SetFieldArgs (p, obj, field, newval, env') ->
      let body = v in
      begin match obj, field with
        | `A (`Obj a), `A (`Str s) ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | ({O.extensible = extensible; _} as attrs, props) ->
              begin match get_prop obj s state.ostore global with
                | Some (O.Data ({O.writable = `A `True; _}, enum, config)) ->
                  let (enum, config) = if O.has_prop (attrs, props) s then
                      (enum, config)
                    else
                      (`A `True, `A `True) in
                  let newobj = O.set_prop (attrs, props) s
                      (O.Data ({O.value = newval; O.writable = `A `True},
                               enum, config)) in
                  let ostore' = ostore_set a newobj state.ostore global.gostore in
                  [{state with control = Val newval; env = env'; ostore = ostore'}]
                | Some (O.Data _)
                | Some (O.Accessor ({O.setter = `A `Undef; _}, _, _)) ->
                  [{state with control = Exception (`Throw (`A (`Str "uwritable-field")))}]
                | Some (O.Accessor ({O.setter = setter; _}, _, _)) ->
                  let (exp, state') = apply_fun p None setter [obj; body] conf global in
                  [{state' with control = Frame (Exp exp, F.RestoreEnv (p, env'))}]
                | None ->
                  let t =
                    let newobj = O.set_prop (attrs, props) s
                        (O.Data ({O.value = newval; O.writable = `A `True},
                                 `A `True, `A `True)) in
                    let ostore' = ostore_set a newobj
                        state.ostore global.gostore in
                    {state with control = Val newval; env = env'; ostore = ostore'} in
                  let f = {state with control = Val (`A `Undef)} in
                  match Delta.prim_to_bool_v extensible with
                  | `True -> [t]
                  | `False -> [f]
                  | `BoolT -> [t; f]
              end
          end
        | `StackObj _, _ -> failwith "TODO: SetFieldArgs on a stack object"
        | v1, v2 -> failwith ("SetFieldArgs on a non-object or non-string: " ^
                              (V.to_string v1) ^ ", " ^ (V.to_string v2))
      end
    | F.GetAttrObj (pattr, field, env') ->
      [{state with control = Frame (Exp field, F.GetAttrField (pattr, v, env'));
                   env = env'}]
    | F.GetAttrField (pattr, obj, env') ->
      begin match obj, v with
        | `A (`Obj a), `A (`Str s) ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | o -> let attr = O.get_attr o pattr s in
              [{state with control = Val attr; env = env'}]
          end
        | `StackObj obj, `A (`Str s) ->
          let attr = O.get_attr obj pattr s in
          [{state with control = Val attr; env = env'}]
        | `A (`Obj _), `A `StrT | `StackObj _, `A `StrT ->
          failwith "GetAttrField with a top string as field"
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
    | F.SetAttrNewval (p, pattr, obj, field, env') ->
      let newval = v in
      begin match obj, field with
        | `A (`Obj a), `A (`Str s) ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | o ->
              let newobj = O.set_attr o pattr s newval in
              let ostore' = ostore_set a newobj state.ostore global.gostore in
              [{state with control = Val (`A `True); env = env'; ostore = ostore'}]
          end
        | `StackObj o, `A (`Str s) -> failwith "TODO: SetAttrNewval on a stack object"
        | _ -> failwith "SetAttrNewval on a non-object or non-string attribute"
      end
    | F.GetObjAttr (oattr, env') -> begin match v with
        | `A (`Obj a) ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | obj -> [{state with control = Val (O.get_obj_attr obj oattr); env = env'}]
          end
        | `StackObj obj -> [{state with control = Val (O.get_obj_attr obj oattr); env = env'}]
        | _ -> failwith "GetObjAttr on a non-object"
      end
    | F.SetObjAttr (p, oattr, newval, env') ->
      [{state with control = Frame (Exp newval, F.SetObjAttrNewval (p, oattr, v, env'));
                   env = env'}]
    | F.SetObjAttrNewval (p, oattr, obj, env') ->
      let helper attrs v' = match oattr, v' with
        | S.Proto, `A (`Obj _) | S.Proto, `A `Null -> {attrs with O.proto = v'}
        | S.Proto, _ -> failwith "Cannot update proto without an object or null"
        | S.Extensible, `A `True | S.Extensible, `A `False | S.Extensible, `A `BoolT ->
          {attrs with O.extensible = v'}
        | S.Extensible, _ -> failwith "Cannot update extensible without a boolean"
        | S.Code, _ -> failwith "Cannot update code"
        | S.Primval, _ -> {attrs with O.primval = v'}
        | S.Klass, _ -> failwith "Cannot update klass" in
      begin match obj with
        | `A (`Obj a) ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | (attrs, props) ->
              let newobj = (helper attrs v, props) in
              let ostore' = ostore_set a newobj state.ostore global.gostore in
              [{state with control = Val v;
                           ostore = ostore'; env = env'}]
          end
        | `StackObj _ ->
          (* TODO: this object lives on the stack and will not be returned by
             this operation, it is therefore not reachable. Is this expected? *)
          [{state with control = Val v; env = env'}]
        | _ -> failwith "SetObjAttrNewval on a non-object"
      end
    | F.OwnFieldNames (p, env') ->
      let helper props =
        let add_name n x m =
          IdMap.add (string_of_int x)
            (O.Data ({O.value = `A (`Str n); O.writable = `A `False},
                     `A `False, `A `False))
            m in
        let namelist = IdMap.fold (fun k v l -> (k :: l)) props [] in
        let props = BatList.fold_right2 add_name namelist
            (iota (List.length namelist)) IdMap.empty in
        let d = (float_of_int (List.length namelist)) in
        let final_props =
          IdMap.add "length"
            (O.Data ({O.value = `A (`Num d); O.writable = `A `False},
                     `A `False, `A `False))
            props in
        let obj' = (O.d_attrsv , final_props) in
        [{state with control = Val (`StackObj obj')}] in
      begin match v with
        | `A (`Obj a) ->
          let store = which_ostore a state.ostore global.gostore in
          begin match ObjectStore.lookup a store with
            | (_, props) -> helper props
          end
        | `StackObj (_, props) -> helper props
        | _ -> failwith "OwnFieldNames on a non-object"
      end
    | F.DeleteFieldObj (field, env') ->
      [{state with control = Frame (Exp field, F.DeleteFieldField (v, env'))}]
    | F.DeleteFieldField (obj, env') ->
      begin match obj, v with
        | `A (`Obj a), `A (`Str s) ->
          if ObjectStore.contains a state.ostore then
            begin match ObjectStore.lookup a state.ostore with
              | obj ->
                if O.has_prop obj s then
                  let t =
                    let newobj = O.remove_prop obj s in
                    let ostore' = ObjectStore.set a newobj state.ostore in
                    {state with control = Val (`A `True); env = env'; ostore = ostore'} in
                  let f =
                    {state with control = Exception (`Throw (`A (`Str "unconfigurable-delete")));
                                env = env'} in
                  match O.lookup_prop obj s with
                  | O.Data (_, _, b) | O.Accessor (_, _, b) ->
                    begin match Delta.prim_to_bool_v b with
                      | `True -> [t]
                      | `False -> [f]
                      | `BoolT -> [t; f]
                    end
                else
                  [{state with control = Val (`A `False); env = env'}]
            end
          else if ObjectStore.contains a global.gostore then
            failwith "DeleteFieldField: cannot update object in the global store"
          else
            failwith ("DeleteFieldField: no object found at address " ^
                      (ObjAddressSet.to_string a))
        | `StackObj obj, `A (`Str s) ->
          (* This stack object will not be reachable when this is reached *)
          if O.has_prop obj s then
            let t = {state with control = Val (`A `True); env = env'} in
            let f = {state with control = Exception (`Throw (`A (`Str "unconfigurable-delete")));
                                env = env'} in
            match O.lookup_prop obj s with
            (* TODO: BoolT *)
            | O.Data (_, _, b) | O.Accessor (_, _, b) ->
              begin match Delta.prim_to_bool_v b with
                | `True -> [t]
                | `False -> [f]
                | `BoolT -> [t; f]
              end
          else
            [{state with control = Val (`A `False); env = env'}]
        | v1, v2 -> failwith ("DeleteFieldField on a non-object or non-string: " ^
                              (V.to_string v1) ^ ", " ^ (V.to_string v2))
      end
    | F.Rec (p, name, a, body, env') ->
      let ostore', v' = alloc_if_necessary p conf ("rec-" ^ name) v in
      let vstore' = ValueStore.set a v' state.vstore in
      [{state with control = Exp body;
                   vstore = vstore'; ostore = ostore'; env = env'}]
    | F.SetBang (p, name, a, env') ->
      let ostore', v' = alloc_if_necessary p conf ("setbang-" ^ name) v in
      let vstore' = ValueStore.set a v' state.vstore in
      [{state with control = Val (`A v');
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
      let (body, state') = apply_fun p None v [exc] conf global in
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
    | F.ObjectProps (p, name, obj, [], env') ->
      let obj' = O.set_prop obj name v in
      (* TODO: do we really need allocation? *)
      let a = alloc_obj p name obj' conf in
      let ostore' = ObjectStore.join a obj' state.ostore in
      {state with control = Val (`A (`Obj a)); env = env'; ostore = ostore'}
    | F.ObjectProps (p, name, obj, (name', prop) :: props, env') ->
      let obj' = O.set_prop obj name v in
      {state with control = Frame (Prop (name, prop), F.ObjectProps (p, name', obj', props, env'));
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
        else
          error ("Identifier cannot be resolved: " ^ id) Not_found in
      let store = which_vstore a state.vstore global.gvstore in
      let v = ValueStore.lookup a store in
      v
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
        (apply_frame (`A v) frame conf global)
    | _ ->
      [StackPush frame, (state, StackSummary.push ss global frame)]

  let step_prop (name, prop) ((state, ss) : conf) (global : global)
    : (stack_change * conf) list = match prop with
    | S.Data ({S.value = v; S.writable = w}, enum, config) ->
      push (F.PropData (S.pos_of v, name,
                        ({O.value = `A `Undef; O.writable = `A (AValue.bool w)},
                         `A (AValue.bool enum), `A (AValue.bool config)),
                        state.env))
        ({state with control = Exp v}, ss) global
    | S.Accessor ({S.getter = g; S.setter = s}, enum, config) ->
      push (F.PropAccessor (S.pos_of g, name,
                            Some s, ({O.getter = `A `Undef;
                                      O.setter = `A `Undef},
                                     `A (AValue.bool enum),
                                     `A (AValue.bool config)),
                            state.env))
        ({state with control = Exp g}, ss) global

  (* Inspired from LambdaS5's Ljs_cesk.eval_cesk function *)
  let step_exp (exp : S.exp) ((state, ss) as conf : conf) (global : global)
    : (stack_change * conf) list = match exp with
    | S.Null _ | S.Undefined _ | S.String _ | S.Num _ | S.True _ | S.False _
    | S.Id _ | S.Lambda _ ->
      let v = eval_atomic state global exp in
      unch (Val (`A v)) conf
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
      let obj = ({O.code = `A `Bot; O.proto = `A `Undef; O.primval = `A `Undef;
                  O.klass = `A (`Str kls);
                  O.extensible = `A (AValue.bool ext)},
                 IdMap.empty) in
      begin match attrs, props with
        | [], [] ->
          unch (Val (`StackObj obj)) (state, ss)
        | [], (prop, exp)::props ->
          push (F.ObjectProps (p, prop, obj, props, state.env))
            ({state with control = Prop (prop, exp)}, ss) global
        | (attr, exp)::attrs, props ->
          push (F.ObjectAttrs (p, attr, obj, attrs, props, state.env))
            ({state with control = Exp exp}, ss) global
      end
    | S.Let (p, id, exp, body) ->
      push (F.Let (p, id, body, state.env))
        ({state with control = Exp exp}, ss) global
    | S.Seq (p, left, right) ->
      push (F.Seq (right, state.env))
        ({state with control = Exp left}, ss) global
    | S.App (p, f, args) ->
      push (F.AppFun (p, f, args, state.env))
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
    | Prop (name, prop) -> step_prop (name, prop) conf global
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
    step_no_gc (GC.gc conf global) global

  let merge ((state, ss) : conf) ((state', _) : conf) : conf =
    ({state with env = Env.merge state.env state'.env;
                 vstore = ValueStore.merge state.vstore state'.vstore;
                 ostore = ObjectStore.merge state.ostore state'.ostore},
     ss)

  let is_value_conf ((state, _) : conf) =
    match state.control with
    | Val _ | PropVal _ -> true
    | _ -> false
end
