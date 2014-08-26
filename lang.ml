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
  type conf
  type state
  val string_of_conf : conf -> string
  module ConfOrdering : BatInterfaces.OrderedType with type t = conf
  type frame
  val string_of_frame : frame -> string
  module FrameOrdering : BatInterfaces.OrderedType with type t = frame
  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged
  module StackChangeOrdering : BatInterfaces.OrderedType with type t = stack_change
  val string_of_stack_change : stack_change -> string
  val inject : exp -> state option -> conf (* can take an initial configuration as argument *)
  (* the frame list argument is the list of the potential frames that reside on
     the top of the stack, not the stack itself *)
  val step : conf -> (conf * frame) option -> (stack_change * conf) list
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

  module StackSummary =
  struct
    (* Stack summary used for garbage collection *)
    type t = AddressSet.t
    let empty = AddressSet.empty
    let compare = AddressSet.compare
    let to_string ss = "[" ^ (BatString.concat ", "
                                (BatList.map Address.to_string
                                   (AddressSet.elements ss))) ^ "]"

    let push ss f =
      AddressSet.union ss (Frame.touch f)
  end

  type conf = state * StackSummary.t

  let string_of_conf (state, ss) = string_of_state state

  let compare_conf (state, ss) (state', ss') =
    order_comp (compare_state state state') (StackSummary.compare ss ss')

  module GC =
  struct
    (* Garbage collection.
       TODO:
         - for now, we only perform GC on the value store. It could be worth
           investigating it on the the object store as well
    *)

    let touch vstore ostore v =
      let rec aux acc visited_objs : AValue.t -> StackSummary.t = function
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
            begin match ObjectStore.lookup a ostore with
              | `Obj obj -> aux_obj (AddressSet.add a acc) (AddressSet.add a visited_objs) obj
              | `ObjT -> failwith "touch: a value was too abtsract"
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


    let rec control_root control env vstore ostore : AddressSet.t = match control with
      | Exp e -> Frame.addresses_of_vars (S.free_vars e) env
      | Prop (S.Data ({S.value = v; _}, _, _)) -> Frame.addresses_of_vars (S.free_vars v) env
      | Prop (S.Accessor ({S.getter = g; S.setter = s}, _, _)) ->
        Frame.addresses_of_vars (IdSet.union (S.free_vars g) (S.free_vars s)) env
      | Frame (control, frame) ->
        AddressSet.union (control_root control env vstore ostore) (Frame.touch frame)
      | Val v -> touch vstore ostore v
      | PropVal (O.Data ({O.value = v1; O.writable = v2}, enum, config) as prop)
      | PropVal (O.Accessor ({O.getter = v1; O.setter = v2}, enum, config) as prop) ->
        Frame.addresses_of_vals (Frame.vals_of_prop prop)
      | Exception (`Break (_, v))
      | Exception (`Throw v) ->
        Frame.addresses_of_vals [v]

    let root (state, ss) : AddressSet.t =
      AddressSet.union ss (control_root state.control state.env state.vstore state.ostore)

    let touching_rel1 vstore ostore addr =
      try match addr with
        | `ObjAddress _ -> touch vstore ostore (`Obj addr)
        | `VarAddress _ -> touch vstore ostore ((ValueStore.lookup addr vstore) :> v)
      with Not_found ->
        print_endline ("Value not found at address " ^ (Address.to_string addr));
        print_endline (ValueStore.to_string vstore);
        raise Not_found

    let touching_rel vstore ostore addr =
      let rec aux todo acc =
        if AddressSet.is_empty todo then
          acc
        else
          let a = AddressSet.choose todo in
          if AddressSet.mem a acc then
            aux (AddressSet.remove a todo) acc
          else
            let addrs = touching_rel1 vstore ostore a in
            aux (AddressSet.remove a (AddressSet.union addrs todo))
              (AddressSet.add a acc)
      in
      aux (AddressSet.singleton addr) AddressSet.empty

    let reachable ((state, ss) : conf) : AddressSet.t =
      let r = root (state, ss) in
      AddressSet.fold (fun a acc ->
          AddressSet.union acc (touching_rel state.vstore state.ostore a))
        r AddressSet.empty

    let gc ((state, ss) : conf) : conf =
      let r = reachable (state, ss) in
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

  (* TODO: put that somewhere else? *)
  let alloc_var id _ state = Address.alloc_var id state.time

  let alloc_obj id _ state = Address.alloc_obj id state.time

  let alloc_if_necessary state id = function
    | #AValue.t as v -> (state.ostore, v)
    | `StackObj obj ->
      let a = alloc_obj id obj state in
      let ostore' = ObjectStore.join a (`Obj obj) state.ostore in
      (ostore', `Obj a)

  let inject (exp : S.exp) (s : state option) : conf =
    let empty = { control = Exp exp; env = Env.empty; vstore = ValueStore.empty;
                  ostore = ObjectStore.empty; time = Time.initial } in
    (BatOption.map_default
       (fun init -> {empty with env = init.env; vstore = init.vstore; ostore = init.ostore})
       empty s,
     StackSummary.empty)

  let unch (control : control) ((state, ss) : conf) =
    [StackUnchanged, ({state with control}, ss)]
  let push (frame : F.t) ((state, ss) : conf) =
    [StackPush frame, (state, StackSummary.push ss frame)]

  let rec get_prop obj prop ostore = match obj with
    | `Obj a ->
      begin match ObjectStore.lookup a ostore with
        | `Obj ({O.proto = pvalue; _}, props) ->
          begin try Some (IdMap.find prop props)
            with Not_found -> get_prop (pvalue :> v) prop ostore
          end
        | `ObjT -> failwith "get_prop: too abstracted"
      end
    | `StackObj ({O.proto = pvalue; _}, props) ->
      begin try Some (IdMap.find prop props)
        with Not_found -> get_prop (pvalue :> v) prop ostore
      end
    | `ObjT -> failwith "get_prop: too abstracted"
    | `Null -> None
    | #AValue.t as v -> failwith ("get_prop on non-object: " ^ (AValue.to_string v))

  (* Inspired from LambdaS5's Ljs_cesk.eval_cesk function *)
  (* TODO: currently, we call Time.tick only when an application takes place
     (apply_fun). It could be worth ticking more (eg. on GetField, SetField,
     etc.) *)
  let step_exp (exp : S.exp) ((state, ss) as conf : conf)
    : (stack_change * conf) list = match exp with
    | S.Null _ -> unch (Val `Null) conf
    | S.Undefined _ -> unch (Val `Undef) conf
    | S.String (_, s) -> unch (Val (`Str s)) conf
    | S.Num (_, n) -> unch (Val (`Num n)) conf
    | S.True _ -> unch (Val `True) conf
    | S.False _ -> unch (Val `False) conf
    | S.Id (_, id) ->
      begin try
          unch (Val ((ValueStore.lookup (Env.lookup id state.env) state.vstore) :> v))
            conf
        with Not_found ->
          print_endline ("Identifier cannot be resolved: " ^ id);
          raise Not_found
      end
    | S.Hint (_, _, e) ->
      unch (Exp e) conf
    | S.Lambda (_, args, body) ->
      let free = S.free_vars body in
      let env' = Env.keep free state.env in
      unch (Val (`Clos (env', args, body))) conf
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
      let state = {state with time = Time.tick p state.time} in
      begin match attrs, props with
        | [], [] ->
          unch (Val (`StackObj obj)) (state, ss)
        | [], (prop, exp)::props ->
          push (F.ObjectProps (prop, obj, props, state.env))
            ({state with control = Prop exp}, ss)
        | (attr, exp)::attrs, props ->
          push (F.ObjectAttrs (p, attr, obj, attrs, props, state.env))
            ({state with control = Exp exp}, ss)
      end
    | S.Let (p, id, exp, body) ->
      print_endline ("Let " ^ id ^ " at " ^ (Pos.string_of_pos p));
      push (F.Let (id, body, state.env))
        ({state with control = Exp exp}, ss)
    | S.Seq (p, left, right) ->
      push (F.Seq (right, state.env))
        ({state with control = Exp left}, ss)
    | S.App (p, f, args) ->
      print_endline ("Apply " ^ (string_of_exp f));
      push (F.AppFun (args, state.env))
        ({state with control = Exp f}, ss)
    | S.Op1 (p, op, arg) ->
      push (F.Op1App (op, state.env))
        ({state with control = Exp arg}, ss)
    | S.Op2 (p, op, arg1, arg2) ->
      push (F.Op2Arg (op, arg2, state.env))
        ({state with control = Exp arg1}, ss)
    | S.If (p, pred, cons, alt) ->
      push (F.If (cons, alt, state.env))
        ({state with control = Exp pred}, ss)
    | S.GetField (p, obj, field, body) ->
      push (F.GetFieldObj (field, body, state.env))
        ({state with control = Exp obj}, ss)
    | S.SetField (p, obj, field, newval, body) ->
      push (F.SetFieldObj (field, newval, body, state.env))
        ({state with control = Exp obj}, ss)
    | S.GetAttr (p, pattr, obj, field) ->
      push (F.GetAttrObj (pattr, field, state.env))
        ({state with control = Exp obj}, ss)
    | S.SetAttr (p, pattr, obj, field, newval) ->
      push (F.SetAttrObj (pattr, field, newval, state.env))
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.GetObjAttr (p, oattr, obj) ->
      push (F.GetObjAttr (oattr, state.env))
        ({state with control = Exp obj}, ss)
    | S.SetObjAttr (p, oattr, obj, newval) ->
      push (F.SetObjAttr (oattr, newval, state.env))
        ({state with control = Exp obj}, ss)
    | S.OwnFieldNames (p, obj) ->
      push (F.OwnFieldNames state.env)
        ({state with control = Exp obj}, ss)
    | S.Rec (p, name, exp, body) ->
      let a = alloc_var name `Undef state in
      let env' = Env.extend name a state.env in
      let vstore' = ValueStore.join a `Undef state.vstore in
      push (F.Rec (name, a, body, env'))
        ({state with control = Exp exp;
                     env = env';
                     vstore = vstore'}, ss)
    | S.SetBang (p, id, exp) ->
      begin try
          let a = Env.lookup id state.env in
          push (F.SetBang (id, a, state.env))
            ({state with control = Exp exp}, ss)
        with Not_found ->
          print_endline ("Identifier cannot be resolved for set!: " ^ id);
          raise Not_found
      end
    | S.Label (p, label, body) ->
      push (F.Label (label, state.env))
        ({state with control = Exp body}, ss)
    | S.Break (p, label, ret) ->
      push (F.Break (label, state.env))
        ({state with control = Exp ret}, ss)
    | S.Throw (p, exp) ->
      push (F.Throw state.env)
        ({state with control = Exp exp}, ss)
    | S.TryCatch (p, body, catch) ->
      push (F.TryCatch (catch, state.env))
        ({state with control = Exp body}, ss)
    | S.TryFinally (p, body, finally) ->
      push (F.TryFinally (finally, state.env))
        ({state with control = Exp body}, ss)
    | S.DeleteField (p, obj, field) ->
      print_endline ("DeleteField: " ^ (string_of_exp obj));
      push (F.DeleteFieldObj (field, state.env))
        ({state with control = Exp obj}, ss)
    | S.Eval _ -> failwith ("Eval not yet handled")

  let rec apply_fun f args (state : state)
    : (S.exp * state) = match f with
    | `Clos (env', args', body) ->
      if (List.length args) != (List.length args') then
        failwith "Arity mismatch"
      else
        let alloc_arg v name (vstore, ostore, env) =
          let (ostore', v') = alloc_if_necessary state name v in
          let a = alloc_var name v' {state with vstore = vstore; ostore = ostore'} in
          (ValueStore.join a v' vstore,
           ostore',
           Env.extend name a env) in
        let (vstore', ostore', env') =
          BatList.fold_right2 alloc_arg args args' (state.vstore, state.ostore, env') in
        (body, {state with env = env'; vstore = vstore'; ostore = ostore';
                           time = Time.tick (S.pos_of body) state.time})
    | `ClosT -> failwith "Closure too abstracted" (* TODO: what to do in this case? *)
    | `Obj a -> begin match ObjectStore.lookup a state.ostore with
        | `Obj ({O.code = `Clos f; _}, _) ->
          apply_fun (`Clos f) args state
        | _ -> failwith "Applied object without code attribute"
      end
    | `ObjT -> failwith "Object too abstracted when applying function"
    | `StackObj ({O.code = `Clos f; _}, _) ->
      apply_fun (`Clos f) args state
    | `StackObj _ -> failwith "Applied object without code attribute"
    | _ -> failwith "Applied non-function"

  let apply_frame (v : v) (frame :frame) (state : state) : state list = match frame with
    | F.Let (id, body, env') ->
      let a = alloc_var id id state in
      let env'' = Env.extend id a env' in
      let ostore', v' = alloc_if_necessary state id v in
      let vstore' = ValueStore.join a v' state.vstore in
      [{state with control = Exp body; env = env''; vstore = vstore'; ostore = ostore'}]
    (* ObjectAttrs of string * O.t * (string * S.exp) list * (string * prop) list * Env.t *)
    | F.ObjectAttrs (p, name, obj, [], [], env') ->
      let ostore', v' = alloc_if_necessary state name v in
      let obj' = O.set_attr_str obj name v' in
      [{state with control = Val (`StackObj obj'); env = env'; ostore = ostore';
                   time = Time.tick p state.time}]
    | F.ObjectAttrs (_, name, obj, [], (name', prop) :: props, env') ->
      let ostore', v' = alloc_if_necessary state name v in
      let obj' = O.set_attr_str obj name v' in
      [{state with control = Frame (Prop prop, F.ObjectProps (name', obj', props, env'));
                   ostore = ostore'; env = env'}]
    | F.ObjectAttrs (p, name, obj, (name', attr) :: attrs, props, env') ->
      let ostore', v' = alloc_if_necessary state name v in
      let obj' = O.set_attr_str obj name v' in
      [{state with control = Frame (Exp attr, F.ObjectAttrs (p, name', obj', attrs, props, env'));
                   ostore = ostore'; env = env'}]
    (* PropData of (O.data * AValue.t * AValue.t) * Env.t *)
    | F.PropData ((data, enum, config), env') ->
      let ostore', v' = alloc_if_necessary state "propdata" v in
      [{state with control = PropVal (O.Data ({data with O.value = v'},
                                              enum, config));
                   ostore = ostore'; env = env'}]
    (* PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t *)
    | F.PropAccessor (None, (accessor, enum, config), env') ->
      let ostore', v' = alloc_if_necessary state "propacc-set" v in
      [{state with control = PropVal (O.Accessor ({accessor with O.setter = v'},
                                                  enum, config));
                   ostore = ostore'; env = env'}]
    | F.PropAccessor (Some exp, (accessor, enum, config), env') ->
      let ostore', v' = alloc_if_necessary state "propacc-get" v in
      [{state with control = Frame (Exp exp, (F.PropAccessor
                                                (None, ({accessor with O.getter = v'},
                                                        enum, config), env')));
                   ostore = ostore'; env = env'}]
    | F.Seq (exp, env') ->
      [{state with control = Exp exp; env = env'}]
    | F.AppFun ([], env') ->
      let (exp, state') = apply_fun v [] state in
      [{state' with control = Exp exp}]
    | F.AppFun (arg :: args, env') ->
      [{state with control = Frame (Exp arg, (F.AppArgs (v, [], args, env')));
                   env = env'}]
    | F.AppArgs (f, vals, [], env') ->
      let args = BatList.rev (v :: vals) in
      let (exp, state') = apply_fun f args state in
      [{state' with control = Exp exp}]
    | F.AppArgs (f, vals, arg :: args, env') ->
      [{state with control = Frame (Exp arg, (F.AppArgs (f, v :: vals, args, env')));
                   env = env'}]
    | F.Op1App (op, env') ->
      (* TODO: we should avoid allocating for op1 and op2 *)
      let ostore', v' = alloc_if_necessary state ("op1-" ^ op) v in
      [{state with control = Val ((D.op1 ostore' op v') :> v);
                   ostore = ostore'; env = env'}]
    | F.Op2Arg (op, arg2, env') ->
      [{state with control = Frame (Exp arg2, (F.Op2App (op, v, env')));
                   env = env'}]
    | F.Op2App (op, arg1, env') ->
      (* TODO: we should avoid allocating for op1 and op2 *)
      let ostore', arg1' = alloc_if_necessary state ("op2-" ^ op ^ "arg1") arg1 in
      let ostore'', arg2' = alloc_if_necessary {state with ostore = ostore'} ("op2-" ^ op ^ "arg2") v in
      [{state with control = Val ((D.op2 state.ostore op arg1' arg2') :> v);
                   ostore = ostore''; env = env'}]
    | F.If (cons, alt, env') -> begin match v with
        | `True -> [{state with control = Exp cons; env = env'}]
        | `BoolT | `Top -> [{state with control = Exp cons; env = env'};
                            {state with control = Exp alt; env = env'}]
        | _ -> [{state with control = Exp alt; env = env'}]
      end
    | F.GetFieldObj (field, body, env') ->
      [{state with control = Frame (Exp field, F.GetFieldField (v, body, env'));
                   env = env'}]
    | F.GetFieldField (obj, body, env') ->
      [{state with control = Frame (Exp body, F.GetFieldBody (obj, v, env'));
                   env = env'}]
    | F.GetFieldBody (obj, field, env') ->
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match get_prop (`Obj a) s state.ostore with
            | Some (O.Data ({O.value = v; _}, _, _)) ->
              [{state with control = Val (v :> v); env = env'}]
            | Some (O.Accessor ({O.getter = g; _}, _, _)) ->
              let (body, state') = apply_fun (g :> v) [obj; v] state in
              [{state' with control = Frame (Exp body, F.RestoreEnv env')}]
            | None -> [{state with control = Val `Undef; env = env'}]
          end
        | `Obj _, `StrT ->
          (* We can handle this case more precisely by returning a state for
             each possible value of a field in this object *)
          print_endline "Trying to access a field with a stringT name";
          [{state with control = Val `Top; env = env'}]
        | `ObjT, _ -> failwith "GetFieldBody: object too abstracted"
        | _ -> failwith "GetFieldBody on a non-object or non-string field"
      end
    | F.SetFieldObj (field, newval, body, env') ->
      [{state with control = Frame (Exp field, F.SetFieldField (v, newval, body, env'));
                   env = env'}]
    | F.SetFieldField (obj, newval, body, env') ->
      [{state with control = Frame (Exp newval, F.SetFieldNewval (obj, v, body, env'));
                   env = env'}]
    | F.SetFieldNewval (obj, field, body, env') ->
      [{state with control = Frame (Exp body, F.SetFieldArgs (obj, field, v, env'));
                   env = env'}]
    | F.SetFieldArgs (obj_, field, newval, env') ->
      (* TODO: allow objects to contain objects that don't live in the store *)
      let body = v in
      let ostore', obj = alloc_if_necessary state "setfieldargs" obj_ in
      let state = {state with ostore = ostore'} in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match ObjectStore.lookup a state.ostore with
            | `Obj ({O.extensible = extensible; _} as attrs, props) ->
              begin match get_prop obj s state.ostore with
                | Some (O.Data ({O.writable = `True; _}, enum, config)) ->
                  let (enum, config) = if O.has_prop (attrs, props) (`Str s) then
                      (enum, config)
                    else
                      (`True, `True) in
                  let ostore', newval' = alloc_if_necessary state ("setfieldargs" ^ s) newval in
                  let newobj = O.set_prop (attrs, props) s
                      (O.Data ({O.value = newval'; O.writable = `True},
                               enum, config)) in
                  let ostore'' = ObjectStore.set a (`Obj newobj) state.ostore in
                  [{state with control = Val (newval :> v); env = env'; ostore = ostore''}]
                | Some (O.Data _)
                | Some (O.Accessor ({O.setter = `Undef; _}, _, _)) ->
                  failwith "unwritable" (* TODO: throw *)
                | Some (O.Accessor ({O.setter = setter; _}, _, _)) ->
                  let (exp, state') = apply_fun (setter :> v) [obj; body] state in
                  [{state' with control = Frame (Exp exp, F.RestoreEnv env')}]
                | None ->
                  match extensible with
                  | `True ->
                    let ostore', newval' = alloc_if_necessary state ("setfieldargs" ^ s) newval in
                    let newobj = O.set_prop (attrs, props) s
                        (O.Data ({O.value = newval'; O.writable = `True},
                                 `True, `True)) in
                    let ostore'' = ObjectStore.set a (`Obj newobj) state.ostore in
                    [{state with control = Val (newval' :> v); env = env'; ostore = ostore''}]
                  | `False ->
                    [{state with control = Val `Undef}]
                  | _ -> failwith "TODO: SetFieldArgs frame"
              end
            | `ObjT -> failwith "SetFieldArgs: object too abstracted"
          end
        | `StackObj _, _ -> failwith "TODO: SetFieldArgs on a stack object"
        | _ -> failwith "update field"
      end
    | F.GetAttrObj (pattr, field, env') ->
      [{state with control = Frame (Exp field, F.GetAttrField (pattr, v, env'));
                   env = env'}]
    | F.GetAttrField (pattr, obj, env') ->
      begin match obj, v with
        | `Obj a, `Str s ->
          begin match ObjectStore.lookup a state.ostore with
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
        | _ -> failwith "GetAttrField on a non-object"
      end
    | F.SetAttrObj (pattr, field, newval, env') ->
      [{state with control = Frame (Exp field, F.SetAttrField (pattr, v, newval, env'));
                   env = env'}]
    | F.SetAttrField (pattr, obj, newval, env') ->
      [{state with control = Frame (Exp newval, F.SetAttrNewval (pattr, obj, v, env'));
                   env = env'}]
    | F.SetAttrNewval (pattr, obj_, field, env') ->
      let ostore', obj = alloc_if_necessary state "setattrnewvalobj" obj_ in
      let ostore'', newval = alloc_if_necessary {state with ostore = ostore'} "setattrnewvalv" v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match ObjectStore.lookup a ostore'' with
            | `Obj o ->
              let newobj = O.set_attr o pattr s newval in
              let ostore''' = ObjectStore.set a (`Obj newobj) ostore'' in
              [{state with control = Val `True; env = env'; ostore = ostore'''}]
            | `ObjT -> failwith "SetAttrNewval: object too abstracted"
          end
        | `ObjT, _ -> failwith "SetAttrNewval: object too abstracted"
        | _ -> failwith "SetAttrNewval on a non-object or non-string attribute"
      end
    | F.GetObjAttr (oattr, env') -> begin match v with
        | `Obj a -> begin match ObjectStore.lookup a state.ostore with
            | `Obj obj -> [{state with control = Val ((O.get_obj_attr obj oattr) :> v); env = env'}]
            | `ObjT ->
              (* TODO: Could be more precise here *)
              [{state with control = Val `Top; env = env'}]
          end
        | `ObjT -> failwith "GetObjAttr: object too abstracted"
        | _ -> failwith "GetObjAttr on a non-object"
      end
    | F.SetObjAttr (oattr, newval, env') ->
      [{state with control = Frame (Exp newval, F.SetObjAttrNewval (oattr, v, env'));
                   env = env'}]
    | F.SetObjAttrNewval (oattr, obj, env') ->
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
        | `Obj a -> begin match ObjectStore.lookup a state.ostore with
            | `Obj (attrs, props) ->
              let ostore', v' = alloc_if_necessary state
                  ("setobjattrnewval-" ^ (S.string_of_oattr oattr)) v in
              let newobj = (helper attrs v', props) in
              let ostore'' = ObjectStore.set a (`Obj newobj) ostore' in
              [{state with control = Val (v' :> v);
                           ostore = ostore''; env = env'}]
            | `ObjT -> failwith "SetObjAttrNewval: object too abstract"
          end
        | `StackObj _ ->
          (* TODO: this object lives on the stack and will not be returned by this
             operation, it is therefore not reachable. Is this expected? *)
          [{state with control = Val v; env = env'}]
        | `ObjT -> failwith "SetObjAttrNewval: object too abstracted"
        | _ -> failwith "SetObjAttrNewval on a non-object"
      end
    | F.OwnFieldNames env' -> begin match v with
        | `Obj a -> begin match ObjectStore.lookup a state.ostore with
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
              let addr = alloc_obj "obj" obj' state in
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
        | `Obj a, `Str s -> begin match ObjectStore.lookup a state.ostore with
            | `Obj obj ->
              if O.has_prop obj (`Str s) then
                match O.lookup_prop obj (`Str s) with
                (* TODO: BoolT *)
                | O.Data (_, _, `True) | O.Accessor (_, _, `True) ->
                  let newobj = O.remove_prop obj (`Str s) in
                  let ostore' = ObjectStore.set a (`Obj newobj) state.ostore in
                  [{state with control = Val `True; env = env'; ostore = ostore'}]
                | _ ->
                  [{state with control = Exception (`Throw (`Str "unconfigurable-delete"));
                               env = env'}]
              else
                [{state with control = Val `False; env = env'}]
            | `ObjT -> failwith "DeleteFieldField: object too abstracted"
          end
        | `StackObj obj, `Str s ->
          (* This stack object will not be reachable when this is reached *)
          if O.has_prop obj (`Str s) then
            match O.lookup_prop obj (`Str s) with
            (* TODO: BoolT *)
            | O.Data (_, _, `True) | O.Accessor (_, _, `True) ->
              [{state with control = Val `True; env = env'}]
            | _ ->
              [{state with control = Exception (`Throw (`Str "unconfigurable-delete"));
                           env = env'}]
          else
            [{state with control = Val `False; env = env'}]
        | v1, v2 -> failwith ("DeleteFieldField on a non-object or non-string: " ^ (F.string_of_value v1) ^ ", " ^ (F.string_of_value v2))
      end
    | F.Rec (name, a, body, env') ->
      let ostore', v' = alloc_if_necessary state ("rec-" ^ name) v in
      let vstore' = ValueStore.set a v' state.vstore in
      [{state with control = Exp body;
                   vstore = vstore'; ostore = ostore'; env = env'}]
    | F.SetBang (name, a, env') ->
      let ostore', v' = alloc_if_necessary state ("setbang-" ^ name) v in
      let vstore' = ValueStore.set a v' state.vstore in
      [{state with control = Val (v' :> v);
                   vstore = vstore'; ostore = ostore'; env = env'}]
    | F.Label (_, env') ->
      [{state with env = env'}]
    | F.Break (lab, env') ->
      [{state with control = Exception (`Break (lab, v)); env = env'}]
    | F.Throw env' ->
      [{state with control = Exception (`Throw v); env = env'}]
    | F.TryCatch (_, env') ->
      (* No exception has been caught, continue normal execution *)
      [{state with control = Val v; env = env'}]
    | F.TryCatchHandler (exc, env') ->
      (* Exception should be handled by the handler *)
      let (body, state') = apply_fun v [exc] state in
      [{state' with control = Frame (Exp body, F.RestoreEnv env')}]
    | F.TryFinally (finally, env') ->
      (* No exception, execute the finally *)
      [{state with control = Exp finally; env = env'}]
    | F.TryFinallyExc (exc, env') ->
      (* Finally has been executed, rethrow the exception *)
      [{state with control = Exception exc; env = env'}]
    | F.RestoreEnv env' ->
      [{state with control = Val v; env = env'}]
    | f -> failwith ("apply_frame: not implemented: " ^ (string_of_frame f))

  let apply_frame_prop v frame (state : state) : state = match frame with
    (* ObjectProps of string * O.t * (string * prop) list * Env.t *)
    | F.ObjectProps (name, obj, [], env') ->
      let obj' = O.set_prop obj name v in
      let a = alloc_obj name obj' state in
      let ostore' = ObjectStore.join a (`Obj obj') state.ostore in
      {state with control = Val (`Obj a); env = env'; ostore = ostore'}
    | F.ObjectProps (name, obj, (name', prop) :: props, env') ->
      let obj' = O.set_prop obj name v in
      {state with control = Frame (Prop prop, F.ObjectProps (name', obj', props, env'));
                  env = env'}
    | f -> failwith ("apply_frame_prop: not implemented: " ^ (string_of_frame f))

  let apply_frame_exc e frame state : state = match e, frame with
    | `Break (label, v), F.Label (l, env') ->
      {state with control = Val v; env = env'}
    | `Break b, F.TryFinally (finally, env') ->
      {state with control = Frame (Exp finally, F.TryFinallyExc (`Break b, env'));
                  env = env'}
    | `Break _, _ -> state
    | `Throw v, F.TryCatch (handler, env') ->
      {state with control = Frame (Exp handler, F.TryCatchHandler (v, env'));
                  env = env'}
    | `Throw v, F.TryFinally (finally, env') ->
      {state with control = Frame (Exp finally, F.TryFinallyExc (`Throw v, env'));
                  env = env'}
    | `Throw _, _ -> state

  let step_prop p ((state, ss) : conf)
    : (stack_change * conf) list = match p with
    | S.Data ({S.value = v; S.writable = w}, enum, config) ->
      push (F.PropData (({O.value = `Undef; O.writable = AValue.bool w},
                         AValue.bool enum, AValue.bool config),
                        state.env))
        ({state with control = Exp v}, ss)
    | S.Accessor ({S.getter = g; S.setter = s}, enum, config) ->
      push (F.PropAccessor (Some s, ({O.getter = `Undef; O.setter = `Undef},
                                     AValue.bool enum, AValue.bool config),
                            state.env))
        ({state with control = Exp g}, ss)

  let step_no_gc ((state, ss) as conf : conf) (frame : (conf * F.t) option)
    : (stack_change * conf) list =
    let res = match state.control with
      | Exp e -> step_exp e conf
      | Prop p -> step_prop p conf
      | Val v -> begin match frame with
          | Some ((_, ss'), frame) ->
            BatList.map (fun state -> (StackPop frame, (state, ss'))) (apply_frame v frame state)
          | None -> []
        end
      | Frame (control', frame) ->
        [StackPush frame, ({state with control = control'},
                           StackSummary.push ss frame)]
      | PropVal prop -> begin match frame with
          | Some ((state', ss'), frame) ->
            [StackPop frame, (apply_frame_prop prop frame state, ss')]
          | None -> []
        end
      | Exception e -> begin match frame with
          | Some ((state', ss'), frame) ->
            [StackPop frame, (apply_frame_exc e frame state, ss')]
          | None -> []
        end
    in
    (* print_endline ((string_of_state state) ^ " -> " ^
                   (string_of_list res
                      (fun (g, c) -> (string_of_stack_change g) ^ " -> " ^
                                     (string_of_state c)))); *)
    res

  let step conf = step_no_gc (if !gc then GC.gc conf else conf)
end
