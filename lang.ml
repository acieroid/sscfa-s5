open Prelude
open Shared
open Env
open Store
open Lattice

module D = Delta
module S = Ljs_syntax
module O = Obj_val
module F = Frame

module type Lang_signature =
sig
  type exp
  val string_of_exp : exp -> string
  type conf
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
  val inject : exp -> conf
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

  (* type clo = [`Clos of Env.t * id list * S.exp ] *)

  type control =
    | Exp of S.exp
    | Prop of S.prop
    | PropVal of O.prop
    | Val of AValue.t
    | Frame of (control * F.t)

  let string_of_control = function
    | Exp exp -> "Exp(" ^ (string_of_exp exp) ^ ")"
    | Prop prop -> "Prop(" ^ (string_of_prop prop) ^ ")"
    | Val v -> "Val(" ^ (AValue.to_string v) ^ ")"
    | PropVal v -> "PropVal(" ^ (O.string_of_prop v) ^ ")"
    | Frame (exp, f) -> "Frame(" ^ (F.to_string f) ^ ")"

  type state = {
    control : control;
    env : Env.t;
    vstore : ValueStore.t;
    ostore : ObjectStore.t;
    time : Time.t;
  }

  let string_of_state state = string_of_control state.control

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

    let touch (vstore : ValueStore.t) (ostore : ObjectStore.t) =
      let rec aux acc visited_objs = function
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
              | `Obj obj -> aux_obj acc (AddressSet.add a visited_objs) obj
              | `ObjT -> failwith "touch: a value was too abtsract"
            end
        | `ClosT | `ObjT | `Top -> failwith "touch: a value was too abstract"
      and aux_obj acc visited_objs ((attrs, props) : O.t) =
        aux_obj_props
          (List.fold_left AddressSet.union acc
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
                            aux acc visited_objs config]) visited_objs  props
        | (_, O.Accessor ({O.getter = g; O.setter = s}, enum, config)) :: props ->
          aux_obj_props (List.fold_left AddressSet.union acc
                           [aux acc visited_objs g;
                            aux acc visited_objs s;
                            aux acc visited_objs enum;
                            aux acc visited_objs config]) visited_objs props
      in
      aux AddressSet.empty AddressSet.empty

    let rec control_root control env vstore ostore : AddressSet.t = match control with
      | Exp e -> Frame.addresses_of_vars (S.free_vars e) env
      | Prop (S.Data ({S.value = v; _}, _, _)) -> Frame.addresses_of_vars (S.free_vars v) env
      | Prop (S.Accessor ({S.getter = g; S.setter = s}, _, _)) ->
        Frame.addresses_of_vars (IdSet.union (S.free_vars g) (S.free_vars s)) env
      | Frame (control, frame) ->
        AddressSet.union (control_root control env vstore ostore) (Frame.touch frame)
      | Val v -> touch vstore ostore v
      | PropVal _ -> AddressSet.empty

    let root (state, ss) : AddressSet.t =
      AddressSet.union ss (control_root state.control state.env state.vstore state.ostore)

    let touching_rel1 vstore ostore addr =
      try
        touch vstore ostore (ValueStore.lookup addr vstore)
      with Not_found ->
        print_endline ("Value not found at address " ^ (Address.to_string addr));
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
      AddressSet.fold (fun a acc ->
          AddressSet.union acc (touching_rel state.vstore state.ostore a))
        (root (state, ss)) AddressSet.empty

    let gc ((state, ss) : conf) : conf =
      ({state with
        vstore = ValueStore.restrict (reachable (state, ss)) state.vstore},
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
  let alloc_val id _ state = Address.alloc id state.time

  let alloc_obj id _ state = Address.alloc id state.time

  let inject (exp : S.exp) : conf = ({
    control = Exp exp;
    env = Env.empty;
    vstore = ValueStore.empty;
    ostore = ObjectStore.empty;
    time = Time.initial;
  }, StackSummary.empty)

  let unch (control : control) ((state, ss) : conf) =
    [StackUnchanged, ({state with control}, ss)]
  let push (frame : F.t) ((state, ss) : conf) =
    [StackPush frame, (state, StackSummary.push ss frame)]

  let rec get_prop obj prop ostore = match obj with
    | `Obj a ->
      begin match ObjectStore.lookup a ostore with
        | `Obj ({O.proto = pvalue; _}, props) ->
          begin try Some (IdMap.find prop props)
            with Not_found -> get_prop pvalue prop ostore
          end
        | `ObjT -> failwith "get_prop: too abstracted"
      end
    | `ObjT -> failwith "get_prop: too abstracted"
    | `Null -> None
    | _ -> failwith ("get_prop on non-object: " ^ (AValue.to_string obj))

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
      unch (Val (ValueStore.lookup (Env.lookup id state.env) state.vstore))
        conf
    | S.Lambda (_, args, body) ->
      let free = S.free_vars body in
      let env' = Env.keep free state.env in
      unch (Val (`Clos (env', args, body))) conf
    | S.Object (_, attrs, props) ->
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
      begin match attrs, props with
        | [], [] ->
          let a = alloc_obj "obj" obj state in
          let ostore' = ObjectStore.join a (`Obj obj) state.ostore in
          unch (Val (`Obj a)) ({state with ostore = ostore'}, ss)
        | [], (prop, exp)::props ->
          push (F.ObjectProps (prop, obj, props, state.env))
            ({state with control = Prop exp}, ss)
        | (attr, exp)::attrs, props ->
          push (F.ObjectAttrs (attr, obj, attrs, props, state.env))
            ({state with control = Exp exp}, ss)
      end
    | S.Let (p, id, exp, body) ->
      push (F.Let (id, body, state.env))
        ({state with control = Exp exp; time = Time.tick p state.time}, ss)
    | S.Seq (p, left, right) ->
      push (F.Seq (right, state.env))
        ({state with control = Exp left; time = Time.tick p state.time}, ss)
    | S.App (p, f, args) ->
      push (F.AppFun (args, state.env))
        ({state with control = Exp f; time = Time.tick p state.time}, ss)
    | S.Op1 (p, op, arg) ->
      push (F.Op1App (op, state.env))
        ({state with control = Exp arg; time = Time.tick p state.time}, ss)
    | S.Op2 (p, op, arg1, arg2) ->
      push (F.Op2Arg (op, arg2, state.env))
        ({state with control = Exp arg1; time = Time.tick p state.time}, ss)
    | S.If (p, pred, cons, alt) ->
      push (F.If (cons, alt, state.env))
        ({state with control = Exp pred; time = Time.tick p state.time}, ss)
    | S.GetField (p, obj, field, body) ->
      push (F.GetFieldObj (field, body, state.env))
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.SetField (p, obj, field, newval, body) ->
      push (F.SetFieldObj (field, newval, body, state.env))
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.GetAttr (p, pattr, obj, field) ->
      push (F.GetAttrObj (pattr, field, state.env))
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.SetAttr (p, pattr, obj, field, newval) ->
      push (F.SetAttrObj (pattr, field, newval, state.env))
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.GetObjAttr (p, oattr, obj) ->
      push (F.GetObjAttr (oattr, state.env))
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.OwnFieldNames (p, obj) ->
      push (F.OwnFieldNames state.env)
        ({state with control = Exp obj; time = Time.tick p state.time}, ss)
    | S.Rec (p, name, exp, body) ->
      let a = alloc_val name `Undef state in
      let env' = Env.extend name a state.env in
      let vstore' = ValueStore.join a `Undef state.vstore in
      push (F.Rec (name, a, body, env'))
        ({state with control = Exp exp;
                     env = env';
                     vstore = vstore';
                     time = Time.tick p state.time}, ss)
    | _ -> failwith ("Not yet handled " ^ (string_of_exp exp))

  let rec apply_fun f args (state : state)
    : (S.exp * state) = match f with
    | `Clos (env', args', body) ->
      if (List.length args) != (List.length args') then
        failwith "Arity mismatch"
      else
        let alloc_arg v name (vstore, env) =
          let a = alloc_val name v state in
          (ValueStore.join a v vstore,
           Env.extend name a env) in
        let (vstore', env') =
          BatList.fold_right2 alloc_arg args args' (state.vstore, env') in
        (body, {state with env = env'; vstore = vstore';
                           time = Time.tick (S.pos_of body) state.time})
    | `ClosT -> failwith "Closure too abstracted" (* TODO: what to do in this case? *)
    | `Obj a -> begin match ObjectStore.lookup a state.ostore with
        | `Obj ({O.code = `Clos f; _}, _) ->
          apply_fun (`Clos f) args state
        | _ -> failwith "Applied object without code attribute"
      end
    | _ -> failwith "Applied non-function"

  let apply_frame v frame (state : state) : state = match frame with
    | F.Let (id, body, env') ->
      let a = alloc_val id id state in
      let env'' = Env.extend id a env' in
      let vstore' = ValueStore.join a v state.vstore in
      {state with control = Exp body; env = env''; vstore = vstore'}
    (* ObjectAttrs of string * O.t * (string * S.exp) list * (string * prop) list * Env.t *)
    | F.ObjectAttrs (name, obj, [], [], env') ->
      let obj' = O.set_attr_str obj name v in
      let a = alloc_obj name obj' state in
      let ostore' = ObjectStore.join a (`Obj obj') state.ostore in
      {state with control = Val (`Obj a); env = env';  ostore = ostore'}
    | F.ObjectAttrs (name, obj, [], (name', prop) :: props, env') ->
      let obj' = O.set_attr_str obj name v in
      {state with control = Frame (Prop prop, F.ObjectProps (name', obj', props, env'));
                  env = env'}
    | F.ObjectAttrs (name, obj, (name', attr) :: attrs, props, env') ->
      let obj' = O.set_attr_str obj name v in
      {state with control = Frame (Exp attr, F.ObjectAttrs (name', obj', attrs, props, env'));
                  env = env'}
    (* PropData of (O.data * AValue.t * AValue.t) * Env.t *)
    | F.PropData ((data, enum, config), env') ->
      {state with control = PropVal (O.Data ({data with O.value = v}, enum, config));
                  env = env'}
    (* PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t *)
    | F.PropAccessor (None, (accessor, enum, config), env') ->
      {state with control = PropVal (O.Accessor ({accessor with O.setter = v}, enum, config));
                  env = env'}
    | F.PropAccessor (Some exp, (accessor, enum, config), env') ->
      {state with
       control = Frame (Exp exp, (F.PropAccessor (None, ({accessor with O.getter = v},
                                                         enum, config), env')));
       env = env'}
    | F.Seq (exp, env') ->
      {state with control = Exp exp; env = env'}
    | F.AppFun ([], env') ->
      let (exp, state') = apply_fun v [] state in
      {state' with control = Exp exp}
    | F.AppFun (arg :: args, env') ->
      {state with control = Frame (Exp arg, (F.AppArgs (v, [], args, env')));
                  env = env'}
    | F.AppArgs (f, vals, [], env') ->
      let (exp, state') = apply_fun f (BatList.rev (v :: vals)) state in
      {state' with control = Exp exp}
    | F.AppArgs (f, vals, arg :: args, env') ->
      {state with control = Frame (Exp arg, (F.AppArgs (f, v :: vals, args, env')));
                  env = env'}
    | F.Op1App (op, env') ->
      {state with control = Val (D.op1 state.ostore op v);
                  env = env'}
    | F.Op2Arg (op, arg2, env') ->
      {state with control = Frame (Exp arg2, (F.Op2App (op, v, env')));
                  env = env'}
    | F.Op2App (op, arg1, env') ->
      {state with control = Val (D.op2 state.ostore op arg1 v);
                  env = env'}
    | F.If (cons, alt, env') -> begin match v with
        | `True -> {state with control = Exp cons; env = env'}
        | `BoolT | `Top -> failwith "TODO: two if possibilities (If frame)"
        | _ -> {state with control = Exp alt; env = env'}
      end
    | F.GetFieldObj (field, body, env') ->
      {state with control = Frame (Exp field, F.GetFieldField (v, body, env'));
                  env = env'}
    | F.GetFieldField (obj, body, env') ->
      {state with control = Frame (Exp body, F.GetFieldBody (obj, v, env'));
                  env = env'}
    | F.GetFieldBody (obj, field, env') ->
      let body = v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match get_prop (`Obj a) s state.ostore with
            | Some (O.Data ({O.value = v; _}, _, _)) ->
              {state with control = Val v; env = env'}
            | Some (O.Accessor ({O.getter = g; _}, _, _)) ->
              let (body, state') = apply_fun g [obj; body] state in
              {state' with control = Frame (Exp body, F.RestoreEnv env')}
            | None -> {state with control = Val `Undef; env = env'}
          end
        | `Obj _, `StrT -> failwith "TODO: GetFieldBody frame"
        | `ObjT, _ -> failwith "TODO: GetFieldBody frame"
        | _ -> failwith "TODO: GetFieldBody frame"
      end
    | F.SetFieldObj (field, newval, body, env') ->
      {state with control = Frame (Exp field, F.SetFieldField (v, newval, body, env'));
                  env = env'}
    | F.SetFieldField (obj, newval, body, env') ->
      {state with control = Frame (Exp newval, F.SetFieldNewval (obj, v, body, env'));
                  env = env'}
    | F.SetFieldNewval (obj, field, body, env') ->
      {state with control = Frame (Exp body, F.SetFieldArgs (obj, field, v, env'));
                  env = env'}
    | F.SetFieldArgs (obj, field, newval, env') ->
      let body = v in
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
                  let newobj = O.set_prop (attrs, props) s
                      (O.Data ({O.value = newval; O.writable = `True},
                               enum, config)) in
                  let ostore' = ObjectStore.set a (`Obj newobj) state.ostore in
                  {state with control = Val newval; env = env'; ostore = ostore'}
                | Some (O.Data _)
                | Some (O.Accessor ({O.setter = `Undef; _}, _, _)) ->
                  failwith "unwritable" (* TODO: throw *)
                | Some (O.Accessor ({O.setter = setter; _}, _, _)) ->
                  let (exp, state') = apply_fun setter [obj; body] state in
                  {state' with control = Frame (Exp exp, F.RestoreEnv env')}
                | None ->
                  match extensible with
                  | `True ->
                    let newobj = O.set_prop (attrs, props) s
                        (O.Data ({O.value = newval; O.writable = `True},
                                 `True, `True)) in
                    let ostore' = ObjectStore.set a (`Obj newobj) state.ostore in
                    {state with control = Val newval; env = env'; ostore = ostore'}
                  | `False ->
                    {state with control = Val `Undef}
                  | _ -> failwith "TODO: SetFieldArgs frame"
              end
            | `ObjT -> failwith "TODO: SetFieldArgs frame"
          end
        | _ -> failwith "update field"
      end
    | F.GetAttrObj (pattr, field, env') ->
      {state with control = Frame (Exp field, F.GetAttrField (pattr, v, env'));
                  env = env'}
    | F.GetAttrField (pattr, obj, env') ->
      let field = v in
      begin match obj with
        | `Obj a ->
          begin match ObjectStore.lookup a state.ostore with
            | `Obj o -> let attr = O.get_attr o pattr field in
              {state with control = Val attr; env = env'}
            | `ObjT -> failwith "TODO: GetAttrField frame"
          end
        | _ -> failwith "TODO: GetAttrField frame"
      end
    | F.SetAttrObj (pattr, field, newval, env') ->
      {state with control = Frame (Exp field, F.SetAttrField (pattr, v, newval, env'));
                  env = env'}
    | F.SetAttrField (pattr, obj, newval, env') ->
      {state with control = Frame (Exp newval, F.SetAttrNewval (pattr, obj, v, env'));
                  env = env'}
    | F.SetAttrNewval (pattr, obj, field, env') ->
      let newval = v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match ObjectStore.lookup a state.ostore with
            | `Obj o ->
              let newobj = O.set_attr o pattr s newval in
              let ostore' = ObjectStore.set a (`Obj newobj) state.ostore in
              {state with control = Val `True; env = env'; ostore = ostore'}
            | `ObjT -> failwith "TODO: SetAttrNewval frame"
          end
        | _ -> failwith "TODO: SetAttrNewval frame"
      end
    | F.GetObjAttr (oattr, env') -> begin match v with
        | `Obj a -> begin match ObjectStore.lookup a state.ostore with
          | `Obj obj -> {state with control = Val (O.get_obj_attr obj oattr); env = env'}
          | `ObjT -> failwith "TODO: GetObjAttr"
          end
        | `ObjT -> failwith "TODO: GetObjAttr"
        | _ -> failwith "GetObjAttr on a non-object"
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
            {state with control = Val (`Obj addr); ostore = ostore'}
          | `ObjT -> failwith "TODO: OwnFieldNames"
          end
        | `ObjT -> failwith "TODO: OwnFieldNames"
        | _ -> failwith "OwnFieldNames on a non-object"
      end
    | F.Rec (name, a, body, env') ->
      let vstore = ValueStore.set a v state.vstore in
      {state with control = Exp body; vstore = vstore}
    | F.RestoreEnv env' ->
      {state with control = Val v; env = env'}
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

  let step_prop p ((state, ss) : conf)
    : (stack_change * conf) list = match p with
    | S.Data ({S.value = v; S.writable = w}, enum, config) ->
      push (F.PropData (({O.value = `Undef; O.writable = AValue.bool w},
                         AValue.bool enum, AValue.bool config),
                        state.env))
        ({state with control = Exp v}, ss)
    | S.Accessor ({S.getter = g; S.setter = s}, enum, config) ->
      push (F.PropAccessor (Some g, ({O.getter = `Undef; O.setter = `Undef},
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
            [StackPop frame, (apply_frame v frame state, ss')]
          | None ->
            []
        end
      | Frame (control', frame) ->
        [StackPush frame, ({state with control = control'},
                           StackSummary.push ss frame)]
      | PropVal prop -> begin match frame with
          | Some ((state', ss'), frame) ->
            print_endline ("apply_frame_prop from state " ^ (string_of_state state));
            let res = [StackPop frame, (apply_frame_prop prop frame state, ss')] in
            print_endline "success";
            res
          | None ->
            []
        end in
    (* print_endline ((string_of_state state) ^ " -> " ^
                   (string_of_list res
                      (fun (g, c) -> (string_of_stack_change g) ^ " -> " ^
                                     (string_of_state c)))); *)
    res

  let step conf = step_no_gc (GC.gc conf)
end
