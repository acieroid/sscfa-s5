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
    | PropVal v -> "PropVal"
    | Frame (exp, f) -> "Frame(" ^ (F.to_string f) ^ ")"

  type state = control * Env.t * ValueStore.t * ObjectStore.t * Time.t

  let string_of_state (control, _, _, _, t) = string_of_control control

  let compare_state (state, env, vstore, ostore, time) (state', env', vstore', ostore', time') =
    order_concat [lazy (Pervasives.compare state state');
                  lazy (Env.compare env env');
                  lazy (ValueStore.compare vstore vstore');
                  lazy (ObjectStore.compare ostore ostore');
                  lazy (Time.compare time time')]

  type conf = state

  let string_of_conf = string_of_state

  let compare_conf = compare_state

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
  let alloc_val id _ (state : state) = match state with
    | (_, _, vstore, _, t) -> Address.alloc id t

  let alloc_obj id _ (state : state) = match state with
    | (_, _, _, ostore, t) -> Address.alloc id t

  let inject (exp : S.exp) : state =
    (Exp exp, Env.empty, ValueStore.empty, ObjectStore.empty, Time.initial)

  let unch conf = [(StackUnchanged, conf)]
  let push frame conf = [(StackPush frame, conf)]

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
  let step_exp (exp : S.exp) ((_, env, vstore, ostore, time) as state : state)
    : (stack_change * conf) list = match exp with
    | S.Null _ -> unch (Val `Null, env, vstore, ostore, time)
    | S.Undefined _ -> unch (Val `Undef, env, vstore, ostore, time)
    | S.String (_, s) -> unch (Val (`Str s), env, vstore, ostore, time)
    | S.Num (_, n) -> unch (Val (`Num n), env, vstore, ostore, time)
    | S.True _ -> unch (Val `True, env, vstore, ostore, time)
    | S.False _ -> unch (Val `False, env, vstore, ostore, time)
    | S.Id (_, id) -> unch (Val (ValueStore.lookup (Env.lookup id env) vstore), env,
                            vstore, ostore, time)
    | S.Lambda (_, args, body) ->
      let free = S.free_vars body in
      let env' = Env.keep free env in
      unch (Val (`Clos (env', args, body)), env, vstore, ostore, time)
    | S.Object (_, attrs, props) ->
      let { S.primval = pexp;
            S.code = cexp;
            S.proto = proexp;
            S.klass = kls;
            S.extensible = ext } = attrs in
      let opt_add name ox xs = match ox with
        | Some x -> (name, x)::xs
        | None -> xs in
      let attrs = [] |>
                  opt_add "proto" proexp |>
                  opt_add "code" cexp |>
                  opt_add "prim" pexp in
      let obj = ({ O.code=`Undef; O.proto=`Undef; O.primval=`Undef;
                   O.klass=(`Str kls);
                   O.extensible = AValue.bool ext },
                 IdMap.empty) in
      begin match attrs, props with
        | [], [] ->
          let a = alloc_obj "obj" obj state in
          let ostore' = ObjectStore.join a (`Obj obj) ostore in
          unch (Val (`Obj a), env, vstore, ostore', time)
        | [], (prop, exp)::props ->
          push (F.ObjectProps (prop, obj, props, env))
            (Prop exp, env, vstore, ostore, time)
        | (attr, exp)::attrs, props ->
          push (F.ObjectAttrs (attr, obj, attrs, props, env))
            (Exp exp, env, vstore, ostore, time)
      end
    | S.Let (p, id, exp, body) ->
      push (F.Let (id, body, env)) (Exp exp, env, vstore, ostore, Time.tick p time)
    | S.Seq (p, left, right) ->
      push (F.Seq (right, env)) (Exp left, env, vstore, ostore, Time.tick p time)
    | S.App (p, f, args) ->
      push (F.AppFun (args, env)) (Exp f, env, vstore, ostore, Time.tick p time)
    | S.Op1 (p, op, arg) ->
      push (F.Op1App (op, env)) (Exp arg, env, vstore, ostore, Time.tick p time)
    | S.Op2 (p, op, arg1, arg2) ->
      push (F.Op2Arg (op, arg2, env)) (Exp arg1, env, vstore, ostore, Time.tick p time)
    | S.If (p, pred, cons, alt) ->
      push (F.If (cons, alt, env)) (Exp pred, env, vstore, ostore, Time.tick p time)
    | S.GetField (p, obj, field, body) ->
      push (F.GetFieldObj (field, body, env)) (Exp obj, env, vstore, ostore, Time.tick p time)
    | S.SetField (p, obj, field, newval, body) ->
      push (F.SetFieldObj (field, newval, body, env)) (Exp obj, env, vstore, ostore, Time.tick p time)
    | S.GetAttr (p, pattr, obj, field) ->
      push (F.GetAttrObj (pattr, field, env)) (Exp obj, env, vstore, ostore, Time.tick p time)
    | S.SetAttr (p, pattr, obj, field, newval) ->
      push (F.SetAttrObj (pattr, field, newval, env)) (Exp obj, env, vstore, ostore, Time.tick p time)
    | _ -> failwith ("Not yet handled " ^ (string_of_exp exp))

  let rec apply_fun f args ((_, _, vstore, ostore, time) as state : state)
    : (S.exp * Env.t * ValueStore.t * ObjectStore.t * Time.t) = match f with
    | `Clos (env', args', body) ->
      if (List.length args) != (List.length args') then
        failwith "Arity mismatch"
      else
        let alloc_arg v name (vstore, env) =
          let a = alloc_val name v state in
          (ValueStore.join a v vstore,
           Env.extend name a env) in
        let (vstore', env') =
          BatList.fold_right2 alloc_arg args args' (vstore, env') in
        (body, env', vstore', ostore, Time.tick (S.pos_of body) time)
    | `ClosT -> failwith "Closure too abstracted" (* TODO: what to do in this case? *)
    | `Obj a -> begin match ObjectStore.lookup a ostore with
        | `Obj ({ O.code = `Clos f; _ }, _) ->
          apply_fun (`Clos f) args state
        | _ -> failwith "Applied object without code attribute"
      end
    | _ -> failwith "Applied non-function"

  let apply_frame v frame ((control, env, vstore, ostore, time) as state : state) _
    : conf = match frame with
    | F.Let (id, body, env') ->
      let a = alloc_val id id state in
      let env'' = Env.extend id a env' in
      let vstore' = ValueStore.join a v vstore in
      (Exp body, env'', vstore', ostore, time)
    (* ObjectAttrs of string * O.t * (string * S.exp) list * (string * prop) list * Env.t *)
    | F.ObjectAttrs (name, obj, [], [], env') ->
      let obj' = O.set_attr_str obj name v in
      let a = alloc_obj name obj' state in
      let ostore' = ObjectStore.join a (`Obj obj') ostore in
      (Val (`Obj a), env', vstore, ostore', time)
    | F.ObjectAttrs (name, obj, [], (name', prop) :: props, env') ->
      let obj' = O.set_attr_str obj name v in
      (Frame (Prop prop, F.ObjectProps (name', obj', props, env')), env', vstore, ostore, time)
    | F.ObjectAttrs (name, obj, (name', attr) :: attrs, props, env') ->
      let obj' = O.set_attr_str obj name v in
      (Frame (Exp attr, F.ObjectAttrs (name', obj', attrs, props, env')), env', vstore, ostore, time)
    (* PropData of (O.data * AValue.t * AValue.t) * Env.t *)
    | F.PropData ((data, enum, config), env') ->
      (PropVal (O.Data ({data with O.value = v}, enum, config)), env', vstore, ostore, time)
    (* PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t *)
    | F.PropAccessor (None, (accessor, enum, config), env') ->
      (PropVal (O.Accessor ({accessor with O.setter = v}, enum, config)), env', vstore, ostore, time)
    | F.PropAccessor (Some exp, (accessor, enum, config), env') ->
      (Frame (Exp exp, (F.PropAccessor (None, ({accessor with O.getter = v}, enum, config), env'))),
       env', vstore, ostore, time)
    | F.Seq (exp, env') ->
      (Exp exp, env', vstore, ostore, time)
    | F.AppFun ([], env') ->
      let (exp, env, vstore, ostore, time) = apply_fun v [] state in
      (Exp exp, env, vstore, ostore, time)
    | F.AppFun (arg :: args, env') ->
      (Frame (Exp arg, (F.AppArgs (v, [], args, env'))), env', vstore, ostore, time)
    | F.AppArgs (f, vals, [], env') ->
      let (exp, env, vstore, ostore, time) = apply_fun f (BatList.rev (v :: vals)) state in
      (Exp exp, env, vstore, ostore, time)
    | F.AppArgs (f, vals, arg :: args, env') ->
      (Frame (Exp arg, (F.AppArgs (f, v :: vals, args, env'))), env', vstore, ostore, time)
    | F.Op1App (op, env') ->
      (Val (D.op1 ostore op v), env', vstore, ostore, time)
    | F.Op2Arg (op, arg2, env') ->
      (Frame (Exp arg2, (F.Op2App (op, v, env'))), env', vstore, ostore, time)
    | F.Op2App (op, arg1, env') ->
      (Val (D.op2 ostore op arg1 v), env', vstore, ostore, time)
    | F.If (cons, alt, env') -> begin match v with
        | `True -> (Exp cons, env', vstore, ostore, time)
        | `BoolT | `Top -> failwith "TODO: two if possibilities (If frame)"
        | _ -> (Exp alt, env', vstore, ostore, time)
      end
    | F.GetFieldObj (field, body, env') ->
      (Frame (Exp field, F.GetFieldField (v, body, env')), env', vstore, ostore, time)
    | F.GetFieldField (obj, body, env') ->
      (Frame (Exp body, F.GetFieldBody (obj, v, env')), env', vstore, ostore, time)
    | F.GetFieldBody (obj, field, env') ->
      let body = v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match get_prop (`Obj a) s ostore with
            | Some (O.Data ({O.value = v; _}, _, _)) -> (Val v, env', vstore, ostore, time)
            | Some (O.Accessor ({O.getter = g; _}, _, _)) ->
              let (body, env'', vstore', ostore, time') = apply_fun g [obj; body] state in
              (Frame (Exp body, F.RestoreEnv env'), env'', vstore', ostore, time')
            | None -> (Val `Undef, env', vstore, ostore, time)
          end
        | `Obj _, `StrT -> failwith "TODO: GetFieldBody frame"
        | `ObjT, _ -> failwith "TODO: GetFieldBody frame"
        | _ -> failwith "TODO: GetFieldBody frame"
      end
    | F.SetFieldObj (field, newval, body, env') ->
      (Frame (Exp field, F.SetFieldField (v, newval, body, env')), env', vstore, ostore, time)
    | F.SetFieldField (obj, newval, body, env') ->
      (Frame (Exp newval, F.SetFieldNewval (obj, v, body, env')), env', vstore, ostore, time)
    | F.SetFieldNewval (obj, field, body, env') ->
      (Frame (Exp body, F.SetFieldArgs (obj, field, v, env')), env', vstore, ostore, time)
    | F.SetFieldArgs (obj, field, newval, env') ->
      let body = v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match ObjectStore.lookup a ostore with
            | `Obj ({O.extensible = extensible; _} as attrs, props) ->
              begin match get_prop obj s ostore with
                | Some (O.Data ({ O.writable = `True; _}, enum, config)) ->
                  let (enum, config) = if O.has_prop (attrs, props) (`Str s) then
                      (enum, config)
                    else
                      (`True, `True) in
                  let newobj = O.set_prop (attrs, props) s
                      (O.Data ({O.value = newval; O.writable = `True},
                               enum, config)) in
                  let ostore' = ObjectStore.set a (`Obj newobj) ostore in
                  (Val newval, env', vstore, ostore', time)
                | Some (O.Data _)
                | Some (O.Accessor ({O.setter = `Undef; _}, _, _)) ->
                  failwith "unwritable" (* TODO: throw *)
                | Some (O.Accessor ({O.setter = setter; _}, _, _)) ->
                  let (exp, env'', vstore', ostore', time') =
                    apply_fun setter [obj; body] state in
                  (Frame (Exp exp, F.RestoreEnv env'), env'', vstore', ostore', time')
                | None ->
                  match extensible with
                  | `True ->
                    let newobj = O.set_prop (attrs, props) s
                        (O.Data ({O.value = newval; O.writable = `True},
                                 `True, `True)) in
                    let ostore' = ObjectStore.set a (`Obj newobj) ostore in
                    (Val newval, env', vstore, ostore', time)
                  | `False ->
                    (Val `Undef, env, vstore, ostore, time)
                  | _ -> failwith "TODO: SetFieldArgs frame"
              end
            | `ObjT -> failwith "TODO: SetFieldArgs frame"
          end
        | _ -> failwith "update field"
      end
    | F.GetAttrObj (pattr, field, env') ->
      (Frame (Exp field, F.GetAttrField (pattr, v, env')), env', vstore, ostore, time)
    | F.GetAttrField (pattr, obj, env') ->
      let field = v in
      begin match obj with
        | `Obj a ->
          begin match ObjectStore.lookup a ostore with
            | `Obj o -> let attr = O.get_attr o pattr field in
              (Val attr, env', vstore, ostore, time)
            | `ObjT -> failwith "TODO: GetAttrField frame"
          end
        | _ -> failwith "TODO: GetAttrField frame"
      end
    | F.SetAttrObj (pattr, field, newval, env') ->
      (Frame (Exp field, F.SetAttrField (pattr, v, newval, env')), env', vstore, ostore, time)
    | F.SetAttrField (pattr, obj, newval, env') ->
      (Frame (Exp newval, F.SetAttrNewval (pattr, obj, v, env')), env', vstore, ostore, time)
    | F.SetAttrNewval (pattr, obj, field, env') ->
      let newval = v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match ObjectStore.lookup a ostore with
            | `Obj o ->
              let newobj = O.set_attr o pattr s newval in
              let ostore' = ObjectStore.set a (`Obj newobj) ostore in
              (Val `True, env', vstore, ostore', time)
            | `ObjT -> failwith "TODO: SetAttrNewval frame"
          end
        | _ -> failwith "TODO: SetAttrNewval frame"
      end
    | _ -> failwith "Not implemented"

  let apply_frame_prop v frame ((_, env, vstore, ostore, time) as state : state) _
    : conf = match frame with
    (* ObjectProps of string * O.t * (string * prop) list * Env.t *)
    | F.ObjectProps (name, obj, [], env') ->
      let obj' = O.set_prop obj name v in
      let a = alloc_obj name obj' state in
      let ostore' = ObjectStore.join a (`Obj obj') ostore in
      (Val (`Obj a), env', vstore, ostore', time)
    | F.ObjectProps (name, obj, (name', prop) :: props, env') ->
      let obj' = O.set_prop obj name v in
      (Frame (Prop prop, F.ObjectProps (name', obj', props, env')), env', vstore, ostore, time)
    | _ -> failwith "Not implemented"

  let step_prop p ((_, env, vstore, ostore, time) : state)
      : (stack_change * conf) list = match p with
    | S.Data ({ S.value = v; S.writable = w }, enum, config) ->
      push (F.PropData (({ O.value = `Undef; O.writable = AValue.bool w },
                       AValue.bool enum, AValue.bool config),
                      env))
        (Exp v, env, vstore, ostore, time)
    | S.Accessor ({ S.getter = g; S.setter = s }, enum, config) ->
      push (F.PropAccessor (Some g, ({ O.getter = `Undef; O.setter = `Undef },
                                   AValue.bool enum, AValue.bool config),
                          env))
        (Exp g, env, vstore, ostore, time)

  let step ((control, env, vstore, ostore, time) as state : state)
      (frame : (state * F.t) option) : (stack_change * conf) list =
    let res = match control with
      | Exp e -> step_exp e state
      | Prop p -> step_prop p state
      | Val v -> begin match frame with
          | Some (state', frame) ->
            [StackPop frame, apply_frame v frame state state']
          | None ->
            []
        end
      | Frame (control', frame) ->
        [(StackPush frame, (control', env, vstore, ostore, time))]
      | PropVal prop -> begin match frame with
          | Some (state', frame) ->
            [StackPop frame, apply_frame_prop prop frame state state']
          | None ->
            []
        end in
    (* print_endline ((string_of_state state) ^ " -> " ^
                   (string_of_list res
                      (fun (g, c) -> (string_of_stack_change g) ^ " -> " ^
                                     (string_of_state c)))); *)
    res
end
