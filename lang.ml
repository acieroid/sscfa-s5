open Prelude
open Shared
open Env
open Store
open Lattice

module D = Delta
module S = Ljs_syntax
module O = Obj_val

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
  val step : conf -> (conf * frame) list -> (stack_change * conf) list
end

module LJS =
struct
  type clo = [`Clos of Env.t * id list * S.exp ]

  type frame =
    (* {let (id = exp) body}, where the exp in the frame is body *)
    | Let of id * S.exp * Env.t
    (* {[field1: val1, ...]} *)
    | ObjectAttrs of string * O.t * (string * S.exp) list * (string * S.prop) list * Env.t
    | ObjectProps of string * O.t * (string * S.prop) list * Env.t
    | PropData of (O.data * AValue.t * AValue.t) * Env.t
    | PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t
    (* left; right *)
    | Seq of S.exp * Env.t
    (* f(arg1, ...) *)
    | AppFun of S.exp list * Env.t
    | AppArgs of AValue.t * AValue.t list * S.exp list * Env.t
    (* op arg *)
    | Op1App of string * Env.t
    (* arg1 op arg2 *)
    | Op2Arg of string * S.exp * Env.t
    | Op2App of string * AValue.t * Env.t
    (* if pred then cons else alt *)
    | If of S.exp * S.exp * Env.t
    (* obj[field] *)
    | GetFieldObj of S.exp * S.exp * Env.t
    | GetFieldField of AValue.t * S.exp * Env.t
    | GetFieldBody of AValue.t * AValue.t * Env.t
    | RestoreEnv of Env.t
    (* obj[field] = val *)
    | SetFieldObj of S.exp * S.exp * S.exp * Env.t
    | SetFieldField of AValue.t * S.exp * S.exp * Env.t
    | SetFieldNewval of AValue.t * AValue.t * S.exp * Env.t
    | SetFieldArgs of AValue.t * AValue.t * AValue.t * Env.t
    (* syntax? *)
    | GetAttrObj of S.pattr * S.exp * Env.t
    | GetAttrField of S.pattr * AValue.t * Env.t

  let string_of_frame = function
    | Let (id, _, _) -> "Let-" ^ id
    | ObjectProps _ -> "ObjectProps"
    | ObjectAttrs _ -> "ObjectAttrs"
    | PropData _ -> "PropData"
    | PropAccessor _ -> "PropAccessor"
    | Seq _ -> "Seq"
    | AppFun _ -> "AppFun"
    | AppArgs _ -> "AppArgs"
    | Op1App _ -> "Op1App"
    | Op2Arg _ -> "Op2Arg"
    | Op2App _ -> "Op2App"
    | If _ -> "If"
    | GetFieldObj _ -> "GetFieldObj"
    | GetFieldField _ -> "GetFieldField"
    | GetFieldBody _ -> "GetFieldBody"
    | RestoreEnv _ -> "RestoreEnv"
    | SetFieldObj _ -> "SetFieldObj"
    | SetFieldField _ -> "SetFieldField"
    | SetFieldNewval _ -> "SetFieldNewval"
    | SetFieldArgs _ -> "SetFieldArgs"
    | GetAttrObj _ -> "GetAttrObj"
    | GetAttrField _ -> "GetAttrField"

  (* TODO: use ppx_deriving? *)
  let compare_frame f f' = match f, f' with
    | Let (id, exp, env), Let (id', exp', env') ->
      order_concat [lazy (Pervasives.compare id id');
                    lazy (Pervasives.compare exp exp');
                    lazy (Env.compare env env')]
    | Let _, _ -> 1
    | _, Let _ -> -1
    | ObjectAttrs (attr, obj, attrs, props, env),
      ObjectAttrs (attr', obj', attrs', props', env') ->
      order_concat [lazy (Pervasives.compare attr attr');
                    lazy (O.compare obj obj');
                    lazy (Pervasives.compare attrs attrs');
                    lazy (Pervasives.compare props props');
                    lazy (Env.compare env env')];
    | ObjectAttrs _, _ -> 1
    | _, ObjectAttrs _ -> -1
    | ObjectProps (prop, obj, props, env),
      ObjectProps (prop', obj', props', env') ->
      order_concat [lazy (Pervasives.compare prop prop');
                    lazy (O.compare obj obj');
                    lazy (Pervasives.compare props props');
                    lazy (Env.compare env env')];
    | ObjectProps _, _ -> 1
    | _, ObjectProps _ -> -1
    | PropData (prop, env), PropData (prop', env') ->
      order_concat [lazy (Pervasives.compare prop prop');
                    lazy (Env.compare env env')]
    | PropData _, _ -> 1
    | _, PropData _ -> -1
    | PropAccessor (exp, acc, env), PropAccessor (exp', acc', env') ->
      order_concat [lazy (Pervasives.compare exp exp');
                    lazy (Pervasives.compare acc acc');
                    lazy (Env.compare env env')]
    | PropAccessor _, _ -> 1
    | _, PropAccessor _ -> -1
    | Seq (right, env), Seq (right', env') ->
      order_concat [lazy (Pervasives.compare right right');
                    lazy (Env.compare env env')]
    | Seq _, _ -> 1
    | _, Seq _ -> -1
    | AppFun (args, env), AppFun (args', env') ->
      order_concat [lazy (Pervasives.compare args args');
                    lazy (Env.compare env env')]
    | AppFun _, _ -> 1
    | _, AppFun _ -> -1
    | AppArgs (f, vals, args, env), AppArgs (f', vals', args', env') ->
      order_concat [lazy (AValue.compare f f');
                    lazy (compare_list AValue.compare vals vals');
                    lazy (Pervasives.compare args args');
                    lazy (Env.compare env env')]
    | AppArgs _, _ -> 1
    | _, AppArgs _ -> -1
    | Op1App (op, env), Op1App (op', env') ->
      order_concat [lazy (Pervasives.compare op op');
                    lazy (Env.compare env env')]
    | Op1App _, _ -> 1
    | _, Op1App _ -> -1
    | Op2Arg (op, arg2, env), Op2Arg (op', arg2', env') ->
      order_concat [lazy (Pervasives.compare op op');
                    lazy (Pervasives.compare arg2 arg2');
                    lazy (Env.compare env env')]
    | Op2Arg _, _ -> 1
    | _, Op2Arg _ -> -1
    | Op2App (op, arg1, env), Op2App (op', arg1', env') ->
      order_concat [lazy (Pervasives.compare op op');
                    lazy (AValue.compare arg1 arg1');
                    lazy (Env.compare env env')]
    | Op2App _, _ -> 1
    | _, Op2App _ -> -1
    | If (cons, alt, env), If (cons', alt', env') ->
      order_concat [lazy (Pervasives.compare cons cons');
                    lazy (Pervasives.compare alt alt');
                    lazy (Env.compare env env')]
    | If _, _ -> 1
    | _, If _ -> -1
    | GetFieldObj (field, body, env), GetFieldObj (field', body', env') ->
      order_concat [lazy (Pervasives.compare field field');
                    lazy (Pervasives.compare body body');
                    lazy (Env.compare env env')]
    | GetFieldObj _, _ -> 1
    | _, GetFieldObj _ -> -1
    | GetFieldField (obj, body, env), GetFieldField (obj', body', env') ->
      order_concat [lazy (AValue.compare obj obj');
                    lazy (Pervasives.compare body body');
                    lazy (Env.compare env env')]
    | GetFieldField _, _ -> 1
    | _, GetFieldField _ -> -1
    | GetFieldBody (obj, field, env), GetFieldBody (obj', field', env') ->
      order_concat [lazy (AValue.compare obj obj');
                    lazy (AValue.compare field field');
                    lazy (Env.compare env env')]
    | GetFieldBody _, _ -> 1
    | _, GetFieldBody _ -> -1
    | RestoreEnv env, RestoreEnv env' ->
      Env.compare env env'
    | RestoreEnv _, _ -> 1
    | _, RestoreEnv _ -> -1
    | SetFieldObj (field, newval, body, env),
      SetFieldObj (field', newval', body', env') ->
      order_concat [lazy (Pervasives.compare field field');
                    lazy (Pervasives.compare newval newval');
                    lazy (Pervasives.compare body body');
                    lazy (Env.compare env env')]
    | SetFieldObj _, _ -> 1
    | _, SetFieldObj _ -> -1
    | SetFieldField (obj, newval, body, env),
      SetFieldField (obj', newval', body', env') ->
      order_concat [lazy (AValue.compare obj obj');
                    lazy (Pervasives.compare newval newval');
                    lazy (Pervasives.compare body body');
                    lazy (Env.compare env env')]
    | SetFieldField _, _ -> 1
    | _, SetFieldField _ -> -1
    | SetFieldNewval (obj, field, body, env),
      SetFieldNewval (obj', field', body', env') ->
      order_concat [lazy (AValue.compare obj obj');
                    lazy (AValue.compare field field');
                    lazy (Pervasives.compare body body');
                    lazy (Env.compare env env')]
    | SetFieldNewval _, _ -> 1
    | _, SetFieldNewval _ -> -1
    | SetFieldArgs (obj, field, newval, env),
      SetFieldArgs (obj', field', newval', env') ->
      order_concat [lazy (AValue.compare obj obj');
                    lazy (AValue.compare field field');
                    lazy (AValue.compare newval newval');
                    lazy (Env.compare env env')]
    | SetFieldArgs _, _ -> 1
    | _, SetFieldArgs _ -> -1
    | GetAttrObj (pattr, field, env), GetAttrObj (pattr', field', env') ->
      order_concat [lazy (Pervasives.compare pattr pattr');
                    lazy (Pervasives.compare field field');
                    lazy (Env.compare env env')]
    | GetAttrObj _, _ -> 1
    | _, GetAttrObj _ -> -1
    | GetAttrField (pattr, obj, env), GetAttrField (pattr', obj', env') ->
      order_concat [lazy (Pervasives.compare pattr pattr');
                    lazy (AValue.compare obj obj');
                    lazy (Env.compare env env')]
    | GetAttrField _, _ -> 1
    | _, GetAttrField _ -> -1

  type control =
    | Exp of S.exp
    | Prop of S.prop
    | PropVal of O.prop
    | Val of AValue.t
    | Frame of (control * frame)

  let string_of_control = function
    | Exp exp -> "Exp(" ^ (string_of_exp exp) ^ ")"
    | Prop prop -> "Prop(" ^ (string_of_prop prop) ^ ")"
    | Val v -> "Val(" ^ (AValue.to_string v) ^ ")"
    | PropVal v -> "PropVal"
    | Frame (exp, f) -> "Frame(" ^ (string_of_frame f) ^ ")"

  type state = control * Env.t * ValueStore.t * ObjectStore.t

  let string_of_state (control, _, _, _) = string_of_control control

  let compare_state (state, env, vstore, ostore) (state', env', vstore', ostore') =
    order_concat [lazy (Pervasives.compare state state');
                  lazy (Env.compare env env');
                  lazy (ValueStore.compare vstore vstore');
                  lazy (ObjectStore.compare ostore ostore')]

  (* TODO: add stack summary *)
  type conf = state

  let string_of_conf = string_of_state

  let compare_conf = compare_state

  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged

  let compare_stack_change g1 g2 = match (g1, g2) with
    | StackPop f1, StackPop f2 -> compare_frame f1 f2
    | StackPush f1, StackPush f2 -> compare_frame f1 f2
    | StackUnchanged, StackUnchanged -> 0
    | StackPop _, _ -> 1
    | _, StackPop _ -> -1
    | StackPush _, StackUnchanged -> 1
    | StackUnchanged, _ -> -1

  let string_of_stack_change = function
    | StackPush f -> "+" ^ (string_of_frame f)
    | StackPop f -> "-" ^ (string_of_frame f)
    | StackUnchanged -> "e"

  module FrameOrdering = struct
    type t = frame
    let compare = compare_frame
  end

  module ConfOrdering = struct
    type t = conf
    let compare = compare_conf
  end

  module StackChangeOrdering = struct
    type t = stack_change
    let compare = compare_stack_change
  end

  (* TODO: put that somewhere else? *)
  let alloc_val _ state = match state with
    | (_, _, vstore, _) -> Address.alloc (ValueStore.size vstore + 1)

  let alloc_obj _ state = match state with
    | (_, _, _, ostore) -> Address.alloc (ObjectStore.size ostore + 1)

  let inject (exp : S.exp) = (Exp exp, Env.empty, ValueStore.empty, ObjectStore.empty)

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
  let step_exp exp ((_, env, vstore, ostore) as state) = match exp with
    | S.Null _ -> unch (Val `Null, env, vstore, ostore)
    | S.Undefined _ -> unch (Val `Undef, env, vstore, ostore)
    | S.String (_, s) -> unch (Val (`Str s), env, vstore, ostore)
    | S.Num (_, n) -> unch (Val (`Num n), env, vstore, ostore)
    | S.True _ -> unch (Val `True, env, vstore, ostore)
    | S.False _ -> unch (Val `False, env, vstore, ostore)
    | S.Id (_, id) -> unch (Val (ValueStore.lookup (Env.lookup id env) vstore), env,
                            vstore, ostore)
    | S.Lambda (_, args, body) ->
      let free = S.free_vars body in
      let env' = Env.keep free env in
      unch (Val (`Clos (env', args, body)), env, vstore, ostore)
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
          let a = alloc_obj obj state in
          let ostore' = ObjectStore.join a (`Obj obj) ostore in
          unch (Val (`Obj a), env, vstore, ostore')
        | [], (prop, exp)::props ->
          push (ObjectProps (prop, obj, props, env))
            (Prop exp, env, vstore, ostore)
        | (attr, exp)::attrs, props ->
          push (ObjectAttrs (attr, obj, attrs, props, env))
            (Exp exp, env, vstore, ostore)
      end
    | S.Let (_, id, exp, body) ->
      push (Let (id, body, env)) (Exp exp, env, vstore, ostore)
    | S.Seq (_, left, right) ->
      push (Seq (right, env)) (Exp left, env, vstore, ostore)
    | S.App (_, f, args) ->
      print_endline ("------ apply " ^ (string_of_exp f));
      push (AppFun (args, env)) (Exp f, env, vstore, ostore)
    | S.Op1 (_, op, arg) ->
      push (Op1App (op, env)) (Exp arg, env, vstore, ostore)
    | S.Op2 (_, op, arg1, arg2) ->
      push (Op2Arg (op, arg2, env)) (Exp arg1, env, vstore, ostore)
    | S.If (_, pred, cons, alt) ->
      push (If (cons, alt, env)) (Exp pred, env, vstore, ostore)
    | S.GetField (_, obj, field, body) ->
      push (GetFieldObj (field, body, env)) (Exp obj, env, vstore, ostore)
    | S.SetField (_, obj, field, newval, body) ->
      push (SetFieldObj (field, newval, body, env)) (Exp obj, env, vstore, ostore)
    | S.GetAttr (_, pattr, obj, field) ->
      push (GetAttrObj (pattr, field, env)) (Exp obj, env, vstore, ostore)
    | _ -> failwith ("Not yet handled " ^ (string_of_exp exp))

  let rec apply_fun f args ((_, _, vstore, ostore) as state) = match f with
    | `Clos (env', args', body) ->
      if (List.length args) != (List.length args') then
        failwith "Arity mismatch"
      else
        let alloc_arg v name (vstore, env) =
          let a = alloc_val v state in
          (ValueStore.join a v vstore,
           Env.extend name a env) in
        let (vstore', env') =
          BatList.fold_right2 alloc_arg args args' (vstore, env') in
        (body, env', vstore', ostore)
    | `ClosT -> failwith "Closure too abstracted" (* TODO: what to do in this case? *)
    | `Obj a -> begin match ObjectStore.lookup a ostore with
        | `Obj ({ O.code = `Clos f; _ }, _) ->
          let (exp, env, vstore, ostore) = apply_fun (`Clos f) args state in
          (exp, env, vstore, ostore)
        | _ -> failwith "Applied object without code attribute"
      end
    | _ -> failwith "Applied non-function"

  let apply_frame v frame ((control, env, vstore, ostore) as state) _ = match frame with
    | Let (id, body, env') ->
      let a = alloc_val id state in
      let env'' = Env.extend id a env' in
      let vstore' = ValueStore.join a v vstore in
      (Exp body, env'', vstore', ostore)
    (* ObjectAttrs of string * O.t * (string * S.exp) list * (string * prop) list * Env.t *)
    | ObjectAttrs (name, obj, [], [], env') ->
      let obj' = O.set_attr obj name v in
      let a = alloc_obj obj' state in
      let ostore' = ObjectStore.join a (`Obj obj') ostore in
      (Val (`Obj a), env', vstore, ostore')
    | ObjectAttrs (name, obj, [], (name', prop) :: props, env') ->
      let obj' = O.set_attr obj name v in
      (Frame (Prop prop, ObjectProps (name', obj', props, env')), env', vstore, ostore)
    | ObjectAttrs (name, obj, (name', attr) :: attrs, props, env') ->
      let obj' = O.set_attr obj name v in
      (Frame (Exp attr, ObjectAttrs (name', obj', attrs, props, env')), env', vstore, ostore)
    (* PropData of (O.data * AValue.t * AValue.t) * Env.t *)
    | PropData ((data, enum, config), env') ->
      (PropVal (O.Data ({data with O.value = v}, enum, config)), env', vstore, ostore)
    (* PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t *)
    | PropAccessor (None, (accessor, enum, config), env') ->
      (PropVal (O.Accessor ({accessor with O.setter = v}, enum, config)), env', vstore, ostore)
    | PropAccessor (Some exp, (accessor, enum, config), env') ->
      (Frame (Exp exp, (PropAccessor (None, ({accessor with O.getter = v}, enum, config), env'))),
       env', vstore, ostore)
    | Seq (exp, env') ->
      (Exp exp, env', vstore, ostore)
    | AppFun ([], env') ->
      let (exp, env, vstore, ostore) = apply_fun v [] state in
      (Exp exp, env, vstore, ostore)
    | AppFun (arg :: args, env') ->
      (Frame (Exp arg, (AppArgs (v, [], args, env'))), env', vstore, ostore)
    | AppArgs (f, vals, [], env') ->
      let (exp, env, vstore, ostore) = apply_fun f (BatList.rev (v :: vals)) state in
      (Exp exp, env, vstore, ostore)
    | AppArgs (f, vals, arg :: args, env') ->
      (Frame (Exp arg, (AppArgs (f, v :: vals, args, env'))), env', vstore, ostore)
    | Op1App (op, env') ->
      (Val (D.op1 ostore op v), env', vstore, ostore)
    | Op2Arg (op, arg2, env') ->
      (Frame (Exp arg2, (Op2App (op, v, env'))), env', vstore, ostore)
    | Op2App (op, arg1, env') ->
      (Val (D.op2 ostore op arg1 v), env', vstore, ostore)
    | If (cons, alt, env') -> begin match v with
        | `True -> (Exp cons, env', vstore, ostore)
        | `BoolT | `Top -> failwith "TODO: two if possibilities"
        | _ -> (Exp alt, env', vstore, ostore)
      end
    | GetFieldObj (field, body, env') ->
      (Frame (Exp field, GetFieldField (v, body, env')), env', vstore, ostore)
    | GetFieldField (obj, body, env') ->
      (Frame (Exp body, GetFieldBody (obj, v, env')), env', vstore, ostore)
    | GetFieldBody (obj, field, env') ->
      let body = v in
      begin match obj, field with
        | `Obj a, `Str s ->
          begin match get_prop (`Obj a) s ostore with
            | Some (O.Data ({O.value = v; _}, _, _)) -> (Val v, env', vstore, ostore)
            | Some (O.Accessor ({O.getter = g; _}, _, _)) ->
              let (body, env'', vstore', ostore) = apply_fun g [obj; body] state in
              (Frame (Exp body, RestoreEnv env'), env'', vstore', ostore)
            | None -> (Val `Undef, env', vstore, ostore)
          end
        | `Obj _, `StrT -> failwith "TODO"
        | `ObjT, _ -> failwith "TODO"
        | _ -> failwith "TODO"
      end
    | SetFieldObj (field, newval, body, env') ->
      (Frame (Exp field, SetFieldField (v, newval, body, env')), env', vstore, ostore)
    | SetFieldField (obj, newval, body, env') ->
      (Frame (Exp newval, SetFieldNewval (obj, v, body, env')), env', vstore, ostore)
    | SetFieldNewval (obj, field, body, env') ->
      (Frame (Exp body, SetFieldArgs (obj, field, v, env')), env', vstore, ostore)
    | SetFieldArgs (obj, field, newval, env') ->
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
                  (Val newval, env', vstore, ostore')
                | Some (O.Data _)
                | Some (O.Accessor ({O.setter = `Undef; _}, _, _)) ->
                  failwith "unwritable" (* TODO: throw *)
                | Some (O.Accessor ({O.setter = setter; _}, _, _)) ->
                  let (exp, env'', vstore', ostore') =
                    apply_fun setter [obj; body] state in
                  (Frame (Exp exp, RestoreEnv env'), env'', vstore', ostore')
                | None ->
                  match extensible with
                  | `True ->
                    let newobj = O.set_prop (attrs, props) s
                        (O.Data ({O.value = newval; O.writable = `True},
                                 `True, `True)) in
                    let ostore' = ObjectStore.set a (`Obj newobj) ostore in
                    (Val newval, env', vstore, ostore')
                  | `False ->
                    (Val `Undef, env, vstore, ostore)
                  | _ -> failwith "TODO"
              end
            | `ObjT -> failwith "TODO"
          end
        | _ -> failwith "update field"
      end
    | GetAttrObj (pattr, field, env') ->
      (Frame (Exp field, GetAttrField (pattr, v, env')), env', vstore, ostore)
    | GetAttrField (pattr, obj, env') ->
      let field = v in
      begin match obj with
        | `Obj a ->
          begin match ObjectStore.lookup a ostore with
            | `Obj o -> let attr = O.get_attr o pattr field in
              (Val attr, env', vstore, ostore)
            | `ObjT -> failwith "TODO"
          end
        | _ -> failwith "TODO"
      end
    | _ -> failwith "Not implemented"

  let apply_frame_prop v frame ((_, env, vstore, ostore) as state) _ = match frame with
    (* ObjectProps of string * O.t * (string * prop) list * Env.t *)
    | ObjectProps (name, obj, [], env') ->
      let obj' = O.set_prop obj name v in
      let a = alloc_obj obj' state in
      let ostore' = ObjectStore.join a (`Obj obj') ostore in
      (Val (`Obj a), env', vstore, ostore')
    | ObjectProps (name, obj, (name', prop) :: props, env') ->
      let obj' = O.set_prop obj name v in
      (Frame (Prop prop, ObjectProps (name', obj', props, env')), env', vstore, ostore)
    | _ -> failwith "Not implemented"

  let step_prop p (_, env, vstore, ostore) = match p with
    | S.Data ({ S.value = v; S.writable = w }, enum, config) ->
      push (PropData (({ O.value = `Undef; O.writable = AValue.bool w },
                       AValue.bool enum, AValue.bool config),
                      env))
        (Exp v, env, vstore, ostore)
    | S.Accessor ({ S.getter = g; S.setter = s }, enum, config) ->
      push (PropAccessor (Some g, ({ O.getter = `Undef; O.setter = `Undef },
                                   AValue.bool enum, AValue.bool config),
                          env))
        (Exp g, env, vstore, ostore)

  let step ((control, env, vstore, ostore) as state) frames = match control with
    | Exp e -> step_exp e state
    | Prop p -> step_prop p state
    | Val v ->
      List.map
        (fun (state', frame) ->
           (StackPop frame, apply_frame v frame state state'))
        frames
    | Frame (control', frame) ->
      [(StackPush frame, (control', env, vstore, ostore))]
    | PropVal prop ->
      List.map
        (fun (state', frame) ->
           (StackPop frame, apply_frame_prop prop frame state state'))
        frames


end