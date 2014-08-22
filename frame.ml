open Prelude
open Shared
open Env
open Lattice

module D = Delta
module S = Ljs_syntax
module O = Obj_val

(* a StackObj is an object that lives on the stack, it avoids allocating
   too much objects and allows to use identifiers for the objects' addresses
   (which is not possible on anonymous objects) *)
type stack_value = [ `StackObj of O.t ]

type value = [ AValue.t | stack_value ]

let compare_value (x : value) (y : value) = match x, y with
  | (#AValue.t as v), (#AValue.t as v') -> AValue.compare v v'
  | #AValue.t, _ -> 1
  | _, #AValue.t -> -1
  | `StackObj o, `StackObj o' -> O.compare o o'

type t =
  (* {let (id = exp) body}, where the exp in the frame is body *)
  | Let of id * S.exp * Env.t
  (* {rec (id = exp) body} *)
  | Rec of id * Address.t * S.exp * Env.t
  (* {[field1: val1, ...]} *)
  | ObjectAttrs of Pos.t * string * O.t * (string * S.exp) list * (string * S.prop) list * Env.t
  | ObjectProps of string * O.t * (string * S.prop) list * Env.t
  | PropData of (O.data * AValue.t * AValue.t) * Env.t
  | PropAccessor of S.exp option * (O.accessor * AValue.t * AValue.t) * Env.t
  (* left; right *)
  | Seq of S.exp * Env.t
  (* f(arg1, ...) *)
  | AppFun of S.exp list * Env.t
  | AppArgs of value * value list * S.exp list * Env.t
  (* op arg *)
  | Op1App of string * Env.t
  (* arg1 op arg2 *)
  | Op2Arg of string * S.exp * Env.t
  | Op2App of string * value * Env.t
  (* if pred then cons else alt *)
  | If of S.exp * S.exp * Env.t
  (* obj[field] *)
  | GetFieldObj of S.exp * S.exp * Env.t
  | GetFieldField of value * S.exp * Env.t
  | GetFieldBody of value * value * Env.t
  (* obj[field] = val *)
  | SetFieldObj of S.exp * S.exp * S.exp * Env.t
  | SetFieldField of value * S.exp * S.exp * Env.t
  | SetFieldNewval of value * value * S.exp * Env.t
  | SetFieldArgs of value * value * value * Env.t
  (* syntax? *)
  | GetAttrObj of S.pattr * S.exp * Env.t
  | GetAttrField of S.pattr * value * Env.t
  (* syntax? *)
  | SetAttrObj of S.pattr * S.exp * S.exp * Env.t
  | SetAttrField of S.pattr * value * S.exp * Env.t
  | SetAttrNewval of S.pattr * value * value * Env.t
  (* syntax? *)
  | GetObjAttr of S.oattr * Env.t
  (* syntax? *)
  | OwnFieldNames of Env.t
  (* frame to restore the contained environment *)
  | RestoreEnv of Env.t

let env_of_frame = function
  | Let (_, _, env)
  | ObjectAttrs (_, _, _, _, _, env)
  | ObjectProps (_, _, _, env)
  | PropAccessor (_, _, env)
  | Rec (_, _, _, env)
  | AppFun (_, env)
  | AppArgs (_, _, _, env)
  | SetFieldObj (_, _, _, env)
  | If (_, _, env)
  | GetFieldObj (_, _, env)
  | SetFieldField (_, _, _, env)
  | SetAttrObj (_, _, _, env)
  | Op2Arg (_, _, env)
  | Seq (_, env)
  | GetFieldField (_, _, env)
  | SetFieldNewval (_, _, _, env)
  | GetAttrObj (_, _, env)
  | SetAttrField (_, _, _, env)
  | PropData (_, env)
  | Op1App (_, env)
  | Op2App (_, _, env)
  | GetFieldBody (_, _, env)
  | SetFieldArgs (_, _, _, env)
  | GetAttrField (_, _, env)
  | SetAttrNewval (_, _, _, env)
  | GetObjAttr (_, env)
  | OwnFieldNames env
  | RestoreEnv env ->
    env

let addresses_of_vars (vars : IdSet.t) (env : Env.t) : AddressSet.t =
  IdSet.fold (fun v acc ->
      if Env.contains v env then
        AddressSet.add (Env.lookup v env) acc
      else begin
        (* TODO: this should only happen for actual unbound variables.
           Shouldn't they be reported before doing the interpretation? *)
        print_endline ("Ignoring variable not found in env: " ^ v);
        acc
      end) vars AddressSet.empty

let free_vars frame =
  let fv_list f = List.fold_left (fun acc x ->
      IdSet.union acc (f x)) IdSet.empty in
  let fv_attr (_, exp) = S.free_vars exp in
  let fv_prop = function
    | (_, S.Data ({S.value = v; _}, _, _)) -> S.free_vars v
    | (_, S.Accessor ({S.getter = g; S.setter = s}, _, _)) ->
       IdSet.union (S.free_vars g) (S.free_vars s) in
  let fv_attrs = fv_list fv_attr in
  let fv_props = fv_list fv_prop in
  match frame with
  (* special cases *)
  | Let (id, exp, _) -> IdSet.remove id (S.free_vars exp)
  | ObjectAttrs (_, _, _, attrs, props, _) ->
    (IdSet.union (fv_attrs attrs) (fv_props props))
  | ObjectProps (_, _, props, _) -> fv_props props

  (* List of exps *)
  | AppFun (args, _)
  | AppArgs (_, _, args, _) ->
    fv_list S.free_vars args

  (* Three exps *)
  | SetFieldObj (exp1, exp2, exp3, _) ->
    fv_list S.free_vars [exp1; exp2; exp3]

  (* Two exps *)
  | If (exp1, exp2, _)
  | GetFieldObj (exp1, exp2, _)
  | SetFieldField (_, exp1, exp2, _)
  | SetAttrObj (_, exp1, exp2, _) ->
    fv_list S.free_vars [exp1; exp2]

  (* One exp *)
  | Op2Arg (_, exp, _)
  | Seq (exp, _)
  | GetFieldField (_, exp, _)
  | SetFieldNewval (_, _, exp, _)
  | GetAttrObj (_, exp, _)
  | SetAttrField (_, _, exp, _)
  | PropAccessor (Some exp, _, _)
  | Rec (_, _, exp, _) ->
    S.free_vars exp

  (* No exp *)
  | PropData _
  | PropAccessor (None, _, _)
  | Op1App _
  | Op2App _
  | GetFieldBody _
  | SetFieldArgs _
  | GetAttrField _
  | SetAttrNewval _
  | GetObjAttr _
  | OwnFieldNames _
  | RestoreEnv _ -> IdSet.empty

let touched_addresses = function
  | Rec (_, a, _, _) -> AddressSet.singleton a
  | _ -> AddressSet.empty

(* TODO: some of those functions should probably go elsewhere *)
let vals_of_prop : O.prop -> value list = function
  | O.Data ({O.value = v; O.writable = w}, enum, config) ->
    [(v :> value); (w :> value); (enum :> value); (config :> value)]
  | O.Accessor ({O.getter = g; O.setter = s}, enum, config) ->
    [(g :> value); (s :> value); (enum :> value); (config :> value)]

let rec addresses_of_vals (l : value list) =
  let rec aux acc = function
    | [] -> acc
    | h :: t -> begin match h with
        | `Clos (env, _, _) -> aux (AddressSet.union (Env.range env) acc) t
        | `ClosT -> failwith "Closure was too abstracted"
        | `Obj a -> aux (AddressSet.add a acc) t
        | `ObjT -> failwith "Object was too abstracted"
        | `StackObj o -> addresses_of_obj o
        | _ -> aux acc t
      end in
  aux AddressSet.empty l
and addresses_of_obj ({O.code = code; O.proto = proto; O.primval = primval;
                       O.klass = klass; O.extensible = extensible}, props) =
  IdMap.fold (fun _ prop -> AddressSet.union (addresses_of_vals (vals_of_prop prop)))
    props (addresses_of_vals
             [(code :> value); (proto :> value); (primval :> value);
              (klass :> value); (extensible :> value)])

let touched_addresses_from_values frame =
  match frame with
  (* Special cases *)
  | AppArgs (f, args, _, _) ->
    addresses_of_vals (f :: args)
  | PropData (({O.value = v; O.writable = w}, enum, config), _) ->
    addresses_of_vals [(v :> value); (w :> value);
                       (enum :> value); (config :> value)]
  | PropAccessor (_, ({O.getter = g; setter = s}, enum, config), _) ->
    addresses_of_vals [(g :> value); (s :> value);
                       (enum :> value); (config :> value)]

  (* Object *)
  | ObjectAttrs (_, _, o, _, _, _)
  | ObjectProps (_, o, _, _) ->
    addresses_of_obj o

  (* No value *)
  | Let (_, _, _)
  | Rec (_, _, _, _)
  | Seq (_, _)
  | AppFun (_, _)
  | Op1App (_, _)
  | Op2Arg (_, _, _)
  | If (_, _, _)
  | GetFieldObj (_, _, _)
  | SetFieldObj (_, _, _, _)
  | GetAttrObj (_, _, _)
  | SetAttrObj (_, _, _, _)
  | GetObjAttr (_, _)
  | OwnFieldNames _
  | RestoreEnv _ ->
    addresses_of_vals []

  (* One value *)
  | Op2App (_, v, _)
  | SetFieldField (v, _, _, _)
  | GetAttrField (_, v, _)
  | SetAttrField (_, v, _, _) ->
    addresses_of_vals [(v :> value)]

  | GetFieldField (v, _, _) ->
    addresses_of_vals [v]

  (* Two values *)
  | SetFieldNewval (v1, v2, _, _)
  | SetAttrNewval (_, v1, v2, _) ->
    addresses_of_vals [(v1 :> value); (v2 :> value)]

  | GetFieldBody (v1, v2, _) ->
    addresses_of_vals [v1; v2]


  (* Three values *)
  | SetFieldArgs (v1, v2, v3, _) ->
    addresses_of_vals [(v1 :> value); (v2 :> value); (v3 :> value)]

let touch frame =
  AddressSet.union
    (AddressSet.union (addresses_of_vars (free_vars frame) (env_of_frame frame))
       (touched_addresses frame))
    (touched_addresses_from_values frame)

(* TODO: addrs: Rec (_, a, _, _) -> a *)
(* TODO: vals: AppArg (v, _, _, _) -> v = `Clos (...) -> S.free_vars *)


let to_string = function
  | Let (id, _, _) -> "Let-" ^ id
  | Rec (id, _, _, _) -> "Rec-" ^ id
  | ObjectProps (name, _, _, _) -> "ObjectProps-" ^ name
  | ObjectAttrs (_, name, _, _, _,  _) -> "ObjectAttrs-" ^ name
  | PropData _ -> "PropData"
  | PropAccessor (Some _, _, _) -> "PropAccessor-Get"
  | PropAccessor (None, _, _) -> "PropAccessor-Set"
  | Seq _ -> "Seq"
  | AppFun _ -> "AppFun"
  | AppArgs _ -> "AppArgs"
  | Op1App (op, _) -> "Op1App-" ^ op
  | Op2Arg (op, _, _) -> "Op2Arg-" ^ op
  | Op2App (op, _, _) -> "Op2App-" ^ op
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
  | SetAttrObj _ -> "SetAttrObj"
  | SetAttrField _ -> "SetAttrField"
  | SetAttrNewval _ -> "SetAttrNewval"
  | GetObjAttr _ -> "GetObjAttr"
  | OwnFieldNames _ -> "OwnFieldNames"

(* TODO: use ppx_deriving when 4.02 is out *)
let compare f f' = match f, f' with
  | Let (id, exp, env), Let (id', exp', env') ->
    order_concat [lazy (Pervasives.compare id id');
                  lazy (Pervasives.compare exp exp');
                  lazy (Env.compare env env')]
  | Let _, _ -> 1
  | _, Let _ -> -1
  | Rec (id, a, exp, env), Rec (id', a', exp', env') ->
    order_concat [lazy (Pervasives.compare id id');
                  lazy (Address.compare a a');
                  lazy (Pervasives.compare exp exp');
                  lazy (Env.compare env env')]
  | Rec _, _ -> 1
  | _, Rec _ -> -1
  | ObjectAttrs (p, attr, obj, attrs, props, env),
    ObjectAttrs (p', attr', obj', attrs', props', env') ->
    order_concat [lazy (Pos.compare p p');
                  lazy (Pervasives.compare attr attr');
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
    order_concat [lazy (compare_value f f');
                  lazy (compare_list compare_value vals vals');
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
                  lazy (compare_value arg1 arg1');
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
    order_concat [lazy (compare_value obj obj');
                  lazy (Pervasives.compare body body');
                  lazy (Env.compare env env')]
  | GetFieldField _, _ -> 1
  | _, GetFieldField _ -> -1
  | GetFieldBody (obj, field, env), GetFieldBody (obj', field', env') ->
    order_concat [lazy (compare_value obj obj');
                  lazy (compare_value field field');
                  lazy (Env.compare env env')]
  | GetFieldBody _, _ -> 1
  | _, GetFieldBody _ -> -1
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
    order_concat [lazy (compare_value obj obj');
                  lazy (Pervasives.compare newval newval');
                  lazy (Pervasives.compare body body');
                  lazy (Env.compare env env')]
  | SetFieldField _, _ -> 1
  | _, SetFieldField _ -> -1
  | SetFieldNewval (obj, field, body, env),
    SetFieldNewval (obj', field', body', env') ->
    order_concat [lazy (compare_value obj obj');
                  lazy (compare_value field field');
                  lazy (Pervasives.compare body body');
                  lazy (Env.compare env env')]
  | SetFieldNewval _, _ -> 1
  | _, SetFieldNewval _ -> -1
  | SetFieldArgs (obj, field, newval, env),
    SetFieldArgs (obj', field', newval', env') ->
    order_concat [lazy (compare_value obj obj');
                  lazy (compare_value field field');
                  lazy (compare_value newval newval');
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
                  lazy (compare_value obj obj');
                  lazy (Env.compare env env')]
  | GetAttrField _, _ -> 1
  | _, GetAttrField _ -> -1
  | SetAttrObj (pattr, field, newval, env),
    SetAttrObj (pattr', field', newval', env') ->
    order_concat [lazy (Pervasives.compare pattr pattr');
                  lazy (Pervasives.compare field field');
                  lazy (Pervasives.compare newval newval');
                  lazy (Env.compare env env')]
  | SetAttrObj _, _ -> 1
  | _, SetAttrObj _ -> -1
  | SetAttrField (pattr, obj, newval, env),
    SetAttrField (pattr', obj', newval', env') ->
    order_concat [lazy (Pervasives.compare pattr pattr');
                  lazy (compare_value obj obj');
                  lazy (Pervasives.compare newval newval');
                  lazy (Env.compare env env')]
  | SetAttrField _, _ -> 1
  | _, SetAttrField _ -> -1
  | SetAttrNewval (pattr, obj, field, env),
    SetAttrNewval (pattr', obj', field', env') ->
    order_concat [lazy (Pervasives.compare pattr pattr');
                  lazy (compare_value obj obj');
                  lazy (compare_value field field');
                  lazy (Env.compare env env')]
  | SetAttrNewval _, _ -> 1
  | _, SetAttrNewval _ -> -1
  | GetObjAttr (oattr, env), GetObjAttr (oattr', env') ->
    order_concat [lazy (Pervasives.compare oattr oattr');
                  lazy (Env.compare env env')]
  | GetObjAttr _, _ -> 1
  | _, GetObjAttr _ -> -1
  | OwnFieldNames env, OwnFieldNames env' ->
    Env.compare env env'
  | OwnFieldNames _, _ -> 1
  | _, OwnFieldNames _ -> -1

  | RestoreEnv env, RestoreEnv env' ->
    Env.compare env env'
