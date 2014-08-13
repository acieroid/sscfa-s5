open Prelude
open Shared
open Env
open Lattice

module D = Delta
module S = Ljs_syntax
module O = Obj_val

type t =
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
  (* syntax? *)
  | SetAttrObj of S.pattr * S.exp * S.exp * Env.t
  | SetAttrField of S.pattr * AValue.t * S.exp * Env.t
  | SetAttrNewval of S.pattr * AValue.t * AValue.t * Env.t

let touch = function
  | _ -> failwith "Not yet implemented: touch"

let to_string = function
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
  | SetAttrObj _ -> "SetAttrObj"
  | SetAttrField _ -> "SetAttrField"
  | SetAttrNewval _ -> "SetAttrNewval"

(* TODO: use ppx_deriving when 4.02 is out *)
let compare f f' = match f, f' with
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
                  lazy (AValue.compare obj obj');
                  lazy (Pervasives.compare newval newval');
                  lazy (Env.compare env env')]
  | SetAttrNewval (pattr, obj, field, env),
    SetAttrNewval (pattr', obj', field', env') ->
    order_concat [lazy (Pervasives.compare pattr pattr');
                  lazy (AValue.compare obj obj');
                  lazy (AValue.compare field field');
                  lazy (Env.compare env env')]
  | SetAttrNewval _, _ -> 1
  | _, SetAttrNewval _ -> -1
