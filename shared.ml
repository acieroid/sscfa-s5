open Prelude
open Ljs_syntax

let debug = ref false
let restricted_gc = ref false

(* Some functions to simplify the writing of comparison functions *)
let order_comp x y =
  if x = 0 then y else x

let order_concat l =
  let rec aux last = function
    | [] -> last
    | (h::t) ->
      if last <> 0 then last else aux (order_comp last (Lazy.force h)) t
  in aux 0 l

let compare_list cmp l1 l2 =
  let l = Pervasives.compare (BatList.length l1) (BatList.length l2) in
  if l == 0 then
    order_concat (BatList.map
                    (fun (el1, el2) -> lazy (cmp el1 el2))
                    (BatList.combine l1 l2))
  else
    l

let string_of_list l s_o_elt =
  if List.length l > 0 then
    let elts = List.fold_right (fun elt a -> (s_o_elt elt)^", "^a) l "" in
    "["^(String.sub elts 0 ((String.length elts)-2))^"]"
  else "[]"

let string_of_map fold k v m =
  "{" ^ (fold (fun k' v' a -> (k k')^" --> "^(v v')^"\n"^a) m " }")

module StringSet = BatSet.Make(struct
    type t = string
    let compare = Pervasives.compare
  end)

module type Time_signature =
sig
  type t
  type arg
  val initial : t
  val compare : t -> t -> int
  val to_string : t -> string
  val tick : arg -> t -> t
end

module type KCFA_k = sig val k : int end

module type KCFA_arg = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
end

module KCFABased =
  functor (Arg : KCFA_arg) -> functor (K : KCFA_k) ->
  struct
    type arg = Arg.t
    type t = Arg.t list
    let initial = []
    let compare = compare_list Arg.compare
    let to_string t = string_of_list t Arg.to_string
    let tick x t =
      print_endline ("\027[34mtick " ^ (Arg.to_string x) ^ "\027[0m");
      BatList.take K.k (x :: t)
  end

type 'a addr_kind = [ `ObjAddress of 'a | `VarAddress of 'a ]

module type Address_signature =
  sig
    type a
    type t = a addr_kind
    type time
    val compare : t -> t -> int
    val is_reclaimable : t -> bool
    val to_string : t -> string
    val alloc_obj : string -> time -> t
    val alloc_var : string -> time -> t
  end

(* S5 uses Store.Loc module (util/store.ml) *)
module MakeAddress =
  functor (T : Time_signature) ->
struct
  type time = T.t
  type a = (string * T.t)
  type t = a addr_kind
  let compare x y = match x, y with
    | `ObjAddress (id, t), `ObjAddress (id', t')
    | `VarAddress (id, t), `VarAddress (id', t') ->
      order_comp (Pervasives.compare id id') (T.compare t t')
    | `ObjAddress _, `VarAddress _ -> 1
    | `VarAddress _, `ObjAddress _ -> -1
  let is_reclaimable a =
    if !restricted_gc then
      match a with
      (* %or is a special variable frequetly present in desugared S5 code, but
         it is *not* used to denote a global identifier *)
      | `VarAddress ("%or", _) -> true
      (* variables starting with % or # are global and should not be GCed, even
         if they are not reachable, as we could be loading an environment where
         they are not used, but they'll be used in a program using this
         environment *)
      | `ObjAddress (id, _)
      | `VarAddress (id, _) ->
        not (BatString.starts_with id "%" || BatString.starts_with id "#")
    else
      true
  let to_string = function
    | `ObjAddress (id, t) -> "@obj-" ^ id ^ "-" ^ (T.to_string t)
    | `VarAddress (id, t) -> "@var-" ^ id ^ "-" ^ (T.to_string t)
  let alloc_obj id t =
    print_endline ("\027[33malloc_obj(" ^ id ^ ", " ^ (T.to_string t) ^ ")\027[0m");
    `ObjAddress (id, t)
  let alloc_var id t =
    print_endline ("\027[33malloc_var(" ^ id ^ ", " ^ (T.to_string t) ^ ")\027[0m");
    `VarAddress (id, t)
end

module ParameterSensitive =
  functor (A : Address_signature) ->
  struct
    (* We need to duplicate a bit of lattice.ml here, it should be better to put
       this in another file. We cannot use the Lattice module here as it depends
       on this module for addresses *)
    type v = [ `True | `False | `BoolT
             | `Obj of A.t | `ObjT
             | `Str of string | `StrT
             | `Num of float | `NumT
             | `Null | `Undef
             | `Top | `Bot ]

    let string_of_v : v -> string = function
      | `True -> "true"
      | `False -> "false"
      | `BoolT -> "boolT"
      | `Obj a -> "obj" ^ (A.to_string a)
      | `ObjT -> "objT"
      | `Num n -> string_of_float n
      | `NumT -> "numT"
      | `Str s -> "'" ^ s ^ "'"
      | `StrT -> "strT"
      | `Null -> "null"
      | `Undef -> "undef"
      | `Top -> "T"
      | `Bot -> "_|_"

    let compare_v x y = match x, y with
      | `True, `True | `False, `False | `BoolT, `BoolT
      | `ObjT, `ObjT | `StrT, `StrT | `NumT, `NumT
      | `Null, `Null | `Undef, `Undef
      | `Top, `Top | `Bot, `Bot -> 0
      | `Obj a, `Obj a' -> A.compare a a'
      | `Str s, `Str s' -> Pervasives.compare s s'
      | `Num n, `Num n' -> Pervasives.compare n n'
      | `True, _ -> 1 | _, `True -> -1
      | `False, _ -> 1 | _, `False -> -1
      | `BoolT, _ -> 1 | _, `BoolT -> -1
      | `Obj _, _ -> 1 | _, `Obj _ -> -1
      | `ObjT, _ -> 1 | _, `ObjT -> -1
      | `Str _, _ -> 1 | _, `Str _ -> -1
      | `StrT, _ -> 1 | _, `StrT -> -1
      | `Num _, _ -> 1 | _, `Num _ -> -1
      | `NumT, _ -> 1 | _, `NumT -> -1
      | `Null, _ -> 1 | _, `Null -> -1
      | `Undef, _ -> 1 | _, `Undef -> -1
      | `Top, _ -> 1 | _, `Top -> -1

    type t = Pos.t * (string * v) list

    let compare ((p, l) : t) ((p', l') : t) : int =
      let cmp (n, v) (n', v') =
        order_concat [lazy (Pervasives.compare n n');
                      lazy (compare_v v v')] in
      order_concat [lazy (Pos.compare p p');
                    lazy (compare_list cmp l l')]

    let to_string ((p, l) : t) =
      string_of_list l (fun (n, v) -> n ^ ": " ^ (string_of_v v))

  end

module K1 = struct let k = 2 end

(* This is ugly as fuck, but it does the trick in a type-safe way *)
module rec PSAddress :
sig
  include Address_signature with type time = PSTime.t
end
  = MakeAddress(PSTime)
and PSTime :
sig
  type v = [ `True | `False | `BoolT
           | `Obj of PSAddress.t | `ObjT
           | `Str of string | `StrT
           | `Num of float | `NumT
           | `Null | `Undef
           | `Top | `Bot ]

  include Time_signature with type arg =  Pos.t * (string * v) list
end
= struct
  include KCFABased(ParameterSensitive(PSAddress))(K1)
  type v = [ `True | `False | `BoolT
           | `Obj of PSAddress.t | `ObjT
           | `Str of string | `StrT
           | `Num of float | `NumT
           | `Null | `Undef
           | `Top | `Bot ]
end


module KPos = struct include Pos let to_string = string_of_pos end
module K1Time = KCFABased(KPos)(K1)
module K1Address = MakeAddress(K1Time)

module Time = K1Time
module Address = K1Address
module AddressSet = BatSet.Make(Address)

let rec string_of_exp exp = match exp with
  | Null p -> "null"
  | Undefined _ -> "undef"
  | String (_, v) -> "'"^v^"'"
  | Num (_, f) -> (string_of_float f)
  | True _ -> "true"
  | False _ -> "false"
  | Id (_, x) -> x
  | Object (_, _, _) -> "object"
  | GetAttr (_, _, _, _) -> "getattr"
  | SetAttr (_, _, _, _, _) -> "setattr"
  | GetObjAttr (_, _, _) -> "getobjattr"
  | SetObjAttr (_, _, _, _) -> "setobjattr"
  | GetField (_, _, _, _) -> "getfield"
  | SetField (_, _, _, _, _) -> "setfield"
  | DeleteField (_, _, _) -> "deletefield"
  | OwnFieldNames (_, _) -> "ownfieldnames"
  | SetBang (_, _, _) -> "setbang"
  | Op1 (_, s, e) -> "op1(" ^ s ^ ", " ^ (string_of_exp e) ^ ")"
  | Op2 (_, s, e1, e2) -> "op2(" ^ s ^ ", " ^ (string_of_exp e1) ^ ", " ^ (string_of_exp e2) ^ ")"
  | If (_, _, _, _) -> "if"
  | App (_, _, _) -> "app"
  | Seq (_, _, _) -> "seq"
  | Let (_, x, e, _) ->
    "let "^x^" = "^(string_of_exp e)^""
  | Rec (_, x, e1, e2) ->
    "rec("^x^", "^(string_of_exp e1)^", "^(string_of_exp e2)^")"
  | Label (_, _, _) -> "label"
  | Break (_, _, _) -> "break"
  | TryCatch (_, _, _) -> "catch"
  | TryFinally (_, _, _) -> "finally"
  | Throw (_, _) -> "throw"
  | Lambda (_, xs, e) ->
    "func("^(string_of_list xs (fun x->x))^", "^(string_of_exp e)^")"
  | Eval (_, _, _) -> "eval"
  | Hint (_, _, _) -> "hint"

let rec full_string_of_exp exp = match exp with
  | Null p -> "null"
  | Undefined _ -> "undef"
  | String (_, v) -> "\"" ^ v ^ "\""
  | Num (_, f) -> string_of_float f
  | True _ -> "true"
  | False _ -> "false"
  | Id (_, x) -> x
  | Object (_, _, _) -> "object"
  | GetAttr (_, _, _, _) -> "getattr"
  | SetAttr (_, _, _, _, _) -> "setattr"
  | GetObjAttr (_, _, _) -> "getobjattr"
  | SetObjAttr (_, _, _, _) -> "setobjattr"
  | GetField (_, _, _, _) -> "getfield"
  | SetField (_, _, _, _, _) -> "setfield"
  | DeleteField (_, _, _) -> "deletefield"
  | OwnFieldNames (_, _) -> "ownfieldnames"
  | SetBang (_, s, e) -> s ^ " := " ^ (full_string_of_exp e)
  | Op1 (_, s, e) -> s ^ "(" ^ (full_string_of_exp e) ^ ")"
  | Op2 (_, s, e1, e2) -> (full_string_of_exp e1) ^ " " ^ s ^ " " ^ (full_string_of_exp e2)
  | If (_, cond, cons, alt) -> "if (" ^ (full_string_of_exp cond) ^ ") {" ^
                               (full_string_of_exp cons) ^ "} else {" ^
                               (full_string_of_exp alt) ^ "}"
  | App (_, f, args) -> (full_string_of_exp f) ^ "(" ^
                        (String.concat ", " (List.map full_string_of_exp args)) ^ ")"
  | Seq (_, e1, e2) -> (full_string_of_exp e1) ^ "; " ^ (full_string_of_exp e2)
  | Let (_, x, e, body) ->
    "{let (" ^ x ^ " = " ^ (full_string_of_exp e) ^ ") " ^ (full_string_of_exp body) ^ "}"
  | Rec (_, x, e1, e2) ->
    "rec (" ^ x ^ " = " ^ (full_string_of_exp e1) ^ ") " ^ (full_string_of_exp e2) ^ ")"
  | Label (_, _, _) -> "label"
  | Break (_, _, _) -> "break"
  | TryCatch (_, _, _) -> "catch"
  | TryFinally (_, _, _) -> "finally"
  | Throw (_, _) -> "throw"
  | Lambda (_, xs, e) ->
    "func (" ^ (String.concat ", " xs) ^ ") {" ^ (full_string_of_exp e) ^ "}"
  | Eval (_, _, _) -> "eval"
  | Hint (_, _, _) -> "hint"

let string_of_prop = function
  | Data ({value = v; _}, _, _) -> "data(" ^ (string_of_exp v) ^ ")"
  | Accessor ({getter = g; setter = s}, _, _) ->
    "accessor(" ^ (string_of_exp g) ^ ", " ^ (string_of_exp s) ^ ")"
