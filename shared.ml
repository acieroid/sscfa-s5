open Prelude
open Ljs_syntax

let debug = ref false

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
  val initial : t
  val compare : t -> t -> int
  val to_string : t -> string
  val tick : Pos.t -> t -> t
end

module OneCFA : Time_signature =
struct
  type t = Pos.t option
  let initial = None
  let compare = Pervasives.compare
  let to_string = function
    | Some p -> "[" ^ (Pos.string_of_pos p) ^ "]"
    | None -> "[]"
  let tick p = function
    | None -> Some p
    | Some _ -> Some p
end

module type KCFA_arg = sig val k : int end

module KCFA : functor (K : KCFA_arg) -> Time_signature =
  functor (K : sig val k : int end) ->
  struct
    type t = Pos.t list
    let initial = []
    let compare = Pervasives.compare
    let to_string t = string_of_list t Pos.string_of_pos
    let tick p t =
      print_endline ("\027[34mtick\027[0m");
      BatList.take K.k (p :: t)
  end

type 'a addr_kind = [ `ObjAddress of 'a | `VarAddress of 'a ]

module type Address_signature =
  functor (T : Time_signature) ->
  sig
    type a
    type t = a addr_kind
    val compare : t -> t -> int
    val to_string : t -> string
    val alloc_obj : string -> T.t -> t
    val alloc_var : string -> T.t -> t
  end

(* S5 uses Store.Loc module (util/store.ml) *)
module MakeAddress : Address_signature =
  functor (T : Time_signature) ->
struct
  type a = (string * T.t)
  type t = a addr_kind
  let compare x y = match x, y with
    | `ObjAddress (id, t), `ObjAddress (id', t') 
    | `VarAddress (id, t), `VarAddress (id', t') ->
      order_comp (Pervasives.compare id id') (T.compare t t')
    | `ObjAddress _, `VarAddress _ -> 1
    | `VarAddress _, `ObjAddress _ -> -1
  let to_string = function
    | `ObjAddress (id, t) -> "@obj-" ^ id
    | `VarAddress (id, t) -> "@var-" ^ id
  let alloc_obj id t =
    print_endline ("\027[33malloc_obj(" ^ (T.to_string t) ^ ")\027[0m");
    `ObjAddress (id, t)
  let alloc_var id t =
    print_endline ("\027[33malloc_var(" ^ (T.to_string t) ^ ")\027[0m");
    `VarAddress (id, t)
end

module K1 = struct let k = 1 end
module Time = KCFA(K1)
module Address = MakeAddress(Time)
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
