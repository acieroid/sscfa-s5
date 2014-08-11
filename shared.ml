open Ljs_syntax

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
  order_concat
    (lazy (Pervasives.compare (BatList.length l1) (BatList.length l2))
     :: (BatList.map
           (fun (el1, el2) -> lazy (cmp el1 el2))
           (BatList.combine l1 l2)))

module StringSet = BatSet.Make(struct
    type t = string
    let compare = Pervasives.compare
  end)

module type Address_signature =
sig
  type t
  val compare : t -> t -> int
  val to_string : t -> string
  val alloc : int -> t (* TODO: find a place where it belongs *)
end

(* S5 uses Store.Loc module (util/store.ml) *)
module Address : Address_signature =
struct
  type t = int
  let compare = Pervasives.compare
  let to_string = string_of_int
  let alloc x = x mod 100
end

let string_of_list l s_o_elt =
  if List.length l > 0 then
    let elts = List.fold_right (fun elt a -> (s_o_elt elt)^", "^a) l "" in
    "["^(String.sub elts 0 ((String.length elts)-2))^"]"
  else "[]"

let string_of_map fold k v m =
  "{" ^ (fold (fun k' v' a -> (k k')^" --> "^(v v')^"\n"^a) m " }")

let rec string_of_exp exp = match exp with
  | Null _ -> "null"
  | Undefined _ -> "undef"
  | String (_, v) -> "string("^v^")"
  | Num (_, f) -> "num("^(string_of_float f)^")"
  | True _ -> "true"
  | False _ -> "false"
  | Id (_, x) -> "id: "^x^" "
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
  | Op1 (_, _, _) -> "op1"
  | Op2 (_, _, _, _) -> "op2"
  | If (_, _, _, _) -> "if"
  | App (_, _, _) -> "appr"
  | Seq (_, _, _) -> "seq"
  | Let (_, x, e, _) ->
    "(let "^x^" "^(string_of_exp e)^")"
  | Rec (_, x, e1, e2) ->
    "rec("^x^", "^(string_of_exp e1)^", "^(string_of_exp e2)^")"
  | Label (_, _, _) -> "label"
  | Break (_, _, _) -> "break"
  | TryCatch (_, _, _) -> "catch"
  | TryFinally (_, _, _) -> "fin"
  | Throw (_, _) -> "thrwo"
  | Lambda (_, xs, e) ->
    "lam("^(string_of_list xs (fun x->x))^", "^(string_of_exp e)^")"
  | Eval (_, _, _) -> "eval"
  | Hint (_, _, _) -> "hint"

let string_of_prop = function
  | Data ({value = v; _}, _, _) -> "data(" ^ (string_of_exp v) ^ ")"
  | Accessor ({getter = g; setter = s}, _, _) ->
    "accessor(" ^ (string_of_exp g) ^ ", " ^ (string_of_exp s) ^ ")"
