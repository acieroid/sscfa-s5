open Prelude
open Ljs_syntax

let gc : [ `NormalGC | `NoGC | `NoGlobalGC | `RestrictedGC ] ref = ref `NormalGC
let only_mcfa = ref false

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

let string_of_list s_o_elt l =
  if List.length l > 0 then
    let elts = List.fold_right (fun elt a -> (s_o_elt elt)^", "^a) l "" in
    "["^(String.sub elts 0 ((String.length elts)-2))^"]"
  else "[]"

let string_of_map fold k v m =
  "{" ^ (String.concat "\n"
           (fold (fun k' v' a -> ((k k') ^ ": " ^ (v v')) :: a) m [])) ^ "}"

let string_of_set fold e s =
  "{" ^ (String.concat ", " (fold (fun e' a -> (e e') :: a) s [])) ^ "}"

module StringSet = BatSet.Make(struct
    type t = string
    let compare = Pervasives.compare
  end)

module type TimeSignature =
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
    let to_string = string_of_list Arg.to_string
    let tick x t =
      (* print_endline ("\027[34mtick " ^ (Arg.to_string x) ^ "\027[0m"); *)
      BatList.take K.k (x :: t)
  end

module type AddressSignature =
  sig
    type t
    type time
    val compare : t -> t -> int
    val is_reclaimable : t -> bool
    val to_string : t -> string
    val alloc : Pos.t -> string -> time -> t
  end

module MakeAddress =
  functor (T : TimeSignature) ->
  struct
    type time = T.t
    type t = (Pos.t * string * T.t)
    let compare ((p, id, t) : t) ((p', id', t') : t) =
      order_concat [lazy (Pos.compare p p');
                    lazy (Pervasives.compare id id');
                    lazy (T.compare t t')]
    let is_reclaimable a = true
    let to_string (_, id, t) = id ^ "-" ^ (T.to_string t)
    let alloc (p : Pos.t) (id : string) (t : T.t) : t = (p, id, t)
  end

module MakeVarAddress =
  functor (T : TimeSignature) ->
  struct
    module A = MakeAddress(T)
    include A
    let is_reclaimable (_, id, _) =
      if !gc != `RestrictedGC then
        (* %or is a special variable frequetly present in desugared S5 code, but
           it is *not* used to denote a global identifier *)
        id = "let-%or" ||
        (* other variables starting with % or # are not reclaimable *)
        not (BatString.starts_with id "%" || BatString.starts_with id "#")
      else
        true
    let to_string a = "@var-" ^ (A.to_string a)
    let alloc p id t =
      Printf.printf "\027[33malloc_var(%s, %s, %s)\027[0m\n%!"
        (Pos.to_string p) id (T.to_string t);
      A.alloc p id t
  end

module MakeObjAddress =
  functor (T : TimeSignature) ->
  struct
    module A = MakeAddress(T)
    include A
    let is_reclaimable (_, id, _) =
      if !gc != `RestrictedGC then
        (* object allocation scheme different than variable's *)
        not (BatString.starts_with id "let-%" || BatString.starts_with id "let-#")
      else
        true
    let to_string a = "@obj-" ^ (A.to_string a)
    let alloc p id t =
      Printf.printf "\027[33malloc_obj(%s, %s, %s)\027[0m\n%!"
        (Pos.to_string p) id (T.to_string t);
      A.alloc p id t
  end

module type ParameterSensitiveArgument = sig
  type t
  val to_string : t -> string
  val compare : t -> t -> int
end
module ParameterSensitive =
  functor (Arg : ParameterSensitiveArgument) ->
  struct
    (* We need to duplicate a bit of lattice.ml here, it should be better to put
       this in another file. We cannot use the Lattice module here as it depends
       on this module for addresses *)
    type v = [ `True | `False | `BoolT
             | `Obj of Arg.t
             | `Str of string | `StrT
             | `Num of float | `NumT
             | `Null | `Undef
             | `Top | `Bot ]

    let string_of_v : v -> string = function
      | `True -> "true"
      | `False -> "false"
      | `BoolT -> "boolT"
      | `Obj addrs -> "obj" ^ (Arg.to_string addrs)
      | `Num n -> string_of_float n
      | `NumT -> "numT"
      | `Str s -> "'" ^ s ^ "'"
      | `StrT -> "strT"
      | `Null -> "null"
      | `Undef -> "undef"
      | `Top -> "T"
      | `Bot -> "_|_"

    let compare_v (x : v) (y : v) : int  = match x, y with
      | `True, `True | `False, `False | `BoolT, `BoolT
      | `StrT, `StrT | `NumT, `NumT
      | `Null, `Null | `Undef, `Undef
      | `Top, `Top | `Bot, `Bot -> 0
      | `Obj addrs, `Obj addrs' -> Arg.compare addrs addrs'
      | `Str s, `Str s' -> Pervasives.compare s s'
      | `Num n, `Num n' -> Pervasives.compare n n'
      | `True, _ -> 1 | _, `True -> -1
      | `False, _ -> 1 | _, `False -> -1
      | `BoolT, _ -> 1 | _, `BoolT -> -1
      | `Obj _, _ -> 1 | _, `Obj _ -> -1
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
      string_of_list (fun (n, v) -> n ^ ": " ^ (string_of_v v)) l

  end

(* Two kinds of timestamps (and therefore two kinds of addresses).
   This could be more modular, but is not easy to get right *)
let k = 1
module rec VarAddress : sig
  include AddressSignature with type time = Time.t
end = MakeVarAddress(Time)
and ObjAddress : sig
  include AddressSignature with type time = Time.t
end = MakeObjAddress(Time)
and ObjAddressSet : sig
  include BatSet.S with type elt = ObjAddress.t
                    (* for compatibility with ObjectStore *)
                    and type t = BatSet.Make(ObjAddress).t
  val to_string : t -> string
  val join : t -> t -> t
end = struct
  module A = BatSet.Make(ObjAddress)
  include A
  let to_string = string_of_set A.fold ObjAddress.to_string
  let join = A.union
end
and Time : sig
  type v = [ `True | `False | `BoolT
           | `Obj of ObjAddressSet.t
           | `Str of string | `StrT
           | `Num of float | `NumT
           | `Null | `Undef
           | `Top | `Bot ]
  include TimeSignature
    with type arg = Pos.t * (string * v) list
     and type t = [ `MCFATime of K1Time.t | `PSKCFATime of PSTime.t ]
end
= struct
  type v = [ `True | `False | `BoolT
           | `Obj of ObjAddressSet.t
           | `Str of string | `StrT
           | `Num of float | `NumT
           | `Null | `Undef
           | `Top | `Bot ]
  type arg = Pos.t * (string * v) list
  type t = [ `MCFATime of K1Time.t | `PSKCFATime of PSTime.t ]
  let initial = `PSKCFATime PSTime.initial
  let compare x y = match x, y with
    | `MCFATime t, `MCFATime t' -> K1Time.compare t t'
    | `MCFATime _, _ -> 1
    | _, `MCFATime __ -> 1
    | `PSKCFATime t, `PSKCFATime t' -> PSTime.compare t t'
  let to_string = function
    | `MCFATime t -> K1Time.to_string t
    | `PSKCFATime t -> PSTime.to_string t
  let tick (arg : arg) : t -> t = function
    | `MCFATime t -> `MCFATime t (* don't tick here with m-CFA *)
    | `PSKCFATime t -> `PSKCFATime (PSTime.tick arg t)
end
and PSTime : sig
  type v = [ `True | `False | `BoolT
           | `Obj of ObjAddressSet.t
           | `Str of string | `StrT
           | `Num of float | `NumT
           | `Null | `Undef
           | `Top | `Bot ]
  include TimeSignature with type arg = Pos.t * (string * v) list
end
= struct
  module PS = ParameterSensitive(ObjAddressSet)
  module K1 = struct let k = 1 end
  include KCFABased(PS)(K1)
  type v = PS.v
end
and K1Time : sig
  include TimeSignature with type arg = Pos.t and type t = Pos.t list
end
= struct
  type arg = Pos.t
  type t = arg list
  let initial = []
  let compare = compare_list Pos.compare
  let to_string = string_of_list Pos.to_string
  let tick x t = BatList.take k (x :: t)
end

module VarAddressSet = struct
  module A = BatSet.Make(VarAddress)
  include A
  let to_string = string_of_set A.fold VarAddress.to_string
end

module AddressSet = struct
  type t = {
    vars : VarAddressSet.t;
    objs : ObjAddressSet.t;
  }
  let empty = {vars = VarAddressSet.empty; objs = ObjAddressSet.empty}
  let vars vs = {empty with vars = vs}
  let objs os = {empty with objs = os}
  let singleton_var a = {empty with vars = VarAddressSet.singleton a}
  let singleton_obj a = {empty with objs = ObjAddressSet.singleton a}
  let add_var a t = {t with vars = VarAddressSet.add a t.vars}
  let add_obj a t = {t with objs = ObjAddressSet.add a t.objs}
  let union_vars addrs t = {t with vars = VarAddressSet.union addrs t.vars}
  let union_objs addrs t = {t with objs = ObjAddressSet.union addrs t.objs}
  let union t t' = {
    vars = VarAddressSet.union t.vars t'.vars;
    objs = ObjAddressSet.union t.objs t'.objs;
  }
  let mem_var a t = VarAddressSet.mem a t.vars
  let mem_obj a t = ObjAddressSet.mem a t.objs
(*  let mem_objs a t = ObjAddressSet.subset a t.objs *)
  let remove_var a t = {t with vars = VarAddressSet.remove a t.vars}
  let remove_obj a t = {t with objs = ObjAddressSet.remove a t.objs}
(*  let remove_objs addrs t = {t with objs = ObjAddressSet.diff t.objs addrs} *)
  let compare t t' =
    order_concat [lazy (VarAddressSet.compare t.vars t'.vars);
                  lazy (ObjAddressSet.compare t.objs t'.objs)]
  let is_empty t =
    VarAddressSet.is_empty t.vars && ObjAddressSet.is_empty t.objs
  let choose t =
    if VarAddressSet.is_empty t.vars then
      `Obj (ObjAddressSet.choose t.objs)
    else
      `Var (VarAddressSet.choose t.vars)
  let fold f t init =
    let init' = VarAddressSet.fold (fun a acc -> f (`Var a) acc) t.vars init in
    ObjAddressSet.fold (fun a acc -> f (`Obj a) acc) t.objs init'
  let to_string t =
    "[" ^ (VarAddressSet.to_string t.vars) ^
    ", " ^ (ObjAddressSet.to_string t.objs) ^ "]"
  let to_vars t = t.vars
  let to_objs t = t.objs
end

let rec string_of_exp exp = match exp with
  | Null p -> "Null"
  | Undefined _ -> "Undefined"
  | String (_, v) -> "'" ^ v ^ "'"
  | Num (_, f) -> (string_of_float f)
  | True _ -> "True"
  | False _ -> "False"
  | Id (_, x) -> x
  | Object (_, _, _) -> "Object"
  | GetAttr (_, _, _, _) -> "GetAttr"
  | SetAttr (_, _, _, _, _) -> "SetAttr"
  | GetObjAttr (_, _, _) -> "GetObjAttr"
  | SetObjAttr (_, _, _, _) -> "SetObjAttr"
  | GetField (_, _, _, _) -> "GetField"
  | SetField (_, _, _, _, _) -> "SetField"
  | DeleteField (_, _, _) -> "DeleteField"
  | OwnFieldNames (_, _) -> "OwnFieldNames"
  | SetBang (_, _, _) -> "SetBang"
  | Op1 (_, s, e) -> "Op1(" ^ s ^ ", " ^ (string_of_exp e) ^ ")"
  | Op2 (_, s, e1, e2) -> "Op2(" ^ s ^ ", " ^ (string_of_exp e1) ^ ", " ^ (string_of_exp e2) ^ ")"
  | If (_, _, _, _) -> "If"
  | App (_, _, _) -> "App"
  | Seq (_, _, _) -> "Seq"
  | Let (_, x, e, _) ->
    "let (" ^ x ^ " = " ^ (string_of_exp e) ^ ")"
  | Rec (_, x, e1, e2) ->
    "rec(" ^ x ^ ", " ^ (string_of_exp e1) ^ ", " ^ (string_of_exp e2) ^ ")"
  | Label (_, _, _) -> "Label"
  | Break (_, _, _) -> "Break"
  | TryCatch (_, _, _) -> "Catch"
  | TryFinally (_, _, _) -> "Finally"
  | Throw (_, _) -> "Throw"
  | Lambda (_, xs, e) ->
    "func(" ^ (string_of_list (fun x -> x) xs) ^ ", " ^ (string_of_exp e) ^ ")"
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
  | Object (_, _, _) -> "Object"
  | GetAttr (_, _, _, _) -> "GetAttr"
  | SetAttr (_, _, _, _, _) -> "SetAttr"
  | GetObjAttr (_, _, _) -> "GetObjAttr"
  | SetObjAttr (_, _, _, _) -> "SetObjAttr"
  | GetField (_, _, _, _) -> "GetField"
  | SetField (_, _, _, _, _) -> "SetField"
  | DeleteField (_, _, _) -> "DeleteField"
  | OwnFieldNames (_, _) -> "OwnFieldNames"
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
    "let (" ^ x ^ " = " ^ (full_string_of_exp e) ^ ") " ^ (full_string_of_exp body)
  | Rec (_, x, e1, e2) ->
    "rec (" ^ x ^ " = " ^ (full_string_of_exp e1) ^ ") " ^ (full_string_of_exp e2) ^ ")"
  | Label (_, _, _) -> "Label"
  | Break (_, _, _) -> "Break"
  | TryCatch (_, _, _) -> "Catch"
  | TryFinally (_, _, _) -> "Finally"
  | Throw (_, _) -> "Throw"
  | Lambda (_, xs, e) ->
    "func (" ^ (String.concat ", " xs) ^ ") {" ^ (full_string_of_exp e) ^ "}"
  | Eval (_, _, _) -> "Eval"
  | Hint (_, _, _) -> "Hint"

let string_of_prop = function
  | Data ({value = v; _}, _, _) -> "Data(" ^ (string_of_exp v) ^ ")"
  | Accessor ({getter = g; setter = s}, _, _) ->
    "Accessor(" ^ (string_of_exp g) ^ ", " ^ (string_of_exp s) ^ ")"
