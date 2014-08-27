 (* Imported from labichn's LambdaS5 fork
   TODO:
     - labichn object store stores set of object, whereas mine stores either one
       object or the top object. Using his approach might be a better idea
*)

open Prelude
open Lattice
open Store
open Shared

module O = Obj_val

exception PrimErr of string

let to_lookup ostore ostore' = fun a ->
  if ObjectStore.contains a ostore then
    ObjectStore.lookup a ostore
  else if ObjectStore.contains a ostore' then
    ObjectStore.lookup a ostore'
  else
    failwith ("No object found at address " ^ (Address.to_string a))

let typeof lookup = function
  | `Undef -> AValue.str "undefined"
  | `Null -> AValue.str "null"
  | `Str _ -> AValue.str "string"
  | `Num _ -> AValue.str "number"
  | `True | `False -> AValue.str "boolean"
  | `Obj a -> begin match lookup a with
      | `Obj ({ O.code = `Bot; _ }, _) -> AValue.str "object"
      | _ -> AValue.str "function"
    end
  (* OSet.fold
     (fun (attrs, _) acc -> match attrs with
     | { code = `Bot } -> AValue.join acc (AValue.str "object")
     | _ -> join acc (AValue.str "function"))
     (get_objs a store) `Bot *)
  | `Clos _ -> raise (PrimErr "typeof got lambda")
  | _ -> `StrT

let is_closure v = match v with
  | `Clos _ | `ClosT-> `True
  | _ -> `False

let is_primitive v = match v with
  | `Undef | `Null | `Str _ | `StrT | `Num _ | `NumT | `True | `False | `BoolT -> `True
  | _ -> `False

let float_str n =
  if not (n <= n || n >= n) then "NaN"
  else
    if n == infinity then "Infinity"
    else if n == neg_infinity then "-Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n)
      else string_of_float n

let prim_to_str v = match v with
  | `Undef -> AValue.str "undefined"
  | `Null -> AValue.str "null"
  | `Str s -> AValue.str s
  | `Num n ->
    let fs = float_str n in
    let fslen = String.length fs in
    if String.get fs (fslen - 1) = '.' then
      AValue.str (String.sub fs 0 (fslen - 1))
    else
        (* This is because we don't want leading zeroes in the "-e" part.
         * For example, OCaml says 1.2345e-07, but ES5 wants 1.2345e-7 *)
      if String.contains fs '-'
      then let indx = String.index fs '-' in
           let prefix = String.sub fs 0 (indx + 1) in
           let suffix = String.sub fs (indx + 1) (fslen - (String.length prefix)) in
           let slen = String.length suffix in
           let fixed = if slen > 1 && (String.get suffix 0 = '0')
             then String.sub suffix 1 (slen - 1)
             else suffix in
           AValue.str (prefix ^ fixed)
      else AValue.str fs
  | `True -> AValue.str "true"
  | `False -> AValue.str "false"
  | `BoolT | `NumT | `StrT -> `StrT
  | _ -> raise (PrimErr ("prim_to_str with value " ^ (AValue.to_string v)))

let strlen s = match s with
  | `Str s -> `Num (float_of_int (String.length s))
  | `StrT -> `NumT
  | _ -> raise (PrimErr ("strlen with value " ^ (AValue.to_string s)))

  (* Section 9.3, excluding objects *)
let prim_to_num v = match v with
  | `Undef -> `Num nan
  | `Null -> `Num 0.0
  | `True -> `Num 1.0
  | `False -> `Num 0.0
  | `Num x -> `Num x
  | `Str "" -> `Num 0.0
  | `Str s -> `Num (try float_of_string s with Failure _ -> nan)
  | `BoolT | `NumT | `StrT -> `NumT
  | _ -> raise (PrimErr ("prim_to_num with value " ^ (AValue.to_string v)))

let prim_to_bool v =
  let helper = function
    | true -> `True
    | false -> `False in
  match v with
  | `Num x ->  helper (not (x == nan || x = 0.0 || x = -0.0))
  | `Str s -> helper (not (String.length s = 0))
  | `BoolT | `NumT | `StrT -> `BoolT
  | `False
  | `Undef
  | `Null -> `False
  | `True
  | _ -> `True

(* TODO: how to deal with such side effects in an abstract interpreter? *)
let print v = match v with
  | `Str s -> printf "%s\n%!" s; `Undef
  | `Num n -> let s = string_of_float n in printf "%S\n%!" s; `Undef
  | _ -> printf "%s\n%!" (AValue.to_string v); `Undef
(*  | _ -> failwith ("[interp] Print received non-string: " ^ AValue.to_string v) *)

let pretty v =
  printf "%s\n%!" (AValue.to_string v); `Undef

let is_extensible lookup obj = match obj with
  | `Obj loc -> begin match lookup loc with
    | `Obj ({ O.extensible = ext; _ }, _) -> ext
    | `ObjT -> `BoolT
    end
  | `ObjT -> `BoolT
  | _ -> raise (PrimErr "is-extensible")

  (* Implement this here because there's no need to expose the class
     property outside of the delta function *)
let object_to_string lookup obj = match obj with
  | `Obj loc -> begin match lookup loc with
      | `Obj ({ O.klass = kls; _ }, _) -> begin match kls with
        | `Str s -> AValue.str ("[object " ^ s ^ "]")
        | _ -> `StrT
        end
      | `ObjT -> `StrT
    end
  | `ObjT -> `StrT
  | _ -> raise (PrimErr "object-to-string, wasn't given object")

let is_array lookup obj = match obj with
  | `Obj loc -> begin match lookup loc with
    | `Obj ({ O.klass = kls; _ }, _) -> begin match kls with
      | `Str "Array" -> `True
      | `Str _ -> `False
      | _ -> `BoolT
      end
    | `ObjT -> `BoolT
    end
  | `ObjT -> `BoolT
  | _ -> raise (PrimErr "is-array")

let to_int32 v = match v with
  | `Num d -> `Num (float_of_int (int_of_float d))
  | `NumT -> `NumT
  | _ -> raise (PrimErr "to-int")

let nnot e = match e with
  | `Undef
  | `False
  | `Null -> `True
  | `Num d when (d = 0.) || (d <> d) -> `True
  | `Str s when (s = "") -> `True
  | `Num _
  | `Str _
  | `Obj _ | `ObjT
  | `Clos _ | `ClosT
  | `True -> `False
  | `NumT | `StrT | `BoolT | `Top -> `BoolT
  | _ -> raise (PrimErr "nnot fallthrough")

let void v = `Undef

let floor' = function
  | `Num d -> `Num (floor d)
  | `NumT -> `NumT
  | _ -> raise (PrimErr "floor")

let ceil' = function
  | `Num d -> `Num (ceil d)
  | `NumT -> `NumT
  | _ -> raise (PrimErr "ceil")

let absolute = function
  | `Num d -> `Num (abs_float d)
  | `NumT -> `NumT
  | _ -> raise (PrimErr "abs")

let log' = function
  | `Num d -> `Num (log d)
  | `NumT -> `NumT
  | _ -> raise (PrimErr "log")

let ascii_ntoc n = match n with
  | `Num d -> `Str (String.make 1 (Char.chr (int_of_float d)))
  | `NumT -> `StrT
  | _ -> raise (PrimErr "ascii_ntoc")
let ascii_cton c = match c with
  | `Str s -> `Num (float_of_int (Char.code (String.get s 0)))
  | `StrT -> `NumT
  | _ -> raise (PrimErr "ascii_cton")

let to_lower = function
  | `Str s -> `Str (String.lowercase s)
  | `StrT -> `StrT
  | _ -> raise (PrimErr "to_lower")

let to_upper = function
  | `Str s -> `Str (String.uppercase s)
  | `StrT -> `StrT
  | _ -> raise (PrimErr "to_lower")

let bnot = function
  | `Num d -> `Num (float_of_int (lnot (int_of_float d)))
  | `NumT -> `NumT
  | _ -> raise (PrimErr "bnot")

let sine = function
  | `Num d -> `Num (sin d)
  | `NumT -> `NumT
  | _ -> raise (PrimErr "sin")

let numstr = function
  | `Str "" -> `Num 0.
  | `Str s -> `Num (try float_of_string s with Failure _ -> nan)
  | `StrT -> `NumT
  | _ -> raise (PrimErr "numstr")

let current_utc = function
  | _ -> `NumT

let op1 (store : ObjectStore.t) (gstore : ObjectStore.t) (op : string)
  : AValue.t -> AValue.t =
  let lookup = to_lookup store gstore in
  match op with
  (* return undef *)
  | "print" -> print
  | "pretty" -> pretty
  | "void" -> void

  (* return string *)
  | "typeof" -> typeof lookup
  | "prim->str" -> prim_to_str
  | "object-to-string" -> object_to_string lookup
  | "ascii_ntoc" -> ascii_ntoc
  | "to-lower" -> to_lower
  | "to-upper" -> to_upper

  (* return num *)
  | "prim->num" -> prim_to_num
  | "strlen" -> strlen
  | "to-int32" -> to_int32
  | "floor" -> floor'
  | "ceil" -> ceil'
  | "abs" -> absolute
  | "log" -> log'
  | "ascii_cton" -> ascii_cton
  | "~" -> bnot
  | "numstr->num" -> numstr
  | "current-utc-millis" -> current_utc

  (* return bool *)
  | "closure?" -> is_closure
  | "primitive?" -> is_primitive
  | "prim->bool" -> prim_to_bool
  | "is-array" -> is_array lookup
  | "!" -> nnot
  | "sin" -> sine
  | _ ->
    raise (PrimErr ("no implementation of unary operator: " ^ op))

let arith s f_op v1 v2 = match v1, v2 with
  | `Num x, `Num y -> `Num (f_op x y)
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT -> `NumT
  | v1, v2 -> raise (PrimErr "arith got non-numbers")

let arith_sum = arith "+" (+.)

let arith_sub = arith "-" (-.)

let arith_mul = arith "*" ( *. )

let arith_div x y = try arith "/" (/.) x y
  with Division_by_zero -> `Num infinity

let arith_mod x y = try arith "mod" mod_float x y
  with Division_by_zero -> `Num nan

(* TODO: abstract those (arith_lt, arith_le, arith_gt, arith_ge) *)
let arith_lt x y = AValue.bool (x < y)

let arith_le x y = AValue.bool (x <= y)

let arith_gt x y = AValue.bool (x > y)

let arith_ge x y = AValue.bool (x >= y)

let bin_float op x y = float_of_int (op (int_of_float x) (int_of_float y))

let bitwise_and = arith "&" (bin_float (land))

let bitwise_or = arith "|" (bin_float (lor))

let bitwise_xor = arith "^" (bin_float (lxor))

let bitwise_shiftl = arith "<<" (bin_float (lsl))

let bitwise_zfshiftr = arith ">>>" (bin_float (lsr))

let bitwise_shiftr = arith ">>" (bin_float (asr))

let string_plus v1 v2 = match v1, v2 with
  | `Str s1, `Str s2 -> `Str (s1 ^ s2)
  | `StrT, `Str _ | `Str _, `StrT | `StrT, `StrT -> `StrT
  | _ -> raise (PrimErr "string concatenation")

let string_lessthan v1 v2 = match v1, v2 with
  | `Str s1, `Str s2 -> AValue.bool (s1 < s2)
  | `StrT, `Str _ | `Str _, `StrT | `StrT, `StrT -> `BoolT
  | _ -> raise (PrimErr "string less than")

let stx_eq v1 v2 = match v1, v2 with
  | `Num x1, `Num x2 -> AValue.bool (x1 = x2)
  | `Str x1, `Str x2 -> AValue.bool (x1 = x2)
  | `Undef, `Undef
  | `Null, `Null
  | `False, `False
  | `True, `True -> `True
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT
  | `StrT, `Str _ | `Str _, `StrT | `StrT, `StrT
  | `BoolT, `True | `True, `BoolT | `BoolT, `False | `False, `BoolT
  | `BoolT, `BoolT -> `BoolT
  | _ -> AValue.bool (v1 == v2) (* otherwise, pointer equality *)

  (* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
     access the heap. *)
let abs_eq v1 v2 = match v1, v2 with
  | `Null, `Undef
  | `Undef, `Null -> `True
  | `Str s1, `Str s2 when s1 = s2 -> `True
  | `Num x, `Num y when x = y -> `True
  | `Str s, `Num x
  | `Num x, `Str s ->
    (try AValue.bool (x = float_of_string s) with Failure _ -> `False)
  | `Num x, `True | `True, `Num x -> AValue.bool (x = 1.0)
  | `Num x, `False | `False, `Num x -> AValue.bool (x = 0.0)
  | `StrT, `Str _ | `Str _, `StrT | `StrT, `StrT
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT
  | `StrT, `Num _ | `StrT, `NumT | `Num _, `StrT | `NumT, `StrT
  | `NumT, `True | `True, `NumT | `NumT, `False | `False, `NumT
  | `Num _, `BoolT | `BoolT, `Num _ | `NumT, `BoolT | `BoolT, `NumT ->
    `BoolT
  | _ -> `False
  (* TODO: are these all the cases? *)

  (* Algorithm 9.12, the SameValue algorithm.
     This gives "nan = nan" and "+0 != -0". *)
let same_value v1 v2 = match v1, v2 with
  | `Num x, `Num y ->
    AValue.bool (if x = 0. && y = 0.
                 then 1. /. x = 1. /. y
                 else Pervasives.compare x y = 0)
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT
  | `StrT, `Str _ | `Str _, `StrT | `StrT, `StrT
  | `BoolT, `True | `True, `BoolT | `BoolT, `False | `False, `BoolT
  | `BoolT, `BoolT -> `BoolT
  | _ -> AValue.bool (Pervasives.compare v1 v2 = 0)

let rec has_property lookup obj field = match obj, field with
  | `Obj loc, _ -> begin match lookup loc with
    | `Obj (({ O.proto = proto; _ }, _) as o) ->
      if O.has_prop o field then
        `True
      else
        has_property lookup proto field
    | `ObjT -> `BoolT
    end
  | `ObjT, _ -> `BoolT
  | _ -> `False

let has_own_property lookup obj field = match obj, field with
  | `Obj loc, `Str _ -> begin match lookup loc with
      | `Obj (({ O.proto = proto; _ }, _) as o) ->
        AValue.bool (O.has_prop o field)
      | `ObjT -> `BoolT
    end
  | `Obj _, `StrT | `ObjT, `Str _ | `ObjT, `StrT -> `BoolT
  | `Obj loc, _ ->
    raise (PrimErr "has-own-property: field not a string")
  | _, `Str s ->
    raise (PrimErr ("has-own-property: obj not an object for field " ^ s))
  | _ ->
    raise (PrimErr "has-own-property: neither an object nor a string")

let base n r =
  let rec get_digits n l = match n with
    | 97 -> 'a' :: l
    | i -> get_digits (n - 1) ((Char.chr i) :: l) in
  let digits =
    ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] @ (get_digits 122 []) in
  let rec get_num_digits num so_far =
    if (r ** so_far) > num then so_far -. 1.0
    else get_num_digits num (so_far +. 1.0) in
  let rec convert b result len =
    let lp = r ** len in
    let index = floor (b /. lp) in
    let digit = String.make 1 (List.nth digits (int_of_float index)) in
    if len = 0.0 then result ^ digit
    else convert (b -. (index *. lp)) (result ^ digit)  (len -. 1.0) in
  (* let rec shift frac n = if n = 0 then frac else shift (frac *. 10.0) (n - 1) in *)
  let (f, integ) = modf n in
    (* TODO(joe): shifted is unused *)
    (* let shifted = shift f ((`Str.length (string_of_float f)) - 2) in *)
  if (f = 0.0) then
    let d = get_num_digits n 0.0 in
    convert n "" d
  else
      (* TODO: implement *)
    "non-base-10 with fractional parts NYI"

let get_base n r = match n, r with
  | `Num x, `Num y ->
    let result = base (abs_float x) (abs_float y) in
    `Str (if x < 0.0 then "-" ^ result else result)
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT -> `StrT
  | _ -> raise (PrimErr "base got non-numbers")

let char_at a b  = match a, b with
  | `Str s, `Num n ->
    `Str (String.make 1 (String.get s (int_of_float n)))
  | `StrT, `Num _ | `Str _, `NumT -> `StrT
  | _ -> raise (PrimErr "char_at didn't get a string and a number")

let locale_compare a b = match a, b with
  | `Str r, `Str s ->
    `Num (float_of_int (String.compare r s))
  | `StrT, `Str _ | `Str _ , `StrT | `StrT, `StrT -> `NumT
  | _ -> raise (PrimErr "locale_compare didn't get 2 strings")

let pow a b = match a, b with
  | `Num base, `Num exp -> `Num (base ** exp)
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT -> `NumT
  | _ -> raise (PrimErr "pow didn't get 2 numbers")

let to_fixed a b = match a, b with
  | `Num x, `Num f ->
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0
    then `Str (string_of_int (int_of_float x))
    else let dot_index = String.index s '.'
    and len = String.length s in
         let prefix_chars = dot_index in
         let decimal_chars = len - (prefix_chars + 1) in
         if decimal_chars = fint then `Str s
         else if decimal_chars > fint
         then let fixed_s = String.sub s 0 (fint - prefix_chars) in
              `Str (fixed_s)
         else let suffix = String.make (fint - decimal_chars) '0' in
              `Str (s ^ suffix)
  | `NumT, `Num _ | `Num _, `NumT | `NumT, `NumT -> `NumT
  | _ -> raise (PrimErr "to-fixed didn't get 2 numbers")

let rec is_accessor lookup a b = match a, b with
  | `Obj loc, _ -> begin match lookup loc with
    | `Obj o ->
      if O.has_prop o b then
        begin match O.lookup_prop o b with
          | O.Data _ -> `False
          | O.Accessor _ -> `True
        end
      else
        let ({ O.proto = proto; _ }, _) = o in
        is_accessor lookup proto b
    | `ObjT -> `BoolT
    end
  | `ObjT, `Str _ -> `BoolT
  | `Null, `Str s -> raise (PrimErr "isAccessor on a null object")
  | _ -> raise (PrimErr "isAccessor")

let op2 (store : ObjectStore.t) (gstore : ObjectStore.t) (op : string)
  : AValue.t -> AValue.t -> AValue.t =
  let lookup = to_lookup store gstore in
  match op with
  | "+" -> arith_sum
  | "-" -> arith_sub
  | "/" -> arith_div
  | "*" -> arith_mul
  | "%" -> arith_mod
  | "&" -> bitwise_and
  | "|" -> bitwise_or
  | "^" -> bitwise_xor
  | "<<" -> bitwise_shiftl
  | ">>" -> bitwise_shiftr
  | ">>>" -> bitwise_zfshiftr
  | "<" -> arith_lt
  | "<=" -> arith_le
  | ">" -> arith_gt
  | ">=" -> arith_ge
  | "stx=" -> stx_eq
  | "abs=" -> abs_eq
  | "sameValue" -> same_value
  | "hasProperty" -> has_property lookup
  | "hasOwnProperty" -> has_own_property lookup
  | "string+" -> string_plus
  | "string<" -> string_lessthan
  | "base" -> get_base
  | "char-at" -> char_at
  | "locale-compare" -> locale_compare
  | "pow" -> pow
  | "to-fixed" -> to_fixed
  | "isAccessor" -> is_accessor lookup
  | _ ->
    raise (PrimErr ("no implementation of binary operator: " ^ op))
