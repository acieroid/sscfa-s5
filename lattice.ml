open Env
open Shared
module S = Ljs_syntax

module AValue = struct
  type t = [
    | `Top
    | `Str of string | `StrT
    | `Num of float | `NumT
    | `True | `False | `BoolT
    | `Null | `Undef
    | `Clos of Env.t * Prelude.id list * S.exp | `ClosT
    | `Obj of ObjAddressSet.t
    | `Nullable of t
    | `Bot
  ]

  let bool b = if b then `True else `False

  let rec to_string : t -> string = function
    | `Top -> "Top"
    | `Str s -> "'" ^ s ^ "'"
    | `StrT -> "StrT"
    | `Num n -> string_of_float n
    | `NumT -> "NumT"
    | `True -> "true"
    | `False -> "false"
    | `BoolT -> "BoolT"
    | `Null -> "null"
    | `Undef -> "undefined"
    | `Clos (_, args, body) -> "Clos(" ^ (string_of_list (fun x -> x) args) ^ ")"
    | `ClosT -> "ClosT"
    | `Obj addrs -> "Obj(" ^ (ObjAddressSet.to_string addrs) ^ ")"
    | `Nullable t -> "Nullable(" ^ (to_string t) ^ ")"
    | `Bot -> "Bot"

  (* TODO: ppx *)
  let rec compare (x : t) (y : t) : int = match x, y with
    | `Top, `Top -> 0 | `Top, _ -> 1 | _, `Top -> -1
    | `Str s, `Str s' -> Pervasives.compare s s' | `Str _, _ -> 1 | _, `Str _ -> -1
    | `StrT, `StrT -> 0 | `StrT, _ -> 1 | _, `StrT -> 1
    | `Num n, `Num n' -> Pervasives.compare n n' | `Num _, _ -> 1 | _, `Num _ -> -1
    | `NumT, `NumT -> 0 | `NumT, _ -> 1 | _, `NumT -> -1
    | `True, `True -> 0 | `True, _ -> 1 | _, `True -> -1
    | `False, `False -> 0 | `False, _ -> 1 | _, `False -> -1
    | `BoolT, `BoolT -> 0 | `BoolT, _ -> 1 | _, `BoolT -> -1
    | `Null, `Null -> 0 | `Null, _ -> 1 | _, `Null -> -1
    | `Undef, `Undef -> 0 | `Undef, _ -> 1 | _, `Undef -> -1
    | `Clos (e, l, exp), `Clos (e', l', exp') ->
      order_concat [lazy (Env.compare e e');
                    lazy (compare_list Pervasives.compare l l');
                    lazy (Pervasives.compare exp exp')]
    | `Clos _, _ -> 1 | _, `Clos _ -> -1
    | `ClosT, `ClosT -> 0 | `ClosT, _ -> 1 | _, `ClosT -> -1
    | `Obj addrs, `Obj addrs' -> ObjAddressSet.compare addrs addrs'
    | `Obj _, _ -> 1 | _, `Obj _ -> -1
    | `Nullable v, `Nullable v' -> compare v v'
    | `Nullable _, _ -> 1
    | _, `Nullable _ -> -1
    | `Bot, `Bot -> 0

  let join (x : t) (y : t) : t = if compare x y = 0 then x else
      match x, y with
      | `Top, _ | _, `Top -> `Top
      | `Str _, `Str _ | `StrT, `Str _ | `Str _, `StrT | `StrT, `StrT -> `StrT
      | `Num _, `Num _ | `NumT, `Num _ | `Num _, `NumT -> `NumT
      | `True, `False | `False, `True | `BoolT, `True | `True, `BoolT
      | `BoolT, `False | `False, `BoolT | `BoolT, `BoolT -> `BoolT
      | `Clos _, `Clos _ | `ClosT, `Clos _ | `Clos _, `ClosT | `ClosT, `ClosT ->
        Printf.printf "\027[31mJoining two closures: %s and %s\027[0m\n%!"
          (to_string x) (to_string y);
        `ClosT
      | `Obj addrs, `Obj addrs' -> `Obj (ObjAddressSet.join addrs addrs')
      | `Nullable v, `Null | `Null, `Nullable v -> `Nullable v
      | `Null, v | v, `Null -> `Nullable v
      | `Bot, v | v, `Bot -> v
      | _, _ ->
        Printf.printf "\027[31mJoining two incompatible values: %s and %s\027[0m\n%!"
          (to_string x) (to_string y);
        `Top

  let aval : t -> t = function
    | `Top -> `Top
    | `Str s -> `Str s
    | `StrT -> `StrT
    | `Num _ | `NumT -> `NumT
    | `True -> `True
    | `False -> `False
    | `BoolT -> `BoolT
    | `Null -> `Null
    | `Undef -> `Undef
    | `Clos c -> `Clos c
    | `ClosT -> `ClosT
    | `Obj a -> `Obj a
    | `Nullable t -> `Nullable t
    | `Bot -> `Bot
end
