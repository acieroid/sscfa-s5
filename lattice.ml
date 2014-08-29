(* This file is a modified version of the lattices in labichn's LambdaS5 fork,
   (src/analyses/aam/aam_lattice.ml), commit 8a9078569d, available at
   https://github.com/labichn/LambdaS5

   The main differences are:
     - the Delay lattice is removed because it is unnecessary to us

   Some notes:
     - thanks to the use of polymorphic variants, one does not need a
       concretization function to access the element stored in a lattice value,
       but just has to pattern match on the variant (eg. if you want to access a
       closure, just pattern match against `Clos)
 *)

(*
  The only module here expected to be used externally is AValue (at the
  bottom). It implements LATTICE and provides abstract value creation
  functions, joins, singleton and subsumption predicates, and string
  representation for abstractions of λS5 values.

  AValue's lattices are somewhat plug-and-play. There are three places that must
  be touched to change one of the primtype's lattice:
  - AValueT's must include X lattice's XT.t module's type in its 'a t union
  - AValueF's concrete primtype modules must call X lattice's XF functor
  - AValueF's creator for the primtype begin changed must create an XT.t
  and you're good to go.

  Many thanks go out to Jacques Garrigue and his solution to the Expression
  Problem in OCaml; without it I would still have three extra constructors
  around all of my values.
*)
open Env
open Shared
module SYN = Ljs_syntax

module type LATTYPE = sig type t end

module type VLATTICE = sig
  include LATTYPE

  (** joins two abstract values together *)
  val join: t -> t -> t

  (** whether the given abstract value's extensional representation is a
      finite  *)
  val singletonp: t -> bool

  (** does [v] subsume [v'], i.e. v' ⊑ v *)
  val subsumes: t -> t -> bool

  (** returns a string representation of the given abstract value *)
  val to_string: t -> string

  (** returns the nearest top value *)
  val to_top: t -> t

end
module Types(X : sig type t type a end) = struct type t = X.t type a = X.a end

module BoolT = struct type t = [ `True | `False | `BoolT ] end
module type BoolS = sig
  type t0 = private [> BoolT.t]
  include VLATTICE with type t = t0
end
module BoolF(L : BoolS) = struct
  type t0 = BoolT.t
  type t = L.t
  (* yes, having verbose annotations before every argument in the
     definitions is a pain, but not nearly as bad as three layers of
     type constructors for each use of an avalue... *)
  let join ((`True | `False | `BoolT) as b : t0)
      ((`True | `False | `BoolT) as b' : t0) : t = match b, b' with
    | `True, `True | `False, `False -> b
    | _ -> `BoolT
  let singletonp ((`True | `False | `BoolT) as b : t0) : bool =
    match b with `True | `False -> true | _ -> false
  let subsumes ((`True | `False | `BoolT) as b : t0)
      ((`True | `False | `BoolT) as b' : t0) = match b, b' with
    | `BoolT, _ -> true | b, b' when b = b' -> true | _ -> false
  let to_string ((`True | `False | `BoolT) as b : t0) = match b with
    | `True -> "true" | `False -> "false" | `BoolT -> "boolT"
  let to_top ((`True | `False | `BoolT) : t0) = `BoolT
end

type env = Env.t
module ClosT = struct
  type t = [ `Clos of env * Prelude.id list * SYN.exp | `ClosT ]
end
module type ClosS = sig
  type t0 = private [> ClosT.t]
  include VLATTICE with type t = t0
end
module ClosF(L : ClosS) = struct
  type t0 = ClosT.t
  type t = L.t
  let join ((`Clos _ | `ClosT) as c : t0)
      ((`Clos _ | `ClosT) as c' : t0) : t =
    if c = c' then c else `ClosT
  let singletonp ((`Clos _ | `ClosT) as c : t0) =
    match c with `Clos _ -> true | _ -> false
  let subsumes ((`Clos _ | `ClosT) as c : t0)
      ((`Clos _ | `ClosT) as c' : t0) = match c, c' with
      | `ClosT, _ -> true
      | `Clos (env, xs, exp), `Clos (env', xs', exp') ->
        Env.subsumes env env' && xs = xs' && compare exp exp' = 0
      | _ -> false
  let to_string ((`Clos _ | `ClosT) as c : t0) : string = match c with
    | `Clos (env, xs, exp) ->
      "clos("^
        (string_of_list xs (fun x -> x))^", "^
        (string_of_exp exp)^")"
    | `ClosT -> "closT"
  let to_top ((`Clos _ | `ClosT) : t0) = `ClosT
end

type addr = Address.t
module ObjT = struct type t = [ `Obj of addr | `ObjT ] end
module type ObjS = sig
  type t0 = private [> ObjT.t]
  include VLATTICE with type t = t0
end
module ObjF(L : ObjS) = struct
  type t0 = ObjT.t
  type t = L.t
  let join ((`Obj _ | `ObjT) as o : t0)
      ((`Obj _ | `ObjT) as o' : t0): t =
    if o = o' then o else `ObjT
  let singletonp ((`Obj _ | `ObjT) as o : t0) =
    match o with `Obj _ -> true | _ -> false
  let subsumes ((`Obj _ | `ObjT) as o : t0)
      ((`Obj _ | `ObjT) as o' : t0) : bool =
    match o, o' with `ObjT, _ -> true | _ -> o = o'
  let to_string ((`Obj _ | `ObjT) as o : t0) = match o with
    | `Obj a -> "obj"^(Address.to_string a)
    | `ObjT -> "objT"
  let to_top ((`Obj _ | `ObjT) : t0) = `ObjT
end

module ConstNumT = struct type t = [ `Num of float | `NumT ] end
module type ConstNumS = sig
  type t0 = private [> ConstNumT.t]
  include VLATTICE with type t = t0
end
module ConstNumF(L : ConstNumS) = struct
  type t0 = ConstNumT.t
  type t = L.t
  let join ((`Num _ | `NumT) as n : t0)
      ((`Num _ | `NumT) as n' : t0) : t =
    if n = n' then n else `NumT
  let singletonp ((`Num _ | `NumT) as n : t0) =
    match n with `Num _ -> true | _ -> false
  let subsumes ((`Num _ | `NumT) as n : t0)
      ((`Num _ | `NumT) as n' : t0) =
    match n, n' with `NumT, _ -> true | _ -> compare n n' = 0
  let to_string ((`Num _ | `NumT) as n : t0) : string =
    match n with `Num f -> string_of_float f | `NumT -> "numT"
  let to_top ((`Num _ | `NumT)  : t0) = `NumT
end

module ConstStrT = struct type t = [ `Str of string | `StrT ] end
module type ConstStrS = sig
  type t0 = private [> ConstStrT.t]
  include VLATTICE with type t = t0
end
module ConstStrF(L : ConstStrS) = struct
  type t0 = ConstStrT.t
  type t = L.t
  let join ((`Str _ | `StrT) as s : t0)
      ((`Str _ | `StrT) as s' : t0) : t =
    if s = s' then s else `StrT
  let singletonp ((`Str _ | `StrT) as s : t0) =
    match s with `Str _ -> true | _ -> false
  let subsumes ((`Str _ | `StrT) as s : t0)
      ((`Str _ | `StrT) as s' : t0) =
    match s, s' with `StrT, _ -> true | _ -> s = s'
  let to_string ((`Str _ | `StrT) as s : t0) : string =
    match s with `Str s -> "'"^s^"'" | `StrT -> "stringT"
  let to_top ((`Str _ | `StrT) : t0) = `StrT
end

module NullT = struct type t = [ `Null ] end
module type NullS = sig
  type t0 = private [> NullT.t]
  include VLATTICE with type t = t0
end
module NullF(L : NullS) = struct
  type t0 = NullT.t
  type t = L.t
  let join (`Null : t0) (`Null : t0): t = `Null
  let singletonp (`Null : t0) = true
  let subsumes (`Null : t0) (`Null : t0) : bool = true
  let to_string (`Null : t0) = "null"
  let to_top (`Null : t0) = `Null
end

module UndefT = struct type t = [ `Undef ] end
module type UndefS = sig
  type t0 = private [> UndefT.t]
  include VLATTICE with type t = t0
end
module UndefF(L : UndefS) = struct
  type t0 = UndefT.t
  type t = L.t
  let join (`Undef : t0) (`Undef : t0): t = `Undef
  let singletonp (`Undef : t0) = true
  let subsumes (`Undef : t0) (`Undef : t0) : bool = true
  let to_string (`Undef : t0) = "undef"
  let to_top (`Undef : t0) = `Undef
end

module AValueT = struct
  type 'a t =
    (* To change a lattice, just swap out one of these types... *)
    [ BoolT.t | ConstNumT.t | UndefT.t | NullT.t | ConstStrT.t | ClosT.t |
      ObjT.t | `Top | `Bot ]
  let compare = Pervasives.compare
end
module type AValueS = sig
  type t0 = private [> a AValueT.t]
  and a = <t:t0>
  include VLATTICE with type t = t0
  val compare: t -> t -> int

  val bool: bool -> t
  val clos: env -> Prelude.id list -> SYN.exp -> t
  val num: float -> t
  val obj: addr -> t
  val str: string -> t
end
module AValueF
  (L : AValueS)
   =
  struct
    type t0 = L.a AValueT.t
    include Types(L)

    (* swap one of these functors...
                     |
                     v *)
    module   Bool = BoolF(L)
    module   Clos = ClosF(L)
    module   Null = NullF(L)
    module    Num = ConstNumF(L)
    module    Obj = ObjF(L)
    module String = ConstStrF(L)
    module  Undef = UndefF(L)

    (* and swap one of these creators, then you're done! *)
    let bool (b : bool) = if b then `True else `False
    let clos (env : env) (xs : Prelude.id list) (exp : SYN.exp) =
      `Clos (env, xs, exp)
    let num (f : float) = `Num f
    let obj (a : addr) = `Obj a
    let str (s : string) = `Str s
    let top : t = `Top

    let join (v : t) (v' : t) : t = match v, v' with
      | v, `Bot | `Bot, v -> v
      |   (#Bool.t0 as b),   (#Bool.t0 as b') ->   Bool.join b b'
      |   (#Clos.t0 as c),   (#Clos.t0 as c') ->   Clos.join c c'
      |   (#Null.t0 as n),   (#Null.t0 as n') ->   Null.join n n'
      |    (#Num.t0 as n),    (#Num.t0 as n') ->    Num.join n n'
      |    (#Obj.t0 as o),    (#Obj.t0 as o') ->    Obj.join o o'
      | (#String.t0 as s), (#String.t0 as s') -> String.join s s'
      |  (#Undef.t0 as u),  (#Undef.t0 as u') ->  Undef.join u u'
      | _ -> `Top

    let singletonp (v : t) : bool = match v with
      |   #Bool.t0 as b ->   Bool.singletonp b
      |   #Clos.t0 as c ->   Clos.singletonp c
      |    #Obj.t0 as o ->    Obj.singletonp o
      |   #Null.t0 as n ->   Null.singletonp n
      |    #Num.t0 as n ->    Num.singletonp n
      | #String.t0 as s -> String.singletonp s
      |  #Undef.t0 as u ->  Undef.singletonp u
      | _ -> false

    let subsumes (v : t) (v' : t) : bool = match v, v' with
      | `Top, _ | _, `Bot -> true
      |   (#Bool.t0 as b),   (#Bool.t0 as b') ->   Bool.subsumes b b'
      |   (#Clos.t0 as c),   (#Clos.t0 as c') ->   Clos.subsumes c c'
      |   (#Null.t0 as n),   (#Null.t0 as n') ->   Null.subsumes n n'
      |    (#Num.t0 as n),    (#Num.t0 as n') ->    Num.subsumes n n'
      |    (#Obj.t0 as o),    (#Obj.t0 as o') ->    Obj.subsumes o o'
      | (#String.t0 as s), (#String.t0 as s') -> String.subsumes s s'
      |  (#Undef.t0 as u),  (#Undef.t0 as u') ->  Undef.subsumes u u'
      | _ -> false

    let to_string (v : t) : string = match v with
      | `Top -> "T" | `Bot -> "_|_"
      |   #Bool.t0 as b ->   Bool.to_string b
      |   #Clos.t0 as c ->   Clos.to_string c
      |   #Null.t0 as n ->   Null.to_string n
      |    #Num.t0 as n ->    Num.to_string n
      |    #Obj.t0 as o ->    Obj.to_string o
      | #String.t0 as s -> String.to_string s
      |  #Undef.t0 as u ->  Undef.to_string u
      | _ -> failwith "somehow fell through AValue's to_string"
     (* ^ Why is this last case needed? Isn't the function complete? *)

    let to_top (v : t) : t = match v with
      | `Top -> `Top | `Bot -> `Top
      |   #Bool.t0 as b ->   Bool.to_top b
      |   #Clos.t0 as c ->   Clos.to_top c
      |   #Null.t0 as n ->   Null.to_top n
      |    #Num.t0 as n ->    Num.to_top n
      |    #Obj.t0 as o ->    Obj.to_top o
      | #String.t0 as s -> String.to_top s
      |  #Undef.t0 as u ->  Undef.to_top u
      | _ -> failwith "somehow fell through AValue's to_top"

    let compare = Pervasives.compare

  end
module type AValueFixpoint = sig
  type t0 = a AValueT.t
  and a = <t:t0>
  include VLATTICE with type t = t0
  val compare: t -> t -> int
  val bool: bool -> t
  val clos: env -> Prelude.id list -> SYN.exp -> t
  val num: float -> t
  val obj: addr -> t
  val str: string -> t
end
module rec AValue : AValueFixpoint = AValueF(AValue)
