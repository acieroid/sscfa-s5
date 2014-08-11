open Shared
open Lattice

module AddrMap = BatMap.Make(Address)

module type Store_signature =
  sig
    type elt
    type t
    val empty : t
    val join : Address.t -> elt -> t -> t
    val lookup : Address.t -> t -> elt
   (* Keep only addresses in the given list *)
    val restrict : Address.t list -> t -> t
    val compare : t -> t -> int
    val size : t -> int
    val to_string : t -> string
  end

module type StoreArg =
sig
  type t
  val compare : t -> t -> int
  val join : t -> t -> t
  val to_string : t -> string
end

module Make =
  functor(Elt : StoreArg) ->
  struct
    type elt = Elt.t
    type t = elt AddrMap.t

    let empty = AddrMap.empty

    let join a v store =
      if AddrMap.mem a store then
        AddrMap.add a (Elt.join (AddrMap.find a store) v) store
      else
        AddrMap.add a v store

    let lookup = AddrMap.find

    let restrict addrs =
      AddrMap.filter (fun a _ ->
          if (List.mem a addrs) then begin
            print_string ("reclaim(" ^ (Address.to_string a) ^ ")");
            print_newline ();
            true
          end
          else
            false)

    let compare = AddrMap.compare Elt.compare

    let size = AddrMap.cardinal

    let to_string =
      string_of_map AddrMap.fold Address.to_string Elt.to_string
  end

module ValueStore = Make(AValue)

module ObjValue =
struct
  type t = [`Obj of Obj_val.t | `ObjT]
  let compare x y = failwith "TODO"
  let join x y = match x, y with
    | `Obj o, `Obj o' ->
      if Obj_val.compare o o' then
        `Obj o
      else
        `ObjT
    | `ObjT, _ | _, `ObjT -> `ObjT
  let to_string = function
    | `ObjT -> "ObjTop"
    | `Obj o -> Obj_val.to_string o
end

module ObjectStore = Make(ObjValue)
