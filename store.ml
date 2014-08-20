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
   (* Keep only addresses in the given set *)
    val restrict : AddressSet.t -> t -> t
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
  val print_reclaim : Address.t -> unit
  val print_join : Address.t -> t -> t -> unit
end

module Make =
  functor(Elt : StoreArg) ->
  struct
    type elt = Elt.t
    type t = elt AddrMap.t

    let empty = AddrMap.empty

    let join a v store =
      if AddrMap.mem a store then begin
        Elt.print_join a v (AddrMap.find a store);
        AddrMap.add a (Elt.join (AddrMap.find a store) v) store
      end
      else
        AddrMap.add a v store

    let set a v store =
      (* Strong update. TODO: use abstract counting and only join, no set *)
      AddrMap.add a v store

    let lookup = AddrMap.find

    let restrict addrs =
      AddrMap.filter (fun a _ ->
          if (AddressSet.mem a addrs) then
            true
          else begin
            Elt.print_reclaim a;
            false
          end)

    let compare = AddrMap.compare Elt.compare

    let size = AddrMap.cardinal

    let to_string =
      string_of_map AddrMap.fold Address.to_string Elt.to_string
  end

module ValueArg = struct
  include AValue
  let print_reclaim a =
    print_endline ("\027[32mvalue_reclaim(" ^ (Address.to_string a) ^ ")\027[0m")
  let print_join a v1 v2 =
    print_endline ("\027[31mJoining values: " ^ (to_string v1) ^ " and " ^ (to_string v2) ^ 
                   " at location " ^ (Address.to_string a) ^ "\027[0m")
end

module ValueStore = Make(ValueArg)

module ObjValue =
struct
  type t = [`Obj of Obj_val.t | `ObjT]
  let compare = Obj_val.compare
  let join x y = match x, y with
    | `Obj o, `Obj o' ->
      if compare o o' == 0 then
        `Obj o
      else
        `ObjT
    | `ObjT, _ | _, `ObjT -> `ObjT
  let to_string = function
    | `ObjT -> "ObjTop"
    | `Obj o -> Obj_val.to_string o
  let print_reclaim a =
    print_endline ("\027[32mobject_reclaim(" ^ (Address.to_string a) ^ ")\027[0m")
  let print_join a v1 v2 =
    print_endline ("\027[31mJoining objects: " ^ (to_string v1) ^ " and " ^ (to_string v2) ^ 
                   " at location " ^ (Address.to_string a) ^ "\027[0m")
end

module ObjectStore = Make(ObjValue)
