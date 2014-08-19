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
end

module Make =
  functor(Elt : StoreArg) ->
  struct
    type elt = Elt.t
    type t = elt AddrMap.t

    let empty = AddrMap.empty

    let join a v store =
      if AddrMap.mem a store then begin
        print_endline ("Joining: " ^ (Elt.to_string v) ^ " and " ^
                      (Elt.to_string (AddrMap.find a store)) ^
                      " at location " ^ (Address.to_string a));
        AddrMap.add a (Elt.join (AddrMap.find a store) v) store
      end
      else
        AddrMap.add a v store

    let set a v store =
      (* Strong update. TODO: use abstract counting and only join, no set *)
      AddrMap.add a v store

    let lookup = AddrMap.find

    let restrict addrs =
      print_endline ("Keep only: " ^ (string_of_list (AddressSet.to_list addrs) Address.to_string));
      AddrMap.filter (fun a _ ->
          if (AddressSet.mem a addrs) then
            true
          else begin
            print_endline ((Address.to_string a) ^ " \027[31mnot in\027[0m " ^  (string_of_list (AddressSet.to_list addrs) Address.to_string));
            print_endline ("\027[31mreclaim(" ^ (Address.to_string a) ^ ")\027[0m");
            false
          end)

    let compare = AddrMap.compare Elt.compare

    let size = AddrMap.cardinal

    let to_string =
      string_of_map AddrMap.fold Address.to_string Elt.to_string
  end

module ValueStore = Make(AValue)

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
end

module ObjectStore = Make(ObjValue)
