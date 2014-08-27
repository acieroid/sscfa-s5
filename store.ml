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
    val contains : Address.t -> t -> bool
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
    type count =
      | One
      | Infinity
    type elt = Elt.t * count
    type t = elt AddrMap.t

    let empty = AddrMap.empty

    let join (a : Address.t) (v : Elt.t) (store : t)  =
      if AddrMap.mem a store then begin
        let (v', count) = AddrMap.find a store in
        print_endline ("\027[31mJoining values: " ^ (Elt.to_string v) ^
                       " and " ^ (Elt.to_string v') ^
                       " at location " ^ (Address.to_string a) ^ "\027[0m");
        AddrMap.add a ((Elt.join v v'), Infinity) store
      end
      else
        AddrMap.add a (v, One) store

    let set (a : Address.t) (v : Elt.t) (store : t) =
      if AddrMap.mem a store then
        let (v', count) = AddrMap.find a store in
        match count with
        | One -> AddrMap.add a (v, One) store (* strong update *)
        | Infinity -> join a v store
      else
        AddrMap.add a (v, One) store

    let lookup (a : Address.t) (store : t) =
      let (v, _) = AddrMap.find a store in
      v

    let contains (a : Address.t) (store : t) =
      AddrMap.mem a store

    let restrict (addrs : AddressSet.t) : t -> t =
      AddrMap.filter (fun a _ ->
          if not (Address.is_reclaimable a) || (AddressSet.mem a addrs) then
            true
          else begin
            print_endline ("\027[32mreclaim(" ^ (Address.to_string a) ^ ")\027[0m");
            false
          end)

    let compare : t -> t -> int =
      AddrMap.compare (fun (v, c) (v', c') ->
          order_concat [lazy (Elt.compare v v');
                        lazy (Pervasives.compare c c')])

    let size : t -> int = AddrMap.cardinal

    let to_string : t -> string =
      string_of_map AddrMap.fold Address.to_string (fun (v, _) -> Elt.to_string v)
  end

module ValueStore = Make(AValue)

module ObjValue =
struct
  type t = [`Obj of Obj_val.t | `ObjT]
  let compare x y = match x, y with
    | `ObjT, `ObjT -> 0
    | `ObjT, _ -> 1
    | _, `ObjT -> -1
    | `Obj o, `Obj o' -> Obj_val.compare o o'
  let join x y = match x, y with
    | `Obj o, `Obj o' ->
      if Obj_val.compare o o' == 0 then
        `Obj o
      else
        `ObjT
    | `ObjT, _ | _, `ObjT -> `ObjT
  let to_string = function
    | `ObjT -> "ObjTop"
    | `Obj o -> Obj_val.to_string o
end

module ObjectStore = Make(ObjValue)
