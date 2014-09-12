open Shared
open Lattice

module type StoreArg =
sig
  type t
  val compare : t -> t -> int
  val join : t -> t -> t
  val to_string : t -> string
end

module Make =
  functor (Address : AddressSignature) ->
  functor (Value : StoreArg) ->
  struct
    module AddrMap = BatMap.Make(Address)
    module AddressSet = BatSet.Make(Address)

    type count =
      | One
      | Infinity
    type elt = Value.t * count
    type t = elt AddrMap.t

    let empty = AddrMap.empty

    let join (a : Address.t) (v : Value.t) (store : t)  =
      if AddrMap.mem a store then begin
        let (v', count) = AddrMap.find a store in
        print_endline ("\027[31mJoining values: " ^ (Value.to_string v) ^
                       " and " ^ (Value.to_string v') ^
                       " at location " ^ (Address.to_string a) ^ "\027[0m");
        AddrMap.add a ((Value.join v v'), Infinity) store
      end
      else
        AddrMap.add a (v, One) store

    let set (a : Address.t) (v : Value.t) (store : t) =
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
          order_concat [lazy (Value.compare v v');
                        lazy (Pervasives.compare c c')])

    let size : t -> int = AddrMap.cardinal

    let to_string : t -> string =
      string_of_map AddrMap.fold Address.to_string (fun (v, _) -> Value.to_string v)

    let merge e1 e2 =
      let merge_val _ v1 v2 =
        match v1, v2 with
        | Some x, _ | None, Some x -> Some x
        | None, None -> None in
      AddrMap.merge merge_val e1 e2
  end

module ValueStore = Make(VarAddress)(AValue)

module ObjectStore = struct
  module O = Obj_val
  module NormalObjectStore = Make(ObjAddress)(O)
  include NormalObjectStore

  let join (a : ObjAddressSet.t) (o : O.t) (store : t) : t =
    (* joins at all the addresses *)
    ObjAddressSet.fold (fun addr s -> NormalObjectStore.join addr o s) a store

  let set (a : ObjAddressSet.t) (o : O.t) (store : t) : t =
    ObjAddressSet.fold (fun addr s -> NormalObjectStore.set addr o s) a store

  let contains (a : ObjAddressSet.t) (store : t) : bool =
    (* store contains the address set if it contains each address of the set *)
    ObjAddressSet.fold (fun addr res ->
        res && NormalObjectStore.contains addr store)
      a true

  let lookup (a : ObjAddressSet.t) (store : t) : O.t =
    (* join all the objects pointed to and returns only one *)
    match BatList.map (fun addr -> NormalObjectStore.lookup addr store)
            (ObjAddressSet.elements a) with
    | [] -> failwith "lookup: empty ObjAddressSet"
    | hd :: [] -> hd
    | hd :: tl -> BatList.fold_left Obj_val.join hd tl

  let restrict (a : ObjAddressSet.t) (store : t) : t =
    NormalObjectStore.restrict a store
end
