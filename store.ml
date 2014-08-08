open Shared
open Lattice

module type Store_signature =
  sig
    type t
    val empty : t
    val join : Address.t -> AValue.t -> t -> t
    val lookup : Address.t -> t -> AValue.t
   (* Keep only addresses in the given list *)
    val restrict : Address.t list -> t -> t
    (* val compare : t -> t -> int *)
    val size : t -> int
    val to_string : t -> string
  end

(* S5 uses Store module (util/store.ml) *)
module Store : Store_signature =
  struct
    module AddrMap = BatMap.Make(Address)

    type t = AValue.t AddrMap.t

    let empty = AddrMap.empty

    let join a v store =
      if AddrMap.mem a store then
        AddrMap.add a (AValue.join (AddrMap.find a store) v) store
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

    (* let compare = AddrMap.compare L.compare *)

    let size = AddrMap.cardinal

    let to_string =
      string_of_map AddrMap.fold Address.to_string AValue.string_of
  end
