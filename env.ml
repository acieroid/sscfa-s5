open Shared
open Prelude

module type Env_signature =
  sig
    type t
    val empty : t
    val extend : string -> Address.t -> t -> t
    val contains : string -> t -> bool
    val lookup : string -> t -> Address.t
    val keep : IdSet.t -> t -> t
    val compare : t -> t -> int
    val size : t -> int
    val to_string : t -> string
    val subsumes : t -> t -> bool
    val domain : t -> IdSet.t
    val range : t -> AddressSet.t
  end

(* S5 uses a map of identifier *)
module Env : Env_signature =
  struct
    module StringMap = BatMap.Make(BatString)

    type t = Address.t StringMap.t

    let empty = StringMap.empty

    let extend = StringMap.add

    let contains = StringMap.mem

    let lookup = StringMap.find

    let keep vars = StringMap.filter (fun var _ -> IdSet.mem var vars)

    let compare = StringMap.compare Address.compare

    let size = StringMap.cardinal

    let to_string env = String.concat ", "
        (BatList.map (fun (v, a) -> v ^ ": " ^ (Address.to_string a))
           (StringMap.bindings env))

    let subsumes e1 e2 =
      let merge_val _ v1 v2 =
        match v1, v2 with
        | Some x, Some y when x = y -> None
        | Some _, Some _ -> v2
        | None, Some _ -> v2
        | Some _, None -> None
        | None, None -> None in
      StringMap.is_empty (StringMap.merge merge_val e1 e2)

    (* urr *)
    let domain env = IdSet.from_list (BatList.of_enum (StringMap.keys env))
    let range env = AddressSet.of_enum (StringMap.values env)
  end
