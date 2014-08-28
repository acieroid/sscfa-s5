open Shared
open Prelude

module type Env_signature =
  sig
    (** Type of the environment itself *)
    type t

    (** The empty environment *)
    val empty : t

    (** Add a mapping to the environment *)
    val extend : string -> Address.t -> t -> t

    (** Check whether the environment contains a mapping for the given name *)
    val contains : string -> t -> bool

    (** Fetch the address of a name in the environment, raising Not_found if no
        such mapping exist *)
    val lookup : string -> t -> Address.t

    (** Keep only the mappings corresponding to the names in the given set *)
    val keep : IdSet.t -> t -> t

    (** Compare two environments *)
    val compare : t -> t -> int

    (** Gives the number of bindings stored in this environment *)
    val size : t -> int

    (** Give a string representation of this environment *)
    val to_string : t -> string

    (** Check whether an environment subsumes another *)
    val subsumes : t -> t -> bool

    (** Extract the domain of the environment (that is, the set of names) *)
    val domain : t -> IdSet.t

    (** Extract the range of the environment (that is, the set of addresses) *)
    val range : t -> AddressSet.t

    (** Merge two environments together, giving priority to values from the
        first environment *)
    val merge : t -> t -> t
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

    let merge e1 e2 =
      let merge_val _ v1 v2 =
        match v1, v2 with
        | Some x, _ | None, Some x -> Some x
        | None, None -> None in
      StringMap.merge merge_val e1 e2
  end
