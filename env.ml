open Shared

module type Env_signature =
  sig
    type t
    val empty : t
    val extend : string -> Address.t -> t -> t
    val lookup : string -> t -> Address.t
    val compare : t -> t -> int
    val size : t -> int
    val to_string : t -> string
    val subsumes : t -> t -> bool
  end

(* S5 uses a map of identifier *)
module Env : Env_signature =
  struct
    module StringMap = BatMap.Make(BatString)

    type t = Address.t StringMap.t

    let empty = StringMap.empty

    let extend = StringMap.add

    let lookup = StringMap.find

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
  end
