open Shared
open Prelude

let m = 1

type allocation_strategy = [ `MCFA | `PSKCFA ]

module type Env_signature =
  sig
    (** Type of the environment itself *)
    type t

    (** The empty environment *)
    val empty : t

    (** Add a mapping to the environment *)
    val extend : string -> VarAddress.t -> t -> t

    (** Check whether the environment contains a mapping for the given name *)
    val contains : string -> t -> bool

    (** Fetch the address of a name in the environment, raising Not_found if no
        such mapping exist *)
    val lookup : string -> t -> VarAddress.t

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
    val range : t -> VarAddressSet.t

    (** Merge two environments together, giving priority to values from the
        first environment *)
    val merge : t -> t -> t

    (* Some parameters that are stack-properties are stored in the environment,
       as the environment is itself a stack property: it is modified at function
       application and restored at the end of a function application *)

    (** Store the call site in the environment (for m-CFA) *)
    val call : Pos.t -> t -> t

    (** Change the allocation strategy *)
    val set_alloc : allocation_strategy -> t -> t
  end

(* S5 uses a map of identifier *)
module Env =
  struct
    module StringMap = BatMap.Make(BatString)

    type t = {
      env : VarAddress.t StringMap.t;
      call : Pos.t list;
      strategy : allocation_strategy;
    }

    let empty = {env = StringMap.empty; call = []; strategy = `MCFA}

    let extend id a e = {e with env = StringMap.add id a e.env}

    let contains id e = StringMap.mem id e.env

    let lookup id e = StringMap.find id e.env

    let keep vars e =
      { e with env = StringMap.filter (fun var _ -> IdSet.mem var vars) e.env}

    let compare e e' =
      order_concat [lazy (compare_list Pos.compare e.call e'.call);
                    lazy (Pervasives.compare e.strategy e'.strategy);
                    lazy (StringMap.compare VarAddress.compare e.env e'.env)]


    let size e = StringMap.cardinal e.env

    let to_string e = String.concat ", "
        (BatList.map (fun (v, a) -> v ^ ": " ^ (VarAddress.to_string a))
           (StringMap.bindings e.env))

    let subsumes e1 e2 =
      let merge_val _ v1 v2 =
        match v1, v2 with
        | Some x, Some y when x = y -> None
        | Some _, Some _ -> v2
        | None, Some _ -> v2
        | Some _, None -> None
        | None, None -> None in
      StringMap.is_empty (StringMap.merge merge_val e1.env e2.env)

    (* urr *)
    let domain e = IdSet.from_list (BatList.of_enum (StringMap.keys e.env))

    let range e = VarAddressSet.of_enum (StringMap.values e.env)

    let merge e1 e2 =
      let merge_val _ v1 v2 =
        match v1, v2 with
        | Some x, _ | None, Some x -> Some x
        | None, None -> None in
      {e1 with env = StringMap.merge merge_val e1.env e2.env}

    let call p env =
      {env with call = BatList.take m (p :: env.call)}

    let set_alloc strategy env =
      {env with strategy = strategy}
  end
