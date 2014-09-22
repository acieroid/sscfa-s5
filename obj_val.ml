open Prelude
open Lattice

(* TODO: this is duplicated from shared.ml *)
let order_comp x y =
  if x = 0 then y else x

let order_concat l =
  let rec aux last = function
    | [] -> last
    | (h::t) ->
      if last <> 0 then last else aux (order_comp last (Lazy.force h)) t
  in aux 0 l

module S = Ljs_syntax

type attrs = {
  code : value; (* callable (closure or object) *)
  proto : value; (* object *)
  primval : value; (* any value *)
  klass : value; (* string? *)
  extensible : value; (* boolean *)
}
and data = {
  value : value; (* any value *)
  writable : value; (* boolean *)
}
and accessor = {
  getter : value; (* callable *)
  setter : value; (* callable *)
}
and prop =
  | Data of data * value * value (* enum & config are booleans *)
  | Accessor of accessor * value * value (* same *)
and t = attrs * (prop IdMap.t)
(* a StackObj is an object that lives on the stack, it avoids allocating
   too much objects and allows to use identifiers for the objects' addresses
   (which is not possible on anonymous objects) *)
and value = [ `A of AValue.t | `StackObj of t ]

let rec compare_value (x : value) (y : value) = match x, y with
  | `A v, `A v' -> AValue.compare v v'
  | `A _, _ -> 1
  | _, `A _ -> -1
  | `StackObj o, `StackObj o' -> compare o o'
and compare ((attrs, props) : t) ((attrs', props') : t) =
  order_concat [lazy (compare_value attrs.code attrs'.code);
                lazy (compare_value attrs.proto attrs'.proto);
                lazy (compare_value attrs.primval attrs'.primval);
                lazy (compare_value attrs.klass attrs'.klass);
                lazy (compare_value attrs.extensible attrs'.extensible);
                lazy (IdMap.compare prop_compare props props')]
and prop_compare x y = match x, y with
  | Data ({value = v; writable = w}, enum, config),
    Data ({value = v'; writable = w'}, enum', config') ->
    order_concat [lazy (compare_value v v');
                  lazy (compare_value w w');
                  lazy (compare_value enum enum');
                  lazy (compare_value config config')]
  | Data _, _ -> 1
  | _, Data _ -> -1
  | Accessor ({getter = g; setter = s}, enum, config),
    Accessor ({getter = g'; setter = s'}, enum', config') ->
    order_concat [lazy (compare_value g g');
                  lazy (compare_value s s');
                  lazy (compare_value enum enum');
                  lazy (compare_value config config')]

let string_of_map fold k v m =
  "{" ^ (String.concat "\n"
           (fold (fun k' v' a -> ((k k') ^ ": " ^ (v v')) :: a) m [])) ^ "}"

let rec to_string ((attrs, props) : t) =
  "Obj(" ^
  (string_of_map IdMap.fold (fun x -> x) string_of_prop props) ^ ")"
and string_of_value = function
  | `A v -> AValue.to_string v
  | `StackObj o -> "StackObj(" ^ (to_string o) ^ ")"
and string_of_prop : prop -> string = function
  | Data ({value = v; _}, _, _) ->
    "Data(" ^ (string_of_value v) ^ ")"
  | Accessor ({getter = g; setter = s}, _, _) ->
    "Accessor(" ^ (string_of_value g) ^ ", " ^ (string_of_value s) ^ ")"

(* TODO: should use AValue.compare, as its definition could change *)
let compare : t -> t -> int = Pervasives.compare

let set_attr_str ((attrs, props) : t) (attr : string) (value : value) =
  match attr with
  | "proto" -> ({ attrs with proto = value }, props)
  | "code" -> ({ attrs with code = value }, props)
  | "prim" -> ({ attrs with primval = value }, props)
  | _ -> failwith ("Invalid attr for object: " ^ attr)

let set_prop ((attrs, props) : t) (prop : string) (value : prop) =
  (attrs, IdMap.add prop value props)

let has_prop ((attrs, props) : t) (prop : string) : bool =
  IdMap.mem prop props

let lookup_prop ((attrs, props) : t) (prop : string) : prop =
  IdMap.find prop props

let remove_prop ((attrs, props) : t) (prop : string) : t =
  (attrs, IdMap.remove prop props)

(* Mostly taken from Ljs_eval.get_attr *)
let get_attr ((attrs, props) : t) (attr : S.pattr) (field : string) : value =
  if not (IdMap.mem field props) then
    (`A `Undef)
  else begin match (IdMap.find field props), attr with
    | Data (_, _, config), S.Config
    | Accessor (_, _, config), S.Config -> config
    | Data (_, enum, _), S.Enum
    | Accessor (_, enum, _), S.Enum -> enum
    | Data ({writable = w; _}, _, _), S.Writable -> w
    | Data ({value = v; _}, _, _), S.Value -> v
    | Accessor ({ getter = g; _}, _, _), S.Getter -> g
    | Accessor ({ setter = s; _}, _, _), S.Setter -> s
    | prop, attr -> failwith ("O.get_attr: bad access of attribute: " ^
                              (string_of_prop prop) ^ (S.string_of_attr attr))
  end

(* Mostly taken from Ljs_eval.set_attr *)
let set_attr ({extensible = ext; _} as attrs, props : t) (attr : S.pattr)
    (field : string) (value : value) : t =
  let newprop =
    if not (IdMap.mem field props) then
      match ext with
      | `A `True -> begin match attr with
          | S.Getter -> Accessor ({getter = value;
                                   setter = `A `Undef},
                                  `A `False,
                                  `A `False)
          | S.Setter -> Accessor ({getter = `A `Undef;
                                   setter = value},
                                  `A `False,
                                  `A `False)
          | S.Value -> Data ({value = value;
                              writable = `A `False},
                             `A `False,
                             `A `False)
          | S.Writable -> Data ({value = `A `Undef;
                                 writable = value},
                                `A `False,
                                `A `False)
          | S.Enum -> Data ({value = `A `Undef;
                             writable = `A `False},
                            value, `A `True)
          | S.Config -> Data ({value = `A `Undef;
                               writable = `A `False},
                              `A `True, value)
        end
      | `A `False -> failwith "extending inextensible object" (* TODO: raise an error that will be thrown instead *)
      | `A `BoolT -> failwith "set_attr: TODO (branching)"
      | `A v -> failwith ("set_attr: " ^ (AValue.to_string v))
      | `StackObj o -> failwith ("set_attr: StackObj: " ^ (to_string o))
    else
      (* TODO: In all the cases with `BoolT as config, there should be two
         results: one corresponding to `True, and one error state corresponding
         to `False. However, we assume that the desugared S5 code will never
         perform a field update when it can't (ie. the BoolTs results from
         joining a False with a more recent True) *)
      match (IdMap.find field props), attr with
      | Data ({writable = `A `True; _} as d, enum, config), S.Writable
      | Data ({writable = `A `BoolT; _} as d, enum, config), S.Writable
      | Data (d, enum, (`A `True as config)), S.Writable
      | Data (d, enum, (`A `BoolT as config)), S.Writable ->
        Data ({d with writable = value}, enum, config)
      | Data ({writable = `A `True; _} as d, enum, config), S.Value
      | Data ({writable = `A `BoolT; _} as d, enum, config), S.Value ->
        Data ({d with value = value}, enum, config)
      | Data (d, enum, `A `True), S.Setter
      | Data (d, enum, `A `BoolT), S.Setter ->
        Accessor ({getter = `A `Undef; setter = value}, enum, `A `True)
      | Data (d, enum, `A `True), S.Getter
      | Data (d, enum, `A `BoolT), S.Getter ->
        Accessor ({getter = value; setter = `A `Undef}, enum, `A `True)
      | Accessor (a, enum, `A `True), S.Getter
      | Accessor (a, enum, `A `BoolT), S.Getter ->
        Accessor ({a with getter = value}, enum, `A `True)
      | Accessor (a, enum, `A `True), S.Setter
      | Accessor (a, enum, `A `BoolT), S.Setter ->
        Accessor ({a with setter = value}, enum, `A `True)
      | Accessor (a, enum, `A `True), S.Value
      | Accessor (a, enum, `A `BoolT), S.Value ->
        Data ({value = value; writable = `A `False}, enum, `A `True)
      | Accessor (a, enum, `A `True), S.Writable
      | Accessor (a, enum, `A `BoolT), S.Writable ->
        Data ({value = `A `Undef; writable = value}, enum, `A `True)
      | Data (d, _, `A `True), S.Enum
      | Data (d, _, `A `BoolT), S.Enum ->
        Data (d, value, `A `True)
      | Data (d, enum, `A `True), S.Config
      | Data (d, enum, `A `BoolT), S.Config ->
        Data (d, enum, value)
      | Data (d, enum, `A `False), S.Config when value = `A `False ->
        Data (d, enum, `A `False)
      | Accessor (a, enum, `A `True), S.Config
      | Accessor (a, enum, `A `BoolT), S.Config ->
        Accessor (a, enum, value)
      | Accessor (a, enum, `A `True), S.Enum
      | Accessor (a, enum, `A `BoolT), S.Enum ->
        Accessor (a, value, `A `True)
      | Accessor (a, enum, `A `False), S.Config when value = `A `False ->
        Accessor (a, enum, `A `False)
      | prop, _ -> failwith ("bad property set: " ^ (string_of_prop prop) ^
                             ", " ^ (S.string_of_attr attr))
  in
  (attrs, IdMap.add field newprop props)

let get_obj_attr ((attrs, _) : t) (attr : S.oattr) : value =
  match attrs, attr with
  | {proto = v; _}, S.Proto
  | {extensible = v; _}, S.Extensible
  | {code = v; _}, S.Code
  | {primval = v; _}, S.Primval
  | {klass = v; _}, S.Klass -> v

let rec join ((attrs, props) : t) ((attrs', props') : t) : t =
  let new_attrs = {code = join_value attrs.code attrs'.code;
                   proto = join_value attrs.proto attrs'.proto;
                   primval = join_value attrs.primval attrs'.primval;
                   klass = join_value attrs.primval attrs'.primval;
                   extensible = join_value attrs.primval attrs'.primval} in
  let join_props (p : prop) (p' : prop) : prop = match p, p' with
    | Data ({value = v; writable = w}, enum, config),
      Data ({value = v'; writable = w'}, enum', config') ->
      Data ({value = join_value v v'; writable = join_value w w'},
            join_value enum enum', join_value config config')
    | Accessor ({getter = g; setter = s}, enum, config),
      Accessor ({getter = g'; setter = s'}, enum', config') ->
      Accessor ({getter = join_value g g'; setter = join_value s s'},
                join_value enum enum', join_value config config')
    | p1, p2 ->
      failwith ("joining different props:" ^
                (string_of_prop p1) ^ " and " ^ (string_of_prop p2)) in
  let merge_props _ x y = match x, y with
    | Some p, Some p' -> Some (join_props p p')
    | Some p, None | None, Some p -> Some p
    | None, None -> None in
  let new_props = IdMap.merge merge_props props props' in
  (new_attrs, new_props)
and join_value (x : value) (y : value) : value = match x, y with
  | `A v, `A v' -> `A (AValue.join v v')
  | `StackObj o, `StackObj o' -> `StackObj (join o o')
  | _, _ -> failwith ("cannot join " ^ (string_of_value x) ^ " and " ^ (string_of_value y))

let d_attrsv = {
  primval = `A `Undef;
  code = `A `Bot;
  proto = `A `Null;
  extensible = `A `False;
  klass = `A (`Str "LambdaJS internal");
}

let props_to_nearest_top (attrs, props) : t =
  (attrs, IdMap.map (function
    | Data ({value = v; writable = w}, enum, config) ->
      let newval = match v with
        | `A v' -> `A (AValue.aval v')
        | `StackObj o -> `StackObj o in
      Data ({value = newval; writable = w}, enum, config)
    | Accessor (a, enum, config) ->
      Accessor (a, enum, config))
      props)

module Value = struct
  type t = value
  let to_string = string_of_value
  let compare = compare_value
  let inj (v : AValue.t) = `A v
  let join (t : t) (t' : t) : t = match t, t' with
    | `A v, `A v' -> `A (AValue.join v v')
    | `StackObj o, `StackObj o' -> `StackObj (join o o')
    | _, _ ->
      Printf.printf "\027[31mJoining value with stack object: %s and %s\027[0m\n%!"
        (to_string t) (to_string t');
      `A `Top
end
