open Prelude
open Lattice

module S = Ljs_syntax

type attrs = {
  code : AValue.t;
  proto : AValue.t;
  primval : AValue.t;
  klass : AValue.t;
  extensible : AValue.t;
}

type data = {
  value : AValue.t;
  writable : AValue.t;
}

type accessor = {
  getter : AValue.t;
  setter : AValue.t;
}

type prop =
  | Data of data * AValue.t * AValue.t
  | Accessor of accessor * AValue.t * AValue.t

(* TODO: use a PropMap that is keyed on AValue.t instead of an IdMap *)
type t = attrs * (prop IdMap.t)

let compare x y = failwith "not implemented: Obj_val.compare"

let to_string o = failwith "not implemented: Obj_val.to_string"

let set_attr (attrs, props) attr value = match attr with
  | "proto" -> ({ attrs with proto = value }, props)
  | "code" -> ({ attrs with code = value }, props)
  | "prim" -> ({ attrs with primval = value }, props)
  | _ -> failwith ("Invalid attr for object: " ^ attr)

let set_prop (attrs, props) prop value =
  (attrs, IdMap.add prop value props)

let has_prop (attrs, props) = function
  | `Str prop -> IdMap.mem prop props
  | `StrT -> failwith "has_prop on abstract string"
  | _ -> failwith "has_prop: invalid field name"

let lookup_prop (attrs, props) = function
  | `Str prop -> IdMap.find prop props
  | `StrT -> failwith "lookup_prop on abstract string"
  | _ -> failwith "lookup_prop: invalid field name"

let get_attr (attrs, props) attr = function
  | `Str field ->
    if not (IdMap.mem field props) then
      `Undef
    else
      begin match (IdMap.find field props), attr with
      | Data (_, _, config), S.Config
      | Accessor (_, _, config), S.Config -> config
      | Data (_, enum, _), S.Enum
      | Accessor (_, enum, _), S.Enum -> enum
      | Data ({writable = w; _}, _, _), S.Writable -> w
      | Data ({value = v; _}, _, _), S.Value -> v
      | Accessor ({ getter = g; _}, _, _), S.Getter -> g
      | Accessor ({ setter = s; _}, _, _), S.Setter -> s
      | _ -> failwith "bad access of attriubte"
      end
  | `StrT -> failwith "get_attr on abstract string"
  | _ -> failwith "get_attr: invalid field name"
