open Shared
open Env
open Store
open Lattice

module type Lang_signature =
sig
  type exp
  val string_of_exp : exp -> string
  type conf
  val string_of_conf : conf -> string
  module ConfOrdering : BatInterfaces.OrderedType with type t = conf
  type frame
  val string_of_frame : frame -> string
  module FrameOrdering : BatInterfaces.OrderedType with type t = frame
  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged
  module StackChangeOrdering : BatInterfaces.OrderedType with type t = stack_change
  val string_of_stack_change : stack_change -> string
  val inject : exp -> conf
  (* the frame list argument is the list of the potential frames that reside on
     the top of the stack, not the stack itself *)
  val step : conf -> (conf * frame) list -> (stack_change * conf) list
end

module LJS =
struct
  module Address = IntegerAddress

  type clo = TODO (* See labichn's Clo lattice *)

  module Lattice = TODO (* labichn's Aval lattice *)


  module Store = MapStore(Lattice)(Address)

  type state = Ljs_syntax.exp * Env.t * Store.t
  type frame = TODO (* What should be contained in the frames? See the LambdaS5 CESK already existing *)

  let string_of_frame = TODO
  let compare_frame = TODO

  let compare_state = TODO

  type stack_change =
    | StackPop of frame
    | StackPush of frame
    | StackUnchanged

  let compare_stack_change g1 g2 = match (g1, g2) with
    | StackPop f1, StackPop f2 -> compare_frame f1 f2
    | StackPush f1, StackPush f2 -> compare_frame f1 f2
    | StackUnchanged, StackUnchanged -> 0
    | StackPop _, _ -> 1
    | _, StackPop _ -> -1
    | StackPush _, StackUnchanged -> 1
    | StackUnchanged, _ -> -1

  let string_of_stack_change = function
    | StackPush f -> "+" ^ (string_of_frame f)
    | StackPop f -> "-" ^ (string_of_frame f)
    | StackUnchanged -> "e"

  module FrameOrdering = struct
    type t = frame
    let compare = compare_frame
  end

  module StackChangeOrdering = struct
    type t = stack_change
    let compare = compare_stack_change
  end

  let atomic_eval atom env store = TODO (* what are the atomic values? *)

  (* TODO: put that somewhere else? *)
  let alloc v state = match state with
    | (_, _, store) -> Address.alloc (Store.size store + 1)
end
