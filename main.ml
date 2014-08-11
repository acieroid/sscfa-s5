open Prelude
open Ljs_syntax
open Store
open Env
open Lattice
open Shared
open Lang

let file =
  if Array.length Sys.argv < 2 then
    failwith "Expected a S5 file as argument"
  else
    Array.get Sys.argv 1

let load_s5 file : exp =
  Marshal.from_channel (open_in_bin file)

let save_s5 s5 file =
  Marshal.to_channel (open_out_bin file) s5 []

module S = BatSet.Make(struct
    type t = LJS.stack_change * LJS.conf
    let compare (g, c) (g', c') =
      order_comp (LJS.compare_stack_change g g') (LJS.compare_conf c c')
end)

let eval exp =
  let push stack v = v :: stack in
  let pop = function
    | [] -> []
    | hd :: tl -> tl in
  let top = function
    | [] -> []
    | hd :: tl -> [hd] in
  let rec aux stack conf =
    let confs' = LJS.step conf (top stack) in
    match confs' with
    | [] -> print_endline ("Evaluation done: " ^ (LJS.string_of_conf conf))
    | (g, conf) :: _ ->
      print_endline ((LJS.string_of_stack_change g) ^ " -> " ^ (LJS.string_of_conf conf));
      match g with
      | LJS.StackPush f -> aux (push stack (conf, f)) conf
      | LJS.StackPop _ -> aux (pop stack) conf
      | LJS.StackUnchanged -> aux stack conf
  in aux [] (LJS.inject exp)

let _ =
  let s5 = load_s5 file in
  eval s5

(*
  let conf = LJS.inject s5 in
  print_endline (LJS.string_of_conf conf);
  let [g, conf] = LJS.step conf [] in
  print_endline (LJS.string_of_stack_change g);
  print_endline (LJS.string_of_conf conf)
*)
(*  let s =
    ValueStore.empty |>
    ValueStore.join (Address.alloc 1) `True |>
    ValueStore.join (Address.alloc 1) `False in
  Printf.printf "%s\n" (ValueStore.to_string s) *)
(*  let s5 = load_s5 file in
  print_endline (string_of_exp s5)
*)
