open Prelude
open Ljs_syntax
open Store
open Env
open Lattice
open Shared
open Dsg

let file =
  if Array.length Sys.argv < 2 then
    failwith "Expected a S5 file as argument"
  else
    Array.get Sys.argv 1

let load_s5 file : exp =
  Marshal.from_channel (open_in_bin file)

let save_s5 s5 file =
  Marshal.to_channel (open_out_bin file) s5 []

let _ =
  let s5 = load_s5 file in
  let conf = LJS.inject s5 in
  print_endline (LJS.string_of_conf conf);
  let [g, conf] = LJS.step conf [] in
  print_endline (LJS.string_of_stack_change g);
  print_endline (LJS.string_of_conf conf)

(*  let s =
    ValueStore.empty |>
    ValueStore.join (Address.alloc 1) `True |>
    ValueStore.join (Address.alloc 1) `False in
  Printf.printf "%s\n" (ValueStore.to_string s) *)
(*  let s5 = load_s5 file in
  print_endline (string_of_exp s5)
*)
