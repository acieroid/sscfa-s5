open Prelude
open Ljs_syntax
open Store
open Env
open Lattice
open Shared

let file =
  if Array.length Sys.argv < 2 then
    failwith "Expected a S5 file as argument"
  else
    Array.get Sys.argv 1

let load_s5 file =
  Marshal.from_channel (open_in_bin file)

let save_s5 s5 file =
  Marshal.to_channel (open_out_bin file) s5 []

let _ =
  let s =
    Store.empty |>
    Store.join (Address.alloc 1) `True |>
    Store.join (Address.alloc 1) `False in
  Printf.printf "%s\n" (Store.to_string s)
(*  let s5 = load_s5 file in
  print_endline (string_of_exp s5)
*)
