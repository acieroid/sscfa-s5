open Lang
open Dsg
open Lexing
open Prelude

module S = Ljs_syntax

let file =
  if Array.length Sys.argv < 2 then
    failwith "Expected a S5 file as argument"
  else
    Array.get Sys.argv 1

let load_s5 file : S.exp =
  let cin = open_in_bin file in
  let lexbuf = Lexing.from_channel cin in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file };
  try
    let e = Ljs_parser.prog Ljs_lexer.token lexbuf in
    close_in cin;
    e
  with
  |  Failure "lexing: empty token" ->
    failwith (sprintf "lexical error at %s"
                (Pos.string_of_pos (Pos.real
                                      (lexbuf.lex_curr_p, lexbuf.lex_curr_p))))
  | Parsing.Parse_error ->
    failwith (sprintf "parse error at %s; unexpected token %s"
                (Pos.string_of_pos (Pos.real
                                      (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
                (lexeme lexbuf))

module G = DSG.G

let eval exp =
  let push stack v = v :: stack in
  let pop = function
    | [] -> []
    | hd :: tl -> tl in
  let top = function
    | [] -> None
    | hd :: tl -> Some hd in
  let rec aux graph stack conf =
    try
      let confs' = LJS.step conf (top stack) in
      match confs' with
      | [] ->
        print_endline ("Evaluation done: " ^ (LJS.string_of_conf conf));
        graph
      | (g, conf') :: _ ->
        print_endline ((LJS.string_of_conf conf) ^ " -> " ^ (LJS.string_of_stack_change g) ^ " -> " ^ (LJS.string_of_conf conf'));
        aux (G.add_edge_e graph (conf, g, conf'))
          (match g with
           | LJS.StackPush f -> push stack (conf', f)
           | LJS.StackPop _ -> pop stack
           | LJS.StackUnchanged -> stack)
          conf'
    with e ->
      print_endline (Printexc.get_backtrace ());
      print_endline (Printexc.to_string e);
      graph
  in aux G.empty [] (LJS.inject exp)

let _ =
  let s5 = load_s5 file in
  print_endline (Shared.full_string_of_exp s5);
  (* let dsg = DSG.build_dyck s5 in
  DSG.output_dsg dsg "dsg.dot";
  DSG.output_ecg dsg "ecg.dot" *)
  let g = eval s5 in
  let out = open_out_bin "graph.dot" in
  DSG.Dot.output_graph out g;
  close_out out

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
