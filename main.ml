open Lang
open Dsg
open Lexing
open Prelude
open Shared

module S = Ljs_syntax

let file =
  if Array.length Sys.argv < 2 then
    failwith "Expected a S5 file as argument"
  else
    Array.get Sys.argv 1

(* Parse a S5 source code file *)
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

let save_state dsg file =
  match DSG.final_states dsg with
  | [] -> failwith "No final state found"
  | [state] ->
    let cout = open_out_bin file in
    Marshal.to_channel cout state [Marshal.Compat_32];
    close_out cout
  | _ -> failwith "More than one state found"

let load_state file =
  let cin = open_in_bin file in
  let state = Marshal.from_channel cin in
  close_in cin;
  state

module G = DSG.G

(* Evaluate a program as a linear sequence of states. If one step leads to more
   than one state, only the first one is kept. (This allow easier debugging on
   simple programs.) *)
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
      Printf.printf "Failed after computing %d states: %s" (G.nb_vertex graph) (Printexc.to_string e);
      graph
  in aux G.empty [] (LJS.inject exp)

let computation = `Dsg

let _ =
  let s5 = load_s5 file in
  match computation with
  | `Dsg ->
    let dsg = DSG.build_dyck s5 in
    let final_states = DSG.final_states dsg in
    print_endline ("Final states: " ^ (string_of_list final_states LJS.string_of_conf));
    DSG.output_dsg dsg "dsg.dot";
    DSG.output_ecg dsg "ecg.dot"
  | `Eval ->
    let g = eval s5 in
    let out = open_out_bin "graph.dot" in
    DSG.Dot.output_graph out g;
    close_out out
