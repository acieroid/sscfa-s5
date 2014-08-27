open Lang
open Dsg
open Lexing
open Prelude
open Shared

let env = ref None
let dump = ref None
let file = ref None
let computation = ref `Dsg

let speclist = [
  "-env", Arg.String (fun s -> env := Some s),
  "environment file to load";
  "-dump", Arg.String (fun s -> dump := Some s),
  "where to dump the final environment (and store) of the execution";
  (* TODO: it would be better to disable collection of variables prefixed with
     % or #, except some (eg. %or) *)
  "-no-gc", Arg.Unit (fun () -> gc := false),
  "disable GC (needed when loading environments)";
  "-deterministic", Arg.Unit (fun () -> computation := `Eval),
  "assume all transitions are deterministic, resulting in a list of states instead of a graph"
]

let usage = "usage: " ^ (Sys.argv.(0)) ^ " [-dump file] [-env file] file"

module S = Ljs_syntax

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

let save_state (c : LJS.conf) file =
  let cout = open_out_bin file in
  Marshal.to_channel cout c [Marshal.Compat_32];
  close_out cout

let load_state file : LJS.conf =
  let cin = open_in_bin file in
  let state = Marshal.from_channel cin in
  close_in cin;
  state

module G = DSG.G

(* Evaluate a program as a linear sequence of states. If one step leads to more
   than one state, only the first one is kept. (This allow easier debugging on
   simple programs.) *)
let eval exp env =
  let push stack v = v :: stack in
  let pop = function
    | [] -> []
    | hd :: tl -> tl in
  let top = function
    | [] -> None
    | hd :: tl -> Some hd in
  let (c0, global) = LJS.inject exp env in
  let rec aux graph stack conf =
    try
      let confs' = LJS.step conf global (top stack) in
      match confs' with
      | [] ->
        (* print_endline ("Evaluation done: " ^ (LJS.string_of_conf conf)); *)
        graph, conf
      | (g, conf') :: _ ->
        (* print_endline ((LJS.string_of_conf conf) ^ " -> " ^ (LJS.string_of_stack_change g) ^ " -> " ^ (LJS.string_of_conf conf')); *)
        aux (G.add_edge_e graph (conf, g, conf'))
          (match g with
           | LJS.StackPush f -> push stack (conf', f)
           | LJS.StackPop _ -> pop stack
           | LJS.StackUnchanged -> stack)
          conf'
    with e ->
      print_endline (Printexc.get_backtrace ());
      Printf.printf "Failed after computing %d states: %s\n" (G.nb_vertex graph) (Printexc.to_string e);
      graph, conf in
  aux G.empty [] c0

let () =
  let () = Arg.parse speclist (fun x -> file := Some x) usage in
  match !file with
  | Some file ->
    let s5 = load_s5 file in
    let env = BatOption.map load_state !env in
    begin match !computation with
      | `Dsg ->
        let dsg = DSG.build_dyck s5 env in
        let final_states = DSG.final_states dsg in
        print_endline ("Final states: " ^ (string_of_list final_states LJS.string_of_conf));
        DSG.output_dsg dsg "dsg.dot";
        DSG.output_ecg dsg "ecg.dot";
        begin match !dump with
          | Some s -> save_state (List.hd final_states) s
          | None -> ()
        end
      | `Eval ->
        let g, final = eval s5 env in
        let out = open_out_bin "graph.dot" in
        print_endline ("Final state: " ^ (LJS.string_of_conf final));
        DSG.Dot.output_graph out g;
        close_out out;
        begin match !dump with
          | Some s -> save_state final s
          | None -> ()
        end
    end
  | None ->
    print_endline usage
