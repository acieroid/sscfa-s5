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
  "-no-global-gc", Arg.Unit (fun () -> gc := `NoGlobalGC),
  "don't inspect global environment/store when doing GC (may lead to unsoundness)";
  "-restricted-gc", Arg.Unit (fun () -> gc := `RestrictedGC),
  "disable GC for global S5 variables (starting with %)";
  "-no-gc", Arg.Unit (fun () -> gc := `NoGC),
  "entirely disable GC";
  "-deterministic", Arg.Unit (fun () -> computation := `Eval),
  "assume all transitions are deterministic, resulting in a list of states instead of a graph";
  "-only-mcfa", Arg.Set only_mcfa,
  "only use m-CFA addresses, and no parameter-sensitive k-CFA";
  "-no-atomic-eval", Arg.Unit (fun () -> atomic_eval := false),
  "disable atomic evaluator";
  "-debug", Arg.Set debug,
  "enable debug mode, printing messages on alloc and reclaim";
  "-flatten", Arg.Set flatten,
  "flatten library calls into only one transition";
  "-flatten-strip", Arg.Set flatten_strip,
  "flatten library calls into only one transition, strip the stack summary when doing so";
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
    failwith (Printf.sprintf "lexical error at %s"
                (Pos.to_string
                   (Pos.real (lexbuf.lex_curr_p, lexbuf.lex_curr_p))))
  | Parsing.Parse_error ->
    failwith (Printf.sprintf "parse error at %s; unexpected token %s"
                (Pos.to_string
                   (Pos.real (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
                (lexeme lexbuf))

let save_state (c : LJS.conf) (env : LJS.conf option) file =
  let cout = open_out_bin file in
  let c' = BatOption.map_default (fun env -> LJS.merge c env) c env in
  Marshal.to_channel cout c' [Marshal.Compat_32];
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
      (* print_endline ("conf: " ^ (LJS.string_of_conf conf) ^ ", top: " ^ (BatOption.map_default (fun (_, f) -> F.to_string f) "-" (top stack))); *)
      let confs' = LJS.step conf global (top stack) in
      match confs' with
      | [] ->
        graph, conf
      | (g, ((s, _) as conf')) :: _ ->
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
        let dsg = DSG.build_dyck s5 0 env in
        let final_states = DSG.final_states dsg in
        print_endline ("Final states: " ^ (string_of_list LJS.string_of_conf
                                             final_states));
        DSG.output_dsg dsg "dsg.dot";
        DSG.output_ecg dsg "ecg.dot";
        begin match !dump with
          | Some s -> save_state (List.hd final_states) env s
          | None -> ()
        end
      | `Eval ->
        let g, final = eval s5 env in
        let out = open_out_bin "graph.dot" in
        print_endline ("Final state: " ^ (LJS.string_of_conf final));
        DSG.Dot.output_graph out g;
        close_out out;
        begin match !dump with
          | Some s -> save_state final env s
          | None -> ()
        end
    end;
    Stats.print ();
  | None ->
    print_endline usage
