open Shared
open Lang

module type BuildDSG_signature =
  functor (L : Lang_signature) ->
  sig
    module G : Graph.Sig.P
    module ConfSet : BatSet.S with type elt = L.conf
    module EdgeSet : BatSet.S with type elt = (L.conf * L.stack_change * L.conf)
    module EpsSet : BatSet.S with type elt = L.conf * L.conf
    type dsg = { g : G.t; q0 : L.conf; ecg : G.t }
    val build_dyck : L.exp -> dsg
    val add_short : dsg -> L.conf -> L.conf -> ConfSet.t * EdgeSet.t * EpsSet.t
    val add_edge : dsg -> L.conf -> L.stack_change -> L.conf -> ConfSet.t * EdgeSet.t * EpsSet.t
    val explore : dsg -> L.conf -> ConfSet.t * EdgeSet.t * EpsSet.t
  end

module BuildDSG =
  functor (L : Lang_signature) ->
  struct
    module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(struct
        include L.ConfOrdering
        let hash = Hashtbl.hash
        let equal x y = compare x y == 0
      end)(struct
        include L.StackChangeOrdering
        let default = L.StackUnchanged
      end)

    module DotArg = struct
      include G

      module ConfMap = Map.Make(L.ConfOrdering)
      let id = ref 0
      let new_id () =
        id := !id + 1;
        !id

      let nodes = ref ConfMap.empty
      let node_id node =
        if ConfMap.mem node !nodes then
          ConfMap.find node !nodes
        else
          let id = new_id () in
          nodes := ConfMap.add node id !nodes;
          id

      let edge_attributes ((_, f, _) : E.t) =
        [`Label (L.string_of_stack_change f)]
      let default_edge_attributes _ = []
      let get_subgraph _ = None
      let vertex_name (state : V.t) =
        (string_of_int (node_id state))
      let vertex_attributes (state : V.t) =
        [`Label (L.string_of_conf state)]
      let default_vertex_attributes _ = []
      let graph_attributes _ = []
    end

    module Dot = Graph.Graphviz.Dot(DotArg)
    let output_graph graph file =
      let out = open_out_bin file in
      Dot.output_graph out graph;
      close_out out

    module ConfSet = BatSet.Make(L.ConfOrdering)
    module EdgeOrdering = struct
      type t = L.conf * L.stack_change * L.conf
      let compare (c1, g, c2) (c1', g', c2') =
        order_concat [lazy (L.ConfOrdering.compare c1 c1');
                      lazy (L.StackChangeOrdering.compare g g');
                      lazy (L.ConfOrdering.compare c2 c2')]
    end
    module EdgeSet = BatSet.Make(EdgeOrdering)
    module EpsOrdering = struct
      type t = L.conf * L.conf
      let compare (c1, c2) (c1', c2') =
        order_concat [lazy (L.ConfOrdering.compare c1 c1');
                      lazy (L.ConfOrdering.compare c2 c2')]
    end
    module EpsSet = BatSet.Make(EpsOrdering)

    type dsg = { g : G.t; q0 : L.conf; ecg : G.t }
    let output_dsg dsg = output_graph dsg.g
    let output_ecg dsg = output_graph dsg.ecg

    let add_short dsg c c' =
      (* print_endline ("add_short" ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c'));
         print_endline ("size of ECG: (" ^ (string_of_int (G.nb_vertex dsg.ecg)) ^ ", " ^
                     (string_of_int (G.nb_edges dsg.ecg)) ^ ")"); *)
      let (de, dh) = G.fold_edges_e
          (fun e (de, dh) -> match e with
             | (c1, L.StackPush k, c1') when L.ConfOrdering.compare c1' c == 0 ->
               let de', dh' =
                 (List.fold_left (fun acc edge -> match edge with
                      | (L.StackPop k', c2) when L.FrameOrdering.compare k k' == 0 ->
                        (EdgeSet.add (c', L.StackPop k, c2) de,
                         EpsSet.add (c1, c2) dh)
                      | _ -> acc)
                     (EdgeSet.empty, EpsSet.empty) (L.step c' (Some (c, k)))) in
               (EdgeSet.union de de', EpsSet.union dh dh')
             | _ -> (de, dh))
          dsg.g (EdgeSet.empty, EpsSet.empty) in
      let ds = EdgeSet.fold (fun (c1, g, c2) acc -> match g with
          | L.StackPop k -> ConfSet.add c2 acc
          | _ -> acc)
          de ConfSet.empty in
      let dh' =
        let (end_w_c, start_w_c') = G.fold_edges
            (fun c1 c2 (ec, sc') ->
               ((if L.ConfOrdering.compare c2 c == 0 then (c1, c2) :: ec else ec),
                (if L.ConfOrdering.compare c1 c' == 0 then (c1, c2) :: sc' else sc')))
            dsg.ecg ([], []) in
        List.fold_left EpsSet.union dh
          [List.fold_left (fun acc (c1, c2) -> EpsSet.add (c1, c') acc)
             EpsSet.empty end_w_c;
           List.fold_left (fun acc (c1, c2) -> EpsSet.add (c, c2) acc)
             EpsSet.empty start_w_c';
           List.fold_left (fun acc ((c1, _), (_, c2)) -> EpsSet.add (c1, c2) acc)
             EpsSet.empty (BatList.cartesian_product end_w_c start_w_c')] in
      (ConfSet.filter (fun c -> not (G.mem_vertex dsg.g c)) ds,
       EdgeSet.filter (fun c -> not (G.mem_edge_e dsg.g c)) de,
       EpsSet.filter (fun (c1, c2) -> not (G.mem_edge dsg.ecg c1 c2)) dh')

    let add_edge dsg c g c' =
      (* print_endline ("add_edge " ^ (L.string_of_conf c) ^ " ->" ^ (L.string_of_stack_change g) ^ " " ^ (L.string_of_conf c')); *)
      match g with
      | L.StackUnchanged ->
        (* print_endline ("Adding edge when calling add_short " ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c')); *)
        let (ds, de, dh) = add_short { dsg with ecg = G.add_edge dsg.ecg c c' } c c' in
        (ds, de, EpsSet.add (c, c') dh)
      | L.StackPush k ->
        let de = G.fold_edges
            (fun c_ c1 acc ->
               if L.ConfOrdering.compare c_ c' == 0 then
                 let c2s = List.filter (fun (g', c2) -> match g' with
                     | L.StackPop k' -> L.FrameOrdering.compare k k' == 0
                     | _ -> false) (L.step c1 (Some (c1, k))) in
                 List.fold_left (fun acc (g, c2) -> EdgeSet.add (c1, g, c2) acc)
                   acc c2s
               else
                 acc)
            dsg.ecg EdgeSet.empty in
        let ds = EdgeSet.fold
            (fun (_, _, c2) acc -> ConfSet.add c2 acc)
            de ConfSet.empty in
        let dh = G.fold_edges
            (fun (c_ : L.conf) (c1 : L.conf) (acc : EpsSet.t) ->
               if L.ConfOrdering.compare c_ c' == 0 then
                 let c2s = G.fold_edges_e (fun (c1_, g', c2) acc -> match g' with
                     | L.StackPop k' when L.FrameOrdering.compare k k' == 0 &&
                                          L.ConfOrdering.compare c1 c1_ == 0 ->
                       c2 :: acc
                     | _ -> acc) dsg.g [] in
                 List.fold_left (fun acc c2 -> EpsSet.add (c1, c2) acc)
                   acc c2s
               else
                 acc)
            dsg.ecg EpsSet.empty in
        (ConfSet.filter (fun c -> not (G.mem_vertex dsg.g c)) ds,
         EdgeSet.filter (fun c -> not (G.mem_edge_e dsg.g c)) de,
         EpsSet.filter (fun (c1, c2) -> not (G.mem_edge dsg.ecg c1 c2)) dh)
      | L.StackPop k ->
        let dh = G.fold_edges
            (fun c2 c_ acc ->
               if L.ConfOrdering.compare c_ c == 0 then
                 let c1s = G.fold_edges_e (fun (c1, g', c2_) acc -> match g' with
                     | L.StackPush k' when L.FrameOrdering.compare k k' == 0 &&
                                           L.ConfOrdering.compare c2 c2_ == 0 ->
                       c1 :: acc
                     | _ -> acc) dsg.g [] in
                 List.fold_left (fun acc c1 -> EpsSet.add (c1, c') acc)
                   acc c1s
               else
                 acc)
            dsg.ecg EpsSet.empty in
        (ConfSet.empty,
         EdgeSet.empty,
         EpsSet.filter (fun (c1, c2) -> not (G.mem_edge dsg.ecg c1 c2)) dh)

    let explore dsg c =
      (* print_endline ("explore " ^ (L.string_of_conf c)); *)
      let stepped = L.step c None in
      let ds = (List.fold_left
                  (fun set (_, conf) -> ConfSet.add conf set)
                  ConfSet.empty stepped)
      and de = (List.fold_left
                  (fun set (stack_op, conf) -> EdgeSet.add (c, stack_op, conf) set)
                  EdgeSet.empty stepped) in
      (ConfSet.filter (fun c -> not (G.mem_vertex dsg.g c)) ds,
       EdgeSet.filter (fun c -> not (G.mem_edge_e dsg.g c)) de,
       EpsSet.empty)

    let build_dyck exp =
      let c0 = L.inject exp in
      let i = ref 0 in
      let rec loop dsg ds de dh =
        i := !i + 1;
        try
          (* print_endline ("ΔS = " ^ (string_of_list (ConfSet.to_list ds)
                                       L.string_of_conf));
             print_endline ("ΔE = " ^ (string_of_list (EdgeSet.to_list de)
                                       (fun (c, g, c') ->
                                          (L.string_of_conf c) ^ " ->" ^ (L.string_of_stack_change g) ^ " " ^
                                          (L.string_of_conf c'))));
             print_endline ("ΔH = " ^ (string_of_list (EpsSet.to_list dh)
                                       (fun (c, c') ->
                                          (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c'))));
             print_endline ("Size of ECG (#v, #e): (" ^ (string_of_int (G.nb_vertex dsg.ecg)) ^
                         ", " ^ (string_of_int (G.nb_edges dsg.ecg)) ^ ")"); *)
          (* output_dsg dsg ("/tmp/dsg/dsg-" ^ (string_of_int !i) ^ ".dot");
             output_ecg dsg ("/tmp/dsg/ecg-" ^ (string_of_int !i) ^ ".dot"); *)
          if not (EpsSet.is_empty dh) then
            let c, c' = EpsSet.choose dh in
            (* print_endline ("eps: " ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c')); *)
            let (ds', de', dh') = add_short dsg c c' in
            (* print_endline ("Adding edge " ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c')); *)
            loop { dsg with ecg = G.add_edge dsg.ecg c c' }
              (ConfSet.union ds ds')
              (EdgeSet.union de de')
              (EpsSet.remove (c, c') (EpsSet.union dh dh'))
          else if not (EdgeSet.is_empty de) then
            let c, g, c' = EdgeSet.choose de in
            (* print_endline ("edge: " ^ (L.string_of_conf c) ^ " -> " ^ (L.string_of_conf c')); *)
            let (ds', de', dh') = add_edge dsg c g c' in
            loop { dsg with g = G.add_edge_e dsg.g (c, g, c') }
              (ConfSet.union ds ds')
              (EdgeSet.remove (c, g, c') (EdgeSet.union de de'))
              (EpsSet.union dh dh')
          else if not (ConfSet.is_empty ds) then
            let c = ConfSet.choose ds in
            (* print_endline ("conf: " ^ (L.string_of_conf c)); *)
            let (ds', de', dh') = explore dsg c in
            (* print_endline ("Adding vertex " ^ (L.string_of_conf c)); *)
            loop { dsg with g = G.add_vertex dsg.g c; ecg = G.add_vertex dsg.ecg c }
              (ConfSet.remove c (ConfSet.union ds ds'))
              (EdgeSet.union de de')
              (EpsSet.union dh dh')
          else
            dsg
        with e -> begin
            print_endline ("Failed at i = " ^ (string_of_int !i));
            output_dsg dsg ("/tmp/dsg-" ^ (string_of_int !i) ^ ".dot");
            print_endline (Printexc.to_string e);
            dsg
          end
      in loop { g = G.empty; q0 = c0; ecg = G.empty }
        (ConfSet.singleton c0) EdgeSet.empty EpsSet.empty

    let final_states dsg =
      G.fold_vertex (fun v acc -> if BatList.is_empty (G.succ dsg.g v) then
                        v :: acc
                      else
                        acc)
        dsg.g []
  end

module L = LJS
module DSG = BuildDSG(L)
