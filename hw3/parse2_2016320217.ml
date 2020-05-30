type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production

(* symbol, original derivation, dotted derivation *)
type item = (symbol * symbol list * symbol list)
type dfa_state = item BatSet.t
type dfa_states = dfa_state BatSet.t
type dfa_edge = (dfa_state * symbol * dfa_state)
type dfa_edges = dfa_edge BatSet.t 

type first_follow = (symbol, symbol BatSet.t) BatMap.t

type table_entry = Goto of dfa_state | Shift of dfa_state | Reduce of (symbol * symbol list) | Accept
type parsing_table = ((dfa_state*symbol), table_entry BatSet.t) BatMap.t

(* ocamlfind batteries/ocaml *)

let sidx = ref 0

let symbol_print : symbol -> unit
= fun x ->
  match x with
  |T s -> print_string(s^", ")
  |N s -> print_string(s^", ")
  |Epsilon -> print_string("Epsilon, ")
  |End -> print_string("End, ")

let batmap_print : first_follow -> unit 
= fun first ->
    BatMap.iter (fun key value -> 
    print_endline "--- 키 ---";
    symbol_print key;
    print_endline "";
    (print_endline "--- value ---");
    BatSet.iter symbol_print value;
    (print_endline "");
    ) first

let state_print : dfa_state -> unit
= fun state ->
  print_endline "--- state ---";BatSet.iter(fun (symbol, original_deriv, dotted_deriv) ->
    symbol_print symbol;print_string(" -> ");List.iter symbol_print dotted_deriv;print_endline("")
  ) state

let states_print : dfa_states -> unit
= fun states ->
  BatSet.iter state_print states



let entry_print : table_entry -> unit
= fun entry ->
  print_endline "--- 엔트리 ---";
  match entry with
  |Goto state -> print_endline "Goto"
  |Shift state -> print_endline "Shift";state_print state
  |Reduce (symbol, deriv) -> print_endline "Reduce";symbol_print symbol;print_string " -> ";List.iter symbol_print deriv
  |Accept -> print_endline "Accept"

let table_print : parsing_table -> unit
= fun table ->
  let check = BatMap.filterv (fun set -> (BatSet.cardinal set)>1) table in
  if((BatMap.cardinal check)>0) then print_endline ("-----------------------중 복 발 생--------------------------") else ();
  BatMap.iter(fun (dfa_state, symbol) entry_set ->
    print_endline "--- 스테이트 ---";
    state_print dfa_state;
    print_endline "--- 심볼 ---";
    symbol_print symbol; print_endline("");
    BatSet.iter (entry_print) entry_set;
    (print_endline ""); 
  ) table

  let edge_print : dfa_edge -> unit
  = fun edge ->
  let (source, symbol, target) = edge in
  let p = print_endline "--edge--" in
  print_endline "--source--";state_print source;print_endline "";print_endline "--symbol--";symbol_print symbol;print_endline "";print_endline "--target--";state_print target


  (*------------------------- HW2 내용 --------------------------------------*)
  (*first에 터미널 추가*)
let rec make_first_terminals : symbol list -> first_follow -> first_follow
= fun target first ->
  match target with
  |[] -> first
  |hd::tl ->
    let first_new = BatMap.add hd (BatSet.singleton hd) first in
    make_first_terminals tl first_new

(* type production = (symbol * symbol list) list *)
let rec make_working_list : first_follow -> production -> production -> (first_follow * production)
= fun first production working_list ->
  match production with
  |[] -> (first, working_list)
  |(symbol,symbol_list)::rest_production ->
    match symbol_list with
    |[] -> (*epsilon일 경우*)
      let symbol_first = BatMap.find_default BatSet.empty symbol first in
      let extended_symbol_first = BatSet.add Epsilon symbol_first in
      let extended_first = BatMap.add symbol extended_symbol_first first in
      make_working_list extended_first rest_production working_list
    |hd::tl ->
      match hd with
      |T e -> (* derivation이 terminal로 시작할 경우, 반복적인 확장이 불필요하므로 working_list가 아닌 first에 추가한다. *)
        let symbol_first = BatMap.find_default BatSet.empty symbol first in
        let extended_symbol_first = BatSet.add hd symbol_first in
        let extended_first = BatMap.add symbol extended_symbol_first first in
        make_working_list extended_first rest_production working_list          
      |N e ->
        let working_list_added = working_list@[(symbol,symbol_list)] in
        make_working_list first rest_production working_list_added
      |_ -> print_endline("치명적 오류. 발생할 수 없는 경우!");(first, working_list)

(* next epsilon 계산을 한바퀴 돌았는데도 본래 states와 차이가 없다면 그 states를 반환. 있으면 없을 떄까지 계속한다. *)
let rec fixed_point_iteration : ('a -> 'a) -> 'a -> 'a
= fun f (first, working_list) ->
  let (first_after, _) = f (first, working_list) in
  if(BatMap.equal (fun b1 b2 -> BatSet.equal b1 b2) first first_after) then (first, working_list) else fixed_point_iteration f (first_after, working_list)
    
    (* working list내 개별 X들 대상으로 first 구하는 작업*)
let rec first_iteration_sub : symbol -> symbol list -> first_follow -> first_follow
= fun original target first ->
  match target with
  |[] ->  (* 모든 X_i가 epsilon을 갖고 있다. 따라서 First(X)에도 epsilon을 추가*)
    let symbol_first = BatMap.find_default BatSet.empty original first in
    let extended_symbol_first = BatSet.add Epsilon symbol_first in
    let extended_first = BatMap.add original extended_symbol_first first in
    extended_first
  |hd::tl -> (*  *)
    let original_first = BatMap.find_default BatSet.empty original first in
    let hd_first = BatMap.find_default BatSet.empty hd first in
    let hd_first_remove_epsilon = BatSet.remove Epsilon hd_first in
    let union_first = BatSet.union hd_first_remove_epsilon original_first in
    let first_map = BatMap.add original union_first first in
    if(BatSet.mem Epsilon hd_first) (* X_{i-1}에 epsilon이 있나? *)
    then first_iteration_sub original tl first_map (* 있으면 X_{i}에 대해서도 작업 수행 *)
    else first_map (* 없으면 뒤까지 넘어갈 필요가 없으므로 그대로 반환 *)

let rec make_first_for_fixed_point_iteration : (first_follow * production) -> (first_follow * production)
= fun (first, working_list) ->
  match working_list with
  |[] -> (first, working_list)
  |(symbol, derivation_list)::tl ->
    let first_after = first_iteration_sub symbol derivation_list first in
      make_first_for_fixed_point_iteration (first_after, tl)

let make_first : cfg -> first_follow
= fun cfg ->
  let (non_terminals, terminals, start, production) = cfg in
  let first_initial = make_first_terminals terminals (BatMap.singleton Epsilon (BatSet.singleton Epsilon)) in (* 터미널만 담고 있는 first *)
  let (first, working_list) = make_working_list first_initial production [] in 
  let (first_final, _) = fixed_point_iteration make_first_for_fixed_point_iteration (first, working_list) in
  first_final

let rec find_first : first_follow -> symbol list -> symbol BatSet.t -> symbol BatSet.t
= fun first_map derivation_list first_x ->
  match derivation_list with
  |[] -> BatSet.add Epsilon first_x
  |hd::tl ->
    let first_x1 = BatMap.find hd first_map in
    if(not (BatSet.mem Epsilon first_x1))
    then BatSet.union first_x1 first_x
    else
      let first_x_after = BatSet.union first_x (BatSet.remove Epsilon first_x1) in
      find_first first_map tl first_x_after

let rec follow_iteration_sub : symbol -> symbol list -> first_follow -> first_follow -> first_follow
= fun symbol derivation_list first follow -> (* symbol = A *)
  match derivation_list with
  |[] -> follow
  |hd::tl ->
    (match hd with (* hd = B *)
    |T s -> follow_iteration_sub symbol tl first follow
    |N s ->
      (match tl with (* tl의 head = beta *)
      |[] ->
        let follow_A = BatMap.find_default BatSet.empty symbol follow in
        let follow_B = BatMap.find_default BatSet.empty hd follow in
        let follow_B_A_added = BatSet.union follow_A follow_B in
        let follow_map = BatMap.add hd follow_B_A_added follow in
        follow_map
      |beta::rest ->
        let first_beta = find_first first tl BatSet.empty in
        (*let first_beta = BatMap.find beta first in*)
        let follow_B = BatMap.find_default BatSet.empty hd follow in
        let follow_B_first_beta_added = BatSet.union follow_B (BatSet.remove Epsilon first_beta) in
        if(BatSet.mem Epsilon first_beta)
        then
          let follow_A = BatMap.find_default BatSet.empty symbol follow in
          let follow_B_A_added = BatSet.union follow_A follow_B_first_beta_added in
          let follow_map = BatMap.add hd follow_B_A_added follow in
          follow_iteration_sub symbol tl first follow_map
        else
          let follow_map = BatMap.add hd follow_B_first_beta_added follow in
          follow_iteration_sub symbol tl first follow_map)
    |_ -> print_endline "치명적 오류. 발생할 수 없는 경우!";follow)

let rec make_follow_for_fixed_point_iteration : first_follow -> (first_follow * production) -> (first_follow * production)
= fun first (follow, production) ->
  match production with
  |[] -> (follow, production)
  |(symbol, derivation_list)::tl ->
    let follow_after = follow_iteration_sub symbol derivation_list first follow in
      make_follow_for_fixed_point_iteration first (follow_after, tl)

let make_follow : cfg -> first_follow -> first_follow
= fun cfg first ->
  let (non_terminals, terminals, start, production) = cfg in
  let follow_initial = BatMap.singleton start (BatSet.singleton End) in
  let (follow_final, _) = fixed_point_iteration (make_follow_for_fixed_point_iteration first) (follow_initial, production) in
  follow_final




(*------------------------------- HW3 시작 ---------------------------*)
let rec fixed_point_iteration_closure : ('a -> 'a) -> 'a -> 'a
= fun f state ->
  let state_after = f state in
  if(BatSet.equal state state_after) then state else fixed_point_iteration_closure f state_after
  
(* clousre 확장에 필요한 B set을 구하는 함수 *)
let find_symbol_set_for_expand : dfa_state -> symbol BatSet.t
= fun state ->
  let tmp : item -> symbol BatSet.t -> symbol BatSet.t
  = (fun (symbol, original_derivation, dotted_derivation) set ->
    match dotted_derivation with
    |hd::tl -> BatSet.add hd set
    |[] -> set) in
  BatSet.fold tmp state BatSet.empty

let closure_sub :  production -> dfa_state -> dfa_state
= fun production state ->
  let expand_state : production -> symbol -> dfa_state -> dfa_state
  = (fun production target_symbol result ->
    let production_to_expand = List.filter (fun (symbol, derivation) -> symbol=target_symbol) production in
    List.fold_right (fun (symbol, derivation) result_set -> BatSet.add (symbol, derivation, derivation) result_set) production_to_expand result) in
  let symbol_set_for_expand = find_symbol_set_for_expand state in
  BatSet.fold (expand_state production) symbol_set_for_expand state

let closure : production -> dfa_state -> dfa_state
= fun production state ->
fixed_point_iteration_closure (closure_sub production) state

let goto : production -> dfa_state -> symbol -> dfa_state
= fun production state input_symbol ->
  let state_filtered = BatSet.filter (fun (symbol, original_deriv, dotted_deriv) -> not (dotted_deriv=[])) state in
  let next_state = BatSet.fold (fun (symbol, original_deriv, dotted_deriv) result -> if((List.hd dotted_deriv)=input_symbol) then BatSet.add (symbol, original_deriv, (List.tl dotted_deriv)) result else result) state_filtered BatSet.empty in
  closure production next_state

let rec fixed_point_iteration_Dfa : ((dfa_states * dfa_edges) -> (dfa_states * dfa_edges)) -> (dfa_states * dfa_edges) -> (dfa_states * dfa_edges)
= fun f (nodes, edges) ->
  let (nodes_after, edges_after) = f (nodes, edges) in
  if((BatSet.equal nodes nodes_after) && (BatSet.equal edges_after edges))
  then (nodes, edges)
  else fixed_point_iteration_Dfa f (nodes_after, edges_after)

let find_next_deriv_symbol_list : item -> symbol list -> symbol list
= fun item result ->
  let (symbol, original_deriv, dotted_deriv) = item in
  if(dotted_deriv = [])
  then result
  else
    result@[List.hd dotted_deriv]

    (* 개별 next_deriv_symbol 별 실행 *)
let f_sub_sub : production -> dfa_state -> symbol -> (dfa_states * dfa_edges) -> (dfa_states * dfa_edges)
= fun production single_state symbol (nodeSet, edgeSet) ->
  let j = goto production single_state symbol in
  let nodeSet_after = BatSet.add j nodeSet in
  let edgeSet_after = BatSet.add (single_state, symbol, j) edgeSet in
  (nodeSet_after, edgeSet_after)

  (* 개별 스테이트 별 실행 *)
let f_sub : production -> dfa_state -> (dfa_states * dfa_edges) -> (dfa_states * dfa_edges)
= fun production single_state (nodeSet, edgeSet) -> 
  let next_deriv_symbol_list = BatSet.fold find_next_deriv_symbol_list single_state [] in
  List.fold_right (f_sub_sub production single_state) next_deriv_symbol_list (nodeSet, edgeSet)

let f : production -> (dfa_states * dfa_edges) -> (dfa_states * dfa_edges)
= fun production (nodeSet, edgeSet) ->
  BatSet.fold (f_sub production) nodeSet (nodeSet, edgeSet)

let construct_dfa : cfg -> (dfa_state * dfa_states * dfa_edges)
= fun cfg ->
  let (non_terminals, terminals, start, production) = cfg in
  let start_new = N "start_new" in
  let production_new = [(start_new, [start])]@production in
  let initial_state = closure production_new (BatSet.singleton (start_new, [start], [start])) in
  let nodeSet_initial = BatSet.singleton initial_state in
  let (nodes, edges) = fixed_point_iteration_Dfa (f production_new) (nodeSet_initial, BatSet.empty) in
    (initial_state, nodes, edges)

(* type parsing_table = ((dfa_state*symbol), table_entry BatSet) BatMap.t *)
let constrcut_table_sub_edge : dfa_edge -> parsing_table -> parsing_table
= fun edge table ->
  let (source, symbol, dest) = edge in
  let entry = BatMap.find_default BatSet.empty (source, symbol) table in
  match symbol with
  |T s ->
    let entry_after = BatSet.add (Shift dest) entry in
    BatMap.add (source, symbol) entry_after table
  |N s ->
    let entry_after = BatSet.add (Goto dest) entry in
    BatMap.add (source, symbol) entry_after table

let slr_follow_reference : symbol -> dfa_state -> symbol list -> symbol -> parsing_table -> parsing_table
= fun rule_symbol state original_deriv symbol result ->
  let entry = BatMap.find_default BatSet.empty (state, symbol) result in
  let entry_after = BatSet.add (Reduce (rule_symbol, original_deriv)) entry in
  BatMap.add (state, symbol) entry_after result

let construct_table_sub_state : first_follow -> dfa_state -> parsing_table -> parsing_table
= fun follow state table ->
  let sub : dfa_state -> item -> parsing_table -> parsing_table
  = (fun state item table ->
    let (symbol, original_deriv, dotted_deriv) = item in
    match dotted_deriv with
    |[] ->
      if(symbol = N "start_new")
      then BatMap.add (state, End) (BatSet.singleton Accept) table
      else
      let symbol_y_set = BatMap.find_default BatSet.empty symbol follow in
      BatSet.fold (slr_follow_reference symbol state original_deriv) symbol_y_set table
    |_ -> table) in
  BatSet.fold (sub state) state table
    
let construct_parsing_table : cfg -> first_follow -> (dfa_state * parsing_table)
= fun cfg follow ->
  let (non_terminals, terminals, start, production) = cfg in
  let (state_initial, nodeSet, edgeSet) = construct_dfa cfg in
  let table = BatSet.fold constrcut_table_sub_edge edgeSet BatMap.empty in
  let table_final = BatSet.fold (construct_table_sub_state follow) nodeSet table in
  (state_initial, table_final)

let check_SLR : cfg -> bool
= fun cfg ->
  let first = make_first cfg in
  let follow = make_follow cfg first in
  let (_, table) = construct_parsing_table cfg follow in
  let check = BatMap.filterv (fun set -> (BatSet.cardinal set)>1) table in
  if((BatMap.cardinal check)>0) then false else true

let rec remove_n_from_list : 'a list -> int -> 'a list
= fun lst num ->
  if(num=0) then lst else remove_n_from_list (List.tl lst) (num-1)

let rec lr_Parsing : parsing_table -> dfa_state list -> symbol list -> symbol list -> bool
= fun table state_stack symbols_stack input ->
  let input_hd = List.hd input in
  let entry_set = BatMap.find_default BatSet.empty ((List.hd state_stack), input_hd) table in
  if(BatSet.is_empty entry_set)
  then false
  else
    let (entry, _) = BatSet.pop entry_set in
    match entry with
    |Goto state -> print_endline "발생할 수 없는 경우!";false
    |Shift state ->
      lr_Parsing table (state::state_stack) (input_hd::symbols_stack) (List.tl input)
    |Reduce (symbol, deriv) ->
      let count = List.length deriv in
      let symbols_popped = remove_n_from_list symbols_stack count in
      let symbols_pushed = symbol::symbols_popped in
      let state_popped = remove_n_from_list state_stack count in
      let entry_set_new = BatMap.find_default BatSet.empty ((List.hd state_popped), symbol) table in
      if(BatSet.is_empty entry_set_new)
      then false
      else
        let (entry_new, _) = BatSet.pop entry_set_new in
        let (Goto next_state) = entry_new in
        let state_pushed = next_state::state_popped in
        (lr_Parsing table state_pushed symbols_pushed input)
    |Accept -> true

let parse : cfg -> symbol list -> bool
= fun cfg sentence ->
  let first = make_first cfg in
  let follow = make_follow cfg first in
  let (state_initial, table) = construct_parsing_table cfg follow in
  lr_Parsing table [state_initial] [] sentence