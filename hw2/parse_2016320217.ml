type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
(* non-terminal, terminal, start variable, production*)
type cfg = symbol list * symbol list * symbol * production
type first_follow = (symbol, symbol BatSet.t) BatMap.t
type parsing_table = ((symbol*symbol), symbol list BatSet.t) BatMap.t

let symbol_print : symbol -> unit
= fun x ->
  match x with
  |T s -> print_string(s^", ")
  |N s -> print_string(s^", ")
  |Epsilon -> print_string("Epsilon, ")
  |End -> print_string("End, ")

let batmap_print : first_follow -> unit 
=fun first ->
    BatMap.iter (fun key value -> 
    print_endline "--- 키 ---";
    symbol_print key;
    print_endline "";
    (print_endline "--- value ---");
    BatSet.iter symbol_print value;
    (print_endline "");
    ) first

let parsing_table_print : parsing_table -> unit
= fun table ->
  BatMap.iter (fun (symbol, terminal) value -> 
  print_endline "--- 키 ---";
  symbol_print symbol;
  symbol_print terminal;
  print_endline "";
  (print_endline "--- value ---");
  BatSet.iter (List.iter symbol_print) value;
  (print_endline "");
  ) table

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

let sub : first_follow -> first_follow -> symbol -> symbol list -> parsing_table -> parsing_table
= fun first_map follow_map symbol alpha table ->
  let first_alpha = find_first first_map alpha BatSet.empty in
  let table = BatSet.fold ((fun symbol alpha terminal table -> BatMap.add (symbol, terminal) (BatSet.add alpha (BatMap.find_default BatSet.empty (symbol, terminal) table)) table) symbol alpha) (BatSet.remove Epsilon first_alpha) table in
  if(BatSet.mem Epsilon first_alpha)
  then
    let follow_A = BatMap.find symbol follow_map in
    let table_after = BatSet.fold ((fun symbol alpha terminal table -> BatMap.add (symbol, terminal) (BatSet.add alpha (BatMap.find_default BatSet.empty (symbol, terminal) table)) table) symbol alpha) follow_A table in
    table_after
  else table

let construct_parsing_table  : cfg -> parsing_table
= fun cfg ->
  let (non_terminals, terminals, start, production) = cfg in
  let first = make_first cfg in
  let follow = make_follow cfg first in
  let table = List.fold_left (fun table (symbol, alpha) -> sub first follow symbol alpha table) BatMap.empty production in
  table

let check_LL1 : cfg -> bool
= fun cfg ->
  let table = construct_parsing_table cfg in
  let check = BatMap.filterv (fun set -> (BatSet.cardinal set)>1) table in
  if((BatMap.cardinal check)>0) then false else true

let rec predictive_parsing : parsing_table -> symbol list -> symbol list -> bool
= fun table (top::rest_stack) (w::rest_input) ->
  (*let debug = symbol_print top;symbol_print w;print_endline "진행중 "; in*)
  if(top=w)
  then (if(top=End) then true else predictive_parsing table rest_stack rest_input)
  else
    (match top with
    |T s -> false
    |_ ->
      (let table_entry = BatMap.find_default BatSet.empty (top, w) table in
      if(BatSet.is_empty table_entry)
      then (false) (* 테이블 엔트리가 비어있음 *)
      else
        let (entry_to_push, _) = BatSet.pop table_entry in
        predictive_parsing table (entry_to_push@rest_stack) (w::rest_input)))

let parse : cfg -> symbol list -> bool
= fun cfg sentence ->
  let table = construct_parsing_table cfg in
  let (non_terminals, terminals, start, production) = cfg in
  let stack = start::[End] in
  predictive_parsing table stack sentence

(*
ocamlfind batteries/ocaml
*)