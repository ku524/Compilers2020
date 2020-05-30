open Regex 

exception Not_implemented

let merge_nfa : Nfa.t -> Nfa.t -> Nfa.t
= fun big small -> Nfa.add_edges (Nfa.add_states big (Nfa.get_states small)) (Nfa.get_edges small)

let from_old_to_new_epsilon : Nfa.state -> Nfa.state -> Nfa.t -> Nfa.t
= fun dest from nfa -> Nfa.add_epsilon_edge nfa (from, dest)

let new_nfa : unit -> (Nfa.state * Nfa.state * Nfa.t)
= fun unit ->
  let (new_final, nfa_tmp) = Nfa.create_state (Nfa.create_new_nfa ()) in
  let nfa = Nfa.add_final_state nfa_tmp new_final in
  ((Nfa.get_initial_state nfa), new_final, nfa)

let rec regex2nfa : Regex.t -> Nfa.t 
= fun regex -> 
  match regex with
  | Empty -> Nfa.create_new_nfa ()
  | Epsilon ->
    let nfa1 = Nfa.create_new_nfa () in
    let (new_state,nfa2) = Nfa.create_state nfa1 in
    let nfa3 = Nfa.add_epsilon_edge nfa2 (Nfa.get_initial_state nfa2, new_state) in
      Nfa.add_final_state nfa3 new_state
  | Alpha a -> 
    let nfa1 = Nfa.create_new_nfa () in
    let (new_state,nfa2) = Nfa.create_state nfa1 in
    let nfa3 = Nfa.add_edge nfa2 (Nfa.get_initial_state nfa2, a, new_state) in
      Nfa.add_final_state nfa3 new_state
  | OR (e1, e2) ->
    let nfa_e1 = regex2nfa e1 in
    let nfa_e2 = regex2nfa e2 in
    let (new_init, new_final, nfa_tmp) = (new_nfa ()) in
    let nfa_e1_states_edges = merge_nfa nfa_tmp nfa_e1 in
    let nfa_e1_init = Nfa.add_epsilon_edge nfa_e1_states_edges (new_init, Nfa.get_initial_state nfa_e1) in
    let nfa_e1_merge = BatSet.fold (from_old_to_new_epsilon new_final) (Nfa.get_final_states nfa_e1) nfa_e1_init in
    let nfa_e2_states_edges = merge_nfa nfa_e1_merge nfa_e2 in
    let nfa_e2_init = Nfa.add_epsilon_edge nfa_e2_states_edges (new_init, Nfa.get_initial_state nfa_e2) in
    let nfa_e2_merge = BatSet.fold (from_old_to_new_epsilon new_final) (Nfa.get_final_states nfa_e2) nfa_e2_init in
    nfa_e2_merge
  | CONCAT (e1, e2) ->
    let nfa_e1 = regex2nfa e1 in
    let nfa_e2 = regex2nfa e2 in
    let nfa_1 = merge_nfa (Nfa.create_new_nfa ()) nfa_e1 in
    let nfa_2 = (merge_nfa nfa_1 nfa_e2) in
    let nfa_before = BatSet.fold (from_old_to_new_epsilon (Nfa.get_initial_state nfa_e2)) (Nfa.get_final_states nfa_e1) nfa_2 in (* e1 final -> e2 initial *)
    let nfa_set_final = BatSet.fold (fun x a -> Nfa.add_final_state a x) (Nfa.get_final_states nfa_e2) nfa_before in (* e2 final -> new final *)
    let nfa_complete = Nfa.add_epsilon_edge nfa_set_final (Nfa.get_initial_state nfa_set_final, Nfa.get_initial_state nfa_e1) in
    nfa_complete
  | STAR e ->
    let nfa_e = regex2nfa e in
    let (new_init, new_final, nfa_new) = (new_nfa ()) in
    let nfa_merge = merge_nfa nfa_new nfa_e in
    let nfa_new_init = Nfa.add_epsilon_edge nfa_merge (new_init, Nfa.get_initial_state nfa_e) in
    let nfa_init_to_final = Nfa.add_epsilon_edge nfa_new_init (new_init, new_final) in
    let nfa_reverse_epsilon = BatSet.fold (fun x a -> Nfa.add_epsilon_edge a (x, Nfa.get_initial_state nfa_e)) (Nfa.get_final_states nfa_e) nfa_init_to_final in
    let nfa_complete = BatSet.fold (fun x a -> Nfa.add_epsilon_edge a (x, new_final)) (Nfa.get_final_states nfa_e) nfa_reverse_epsilon in
    nfa_complete    

(* next epsilon 계산을 한바퀴 돌았는데도 본래 states와 차이가 없다면 그 states를 반환. 있으면 없을 떄까지 계속한다. *)
let rec fixed_point_iteration : ('a -> 'a) -> 'a -> 'a
= fun f states ->
if ((f states) = states) then states
  else fixed_point_iteration f (f states)

(* 주어진 states를 돌면서 구성 state마다 갈 수 있는 next_epsilon을 계산하고, result states에 합친다. *)
let rec epsilon_closure_for_fixed_point : Nfa.t -> Dfa.state -> Dfa.state
= fun nfa states ->
BatSet.fold (fun source result -> BatSet.union result (Nfa.get_next_state_epsilon nfa source)) states (BatSet.union states BatSet.empty)

(* fixed point 연산을 합쳐 최종적으로 주어진 states에서 epsilon-closure를 구하는 함수 *)
let epsilon_closure : Nfa.t -> Dfa.state -> Dfa.state
= fun nfa states -> fixed_point_iteration (epsilon_closure_for_fixed_point nfa) states

let find_next_states : Nfa.t -> Dfa.state -> alphabet -> Dfa.state
= fun nfa states alphabet ->
  let next_states_alpha = BatSet.fold (fun state states -> BatSet.union (Nfa.get_next_state nfa state alphabet) states) states BatSet.empty in
  let after_closure = epsilon_closure nfa next_states_alpha in
  after_closure

let rec nfa2dfa_sub : Nfa.t -> Dfa.state BatSet.t -> alphabet list -> (Dfa.t * Dfa.states) -> (Dfa.t * Dfa.states)
= fun nfa work_list alphabet (dfa, dfa_states) ->
  match BatSet.is_empty work_list with
  |true -> (dfa, dfa_states)
  |false ->
    (let (q, work_list_new) = BatSet.pop work_list in
    let rec nfa2dfa_sub_alpha : Dfa.state -> Nfa.t -> Dfa.state BatSet.t -> alphabet list -> (Dfa.t * Dfa.states) -> (Dfa.t * Dfa.states)
    = (fun q nfa work_list alphabet (dfa, dfa_states) ->
      match alphabet with
      |[] -> nfa2dfa_sub nfa work_list [A; B] (dfa, dfa_states)
      |hd::tl ->
        let c = hd in
        let t = find_next_states nfa q c in
        match BatSet.mem t dfa_states with
        |true ->
          (let dfa_complete = Dfa.add_edge dfa (q, c, t) in
          nfa2dfa_sub_alpha q nfa work_list tl (dfa_complete, dfa_states))
        |false ->
          let dfa_new = Dfa.add_state dfa t in
          let work_list_new = BatSet.add t work_list in
          let dfa_states_new = BatSet.add t dfa_states in
          let dfa_complete = Dfa.add_edge dfa_new (q, c, t) in
          nfa2dfa_sub_alpha q nfa work_list_new tl (dfa_complete, dfa_states_new)) in
      nfa2dfa_sub_alpha q nfa work_list_new alphabet (dfa, dfa_states))
      
let nfa2dfa : Nfa.t -> Dfa.t
=fun nfa ->
  let new_initial = (epsilon_closure nfa (BatSet.add (Nfa.get_initial_state nfa) BatSet.empty)) in
  let work_list = BatSet.add new_initial BatSet.empty in
  let dfa_first = Dfa.create_new_dfa new_initial in
  let (dfa_before, dfa_states) = nfa2dfa_sub nfa work_list [A; B] (dfa_first, work_list) in
  (* 1차 : final state 꺼내기, 2차 : dfa_state 꺼내기, 3차 : 비교하기 *)
  let marking_accept_state
  = fun dfa_states nfa_final_state dfa ->
  let marking_accept_state_sub
  = (fun nfa_final_state dfa_state dfa ->
    if(BatSet.mem nfa_final_state dfa_state) then Dfa.add_final_state dfa dfa_state else dfa) in
  BatSet.fold (marking_accept_state_sub nfa_final_state) dfa_states dfa in
  let nfa_final = Nfa.get_final_states nfa in
  let dfa_complete = BatSet.fold (marking_accept_state dfa_states) nfa_final dfa_before in
  dfa_complete
  (* fold : fold f s a 형태로 입력을 받으며, s를 돌면서 (… f x1 (f x0 a))식으로 계산한다. 출력형은 a
  f : x -> a -> a
  iter : iter f s 형태로 입력을 받으며, s를 돌면서 f a_n 를 실행한다. 출력형은 unit
  map : map f x 형태로 입력을 받으며 x를 돌면서 f a_n을 실행한 놈들을 모아 새로운 set을 반환한다. 출력형은 'b t
  *)

(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa str ->
  let rec run_dfa_sub : Dfa.t -> alphabet list -> Dfa.state -> bool
  = (fun dfa str state_now ->
    match str with
    |hd::tl -> run_dfa_sub dfa tl (Dfa.get_next_state dfa state_now hd)
    |[] -> Dfa.is_final_state dfa state_now) in
    run_dfa_sub dfa str (Dfa.get_initial_state dfa)
