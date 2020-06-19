module Liveness = struct
  module SET = Set.Make(String)
type labeld_linstr = int*T.linstr
type labeld_program = labeld_linstr list
type livenessMap = (labeld_linstr, SET.t)PMap.t

let rec find_def_use_map : labeld_program -> (livenessMap * livenessMap) -> (livenessMap * livenessMap)
= fun pgm (defMap, useMap) ->
  let update
  = fun def_list use_list ->
    (let def = List.fold_left (fun result use_elt -> SET.add use_elt result) (SET.empty) def_list in
    let use = List.fold_left (fun result use_elt -> SET.add use_elt result) (SET.empty) use_list in
    let defMap_new = PMap.add (List.hd pgm) def defMap in
    let useMap_new = PMap.add (List.hd pgm) use useMap in
    find_def_use_map (List.tl pgm) (defMap_new, useMap_new)) in
  match pgm with
  |[] -> (defMap, useMap)
  |(_,(label, instr))::tl ->
    match instr with
    |ALLOC (x,n) -> update [x] []
    |ASSIGNV (x, bop, y, z) -> update [x] [y;z]
    |ASSIGNC (x, bop, y, num) -> update [x] [y]
    |ASSIGNU (x, uop, y) -> update [x] [y]
    |COPY (x, y) -> update [x] [y]
    |COPYC (x, _) -> update [x] []
    |CJUMP (x, _) -> update [] [x]
    |CJUMPF (x, _) -> update [] [x]
    |LOAD (x, (a,i)) -> update [x] [a;i]
    |STORE ((a,i), x) -> update [a] [a;i;x]
    |READ x -> update [x] []
    |WRITE x -> update [] [x]
    |_ -> update [] []

let map_equality_check : livenessMap -> livenessMap -> bool
= fun a b ->
    let sub_fold : livenessMap -> labeld_linstr -> SET.t -> bool -> bool
    = (fun map_to_compare a b result ->
      let result_this_loop = if(PMap.mem a map_to_compare) then SET.equal (PMap.find a map_to_compare) b else false in
      result && result_this_loop) in
    let contains : livenessMap -> livenessMap -> bool
    = fun a b -> PMap.foldi (sub_fold b) a true in
  (contains a b) && (contains b a)

let rec find_in_out_sub : labeld_program -> labeld_program -> (livenessMap * livenessMap) -> (livenessMap * livenessMap) -> (livenessMap * livenessMap)
= fun pgm_original pgm (defMap, useMap) (inMap, outMap) ->
  let find_in_with_pc = fun pc -> if(PMap.mem pc inMap) then PMap.find pc inMap else SET.empty in
  let find_pc_with_label = fun target_label -> List.filter (fun (_,(label,instr)) -> if(label=target_label) then true else false) pgm_original in
  let update
  = fun next_pc_list ->
    (let pc = List.hd pgm in
    let def = PMap.find pc defMap in
    let use = PMap.find pc useMap in
    let outSet = if(PMap.mem pc outMap) then PMap.find pc outMap else SET.empty in
    let inSet_new = SET.union use (SET.diff outSet def) in
    let outSet_new = List.fold_left (fun result pc -> SET.union result (find_in_with_pc pc)) SET.empty next_pc_list in
    let inMap_new = PMap.add pc inSet_new inMap in
    let outMap_new = PMap.add pc outSet_new outMap in
    find_in_out_sub pgm_original (List.tl pgm) (defMap, useMap) (inMap_new, outMap_new)) in
  match pgm with
  |[] -> (inMap, outMap)
  |[(_,(_, T.HALT))] -> (inMap, outMap)
  |(_,(label, instr))::tl ->
    match instr with
    |UJUMP l ->
      let next_pc_list = find_pc_with_label l in
      update next_pc_list
    |CJUMP (x,l)|CJUMPF (x,l) ->
      let jump_pc = find_pc_with_label l in
      let next_pc_list = (List.hd tl)::jump_pc in
      update next_pc_list
    |_ -> update [List.hd tl]

let find_in_out : labeld_program -> (livenessMap * livenessMap * livenessMap * livenessMap)
= fun pgm ->
    let rec fixed_point_iteration : ('a -> 'a) -> 'a -> 'a
    = fun f (in_input, out_input) ->
      let (in_after, out_after) = f (in_input, out_input) in
      if((map_equality_check in_input in_after)&&(map_equality_check out_input out_after)) then (in_input, out_input) else fixed_point_iteration f (in_after, out_after) in
  let (defMap, useMap) = find_def_use_map pgm (PMap.empty, PMap.empty) in
  let (inMap, outMap) = fixed_point_iteration (find_in_out_sub pgm pgm (defMap, useMap)) (PMap.empty, PMap.empty) in
  (defMap, useMap, inMap, outMap)

let deadcode_elimination_sub : labeld_program -> labeld_program
= fun pgm ->
    let detect_dead_code_fold
    = (fun (defMap,outMap) a s -> 
    let def = if(PMap.mem a defMap) then PMap.find a defMap else SET.empty in
    let out = if(PMap.mem a outMap) then PMap.find a outMap else SET.empty in
    if(SET.subset def out) then s else a::s) in (* 같지 않다 = 정의됐는데, 사용되지 않는다. dead 코드다. *)
    let rec eliminate_dead_code
    = (fun pgm_todo pgm_done dead_pgm ->
        let remove = fun () -> eliminate_dead_code (List.tl pgm_todo) pgm_done (List.tl dead_pgm) in
        let continue = fun () -> eliminate_dead_code (List.tl pgm_todo) (pgm_done@[List.hd pgm_todo]) dead_pgm in
      match dead_pgm with
      |[] -> pgm_done@pgm_todo
      |hd::tl -> if(hd=(List.hd pgm_todo)) then remove () else continue ()) in
  let (defMap, _, inMap, outMap) = find_in_out pgm in
  let dead_code = List.fold_right (detect_dead_code_fold (defMap, outMap)) pgm [] in
  eliminate_dead_code pgm [] dead_code

let deadcode_elimination : T.program -> T.program
= fun pgm ->
    let rec fixed_point_iteration : ('a -> 'a) -> 'a -> 'a
    = (fun f input ->
      let input_after = f input in
      if(input_after=input) then input else fixed_point_iteration f input_after) in
    let labeling : T.program -> labeld_program
    = fun pgm -> snd (List.fold_left (fun (num,result) linstr -> (num+1,result@[(num, linstr)])) (0,[]) pgm) in
    let unlabeling : labeld_program -> T.program
    = fun pgm -> List.fold_left (fun result labeld -> result@[(snd labeld)]) [] pgm in
  let labeld = labeling pgm in
  unlabeling (fixed_point_iteration deadcode_elimination_sub labeld)
end

module Constant = struct
  let tmp_var_num = ref 0
let new_tmp_var : unit -> string
= fun () ->
  tmp_var_num := !tmp_var_num - 1 ; ".t"^(string_of_int !tmp_var_num)

module SET = Set.Make(String)
module AValue = struct
  type t = Bot | Top | Constant of int
    (* partial order *)
    let order : t -> t -> bool 
    = fun c1 c2 ->
      if(c1=c2) then true
      else
        match c1, c2 with
        | Bot, _ -> true
        | _, Top -> true
        | _ -> false
  
    (* least upper bound *)
    let lub : t -> t -> t 
    = fun c1 c2 ->
      if(c1=c2) then c1
      else
        match c1, c2 with
        | Bot, _ -> c2
        | _, Bot -> c1
        | _ -> Top

    let decapsule : t -> int
    = fun input ->
      match input with
      |Constant n -> n
      |_ -> raise (Failure "decapsule 입력 에러")
end

type labeld_linstr = int*T.linstr
type labeld_program = labeld_linstr list
type constant_table = ((T.var*int), AValue.t) PMap.t
type table_Map = (labeld_linstr, constant_table)PMap.t

let unlabeling : labeld_program -> T.program
= fun pgm -> List.fold_left (fun result labeld -> result@[(snd labeld)]) [] pgm

let map_lub : constant_table -> constant_table -> constant_table
= fun a b ->
  let map_lub_sub : constant_table -> constant_table -> constant_table -> (T.var*int) ->  constant_table
  = (fun a b result key ->
    let val_a = if(PMap.mem key a) then PMap.find key a else AValue.Bot in
    let val_b = if(PMap.mem key b) then PMap.find key b else AValue.Bot in
    PMap.add key (AValue.lub val_a val_b) result) in
  let keys_a = PMap.foldi (fun key value result -> if(List.mem key result) then result else key::result) a [] in
  let keys_b = PMap.foldi (fun key value result -> if(List.mem key result) then result else key::result) b [] in
  let keys = keys_a@keys_b in
    List.fold_left (map_lub_sub a b) PMap.empty keys

let rec find_in_out_sub : labeld_program -> labeld_program -> (table_Map * table_Map) -> (table_Map * table_Map)
= fun pgm done_pgm_rev (inMap, outMap) ->
    let find_prev_list : T.label -> labeld_program
    = (fun label ->
      let rec find_label_linstr : T.label -> labeld_program -> (bool * labeld_linstr)
      = (fun label pgm->
        let continue = fun () -> find_label_linstr label (List.tl pgm) in
        match pgm with
        |[] -> (false,(0,(0,SKIP)))
        |(_,(_, instr))::tl ->
          (match instr with
          |UJUMP l -> if(label=l) then true,List.hd pgm else continue ()
          |CJUMP (var, l) -> if(label=l) then (true,List.hd pgm) else continue ()
          |CJUMPF (var, l) -> if(label=l) then (true,List.hd pgm) else continue ()
          |_ -> continue ())) in
      let pred_instr = if(done_pgm_rev=[]) then [] else [List.hd done_pgm_rev] in
      if(label=0) then pred_instr
      else (
        let (bool_flag, jump_instr) = find_label_linstr label (pgm@done_pgm_rev) in
        if(bool_flag) then jump_instr::pred_instr else pred_instr )) in
    let calc_in : labeld_program -> table_Map -> constant_table
    = (fun prev_list outMap ->
      match prev_list with
      |[] -> PMap.empty
      |[hd] -> if(PMap.mem hd outMap) then PMap.find hd outMap else PMap.empty
      |[hd;hd2] ->
        let out_hd = if(PMap.mem hd outMap) then PMap.find hd outMap else PMap.empty in
        let out_hd2 = if(PMap.mem hd2 outMap) then PMap.find hd2 outMap else PMap.empty in
        map_lub out_hd out_hd2
      |_ -> raise (Failure "prev가 둘 이상")) in
    let next = fun (inMap, outMap) -> find_in_out_sub (List.tl pgm) ((List.hd pgm)::done_pgm_rev) (inMap, outMap) in
    let rec array_init
    = (fun x num in_block ->
      let outblock = PMap.add (x,num) (AValue.Constant 0) in_block in
      if(num=0) then outblock else array_init x (num-1) outblock) in
    let rec array_to_top = fun x num in_block -> if(PMap.mem (x,num) in_block) then array_to_top x (num+1) (PMap.add (x,num) AValue.Top in_block) else in_block in
    let calc : (T.bop*int*int) -> int
    = (fun (bop,v1,v2) ->
      (* 수정 필요. 반례)test2.s, 다른 bop연산일 경우 프로그램 죽음 *)
      match bop with
      |ADD -> v1+v2
      |SUB -> v1-v2
      |MUL -> v1*v2
      |DIV -> v1/v2
      |LT -> if(v1<v2) then 1 else 0
      |LE -> if(v1<=v2) then 1 else 0
      |GT -> if(v1>v2) then 1 else 0
      |GE -> if(v1>=v2) then 1 else 0
      |EQ -> if(v1=v2) then 1 else 0
      |OR -> if((v1<>0)||(v2<>0)) then 1 else 0
      |AND -> if((v1<>0)&&(v2<>0)) then 1 else 0) in
  match pgm with
  |[] -> (inMap, outMap)
  |(_,(label, instr))::tl ->
    let prev_list = find_prev_list label in
    let in_block = calc_in prev_list outMap in
    let out_block =
      (match instr with
      |ALLOC (x,n) -> array_init x n in_block
      |ASSIGNV (x, T.AND, y, z) ->
        let find_y = PMap.find (y,-1) in_block in
        let find_z = PMap.find (z,-1) in_block in
        (match find_y, find_z with
        |Constant a, Constant b -> if(a=0||b=0) then PMap.add (x,-1) (AValue.Constant 0) in_block else PMap.add (x,-1) (AValue.Constant 1) in_block
        |_, Constant a |Constant a,_ -> if(a=0) then PMap.add (x,-1) (AValue.Constant 0) in_block else PMap.add (x,-1) (AValue.Top) in_block
        |_ -> PMap.add (x,-1) (AValue.Top) in_block)
      |ASSIGNV (x, T.OR, y, z) ->
        let find_y = PMap.find (y,-1) in_block in
        let find_z = PMap.find (z,-1) in_block in
        (match find_y, find_z with
        |Constant a, Constant b -> if(a<>0||b<>0) then PMap.add (x,-1) (AValue.Constant 1) in_block else PMap.add (x,-1) (AValue.Constant 0) in_block
        |_, Constant a |Constant a,_ -> if(a<>0) then PMap.add (x,-1) (AValue.Constant 1) in_block else PMap.add (x,-1) (AValue.Top) in_block
        |_ -> PMap.add (x,-1) (AValue.Top) in_block)
      |ASSIGNV (x, bop, y, z) -> (* x = y bop z *) (* ADD | SUB | MUL | DIV | LT | LE | GT | GE | EQ *)
        let find_y = PMap.find (y,-1) in_block in
        let find_z = PMap.find (z,-1) in_block in
        (match find_y, find_z with
        |Constant a, Constant b -> PMap.add (x,-1) (AValue.Constant (calc (bop, a, b))) in_block
        |_ -> PMap.add (x,-1) AValue.Top in_block)
      |ASSIGNC (x, bop, y, n) -> (* x = y bop n *)
        let find_y = PMap.find (y,-1) in_block in
        (match find_y with
        |Constant a -> PMap.add (x,-1) (AValue.Constant (calc (bop, a,n))) in_block
        |_ -> PMap.add (x,-1) AValue.Top in_block)
      |ASSIGNU (x, uop, y) ->  (* x = uop y *) (* MINUS | NOT *)
        let find_y = PMap.find (y,-1) in_block in
        (match find_y with
        |Constant a ->
          (match uop with
          |T.MINUS -> PMap.add (x,-1) (AValue.Constant (-a)) in_block
          |T.NOT -> PMap.add (x,-1) (if(a=0) then AValue.Constant 1 else Constant 0) in_block)
        |_ -> PMap.add (x,-1) AValue.Top in_block)
      |COPY (x,y) -> (* x = y *)
        PMap.add (x,-1) (PMap.find (y,-1) in_block) in_block
      |COPYC (x,n) -> (* x = n *)
        PMap.add (x,-1) (AValue.Constant n) in_block
      |LOAD (x, (a,i)) -> (* x = a[i] *)
        let find_i = PMap.find (i,-1) in_block in
        let find_a_i = (match find_i with
        |AValue.Constant n -> PMap.find (a,n) in_block
        |_ -> AValue.Top) in
        PMap.add (x,-1) find_a_i in_block
      |STORE ((a,i),x) -> (* a[i] = x *)
        let find_i = PMap.find (i,-1) in_block in
        let find_x = PMap.find (x,-1) in_block in
        if((find_x = AValue.Top)||find_i = AValue.Top) then array_to_top a 0 in_block else PMap.add (a, AValue.decapsule find_i) find_x in_block
      |READ x -> (* read x *)
        PMap.add (x,-1) (AValue.Top) in_block
      |_ -> in_block) in (* WRITE |UJUMP l|CJUMP (x,l)|CJUMPF(x,l)|SKIP|HALT *)
    next ((PMap.add (List.hd pgm) in_block inMap), (PMap.add (List.hd pgm) out_block outMap))

let table_equality_check : constant_table -> constant_table -> bool
= fun a b ->
  let sub_fold : constant_table -> (T.var*int) -> AValue.t -> bool -> bool 
  = (fun table_to_compare a b result ->
    let result_this_loop = if (PMap.mem a table_to_compare) then b = (PMap.find a table_to_compare) else false in
    result_this_loop && result) in
  let contains : constant_table -> constant_table -> bool
  = fun a b -> PMap.foldi (sub_fold b) a true in
  (contains a b) && (contains b a)

let map_equality_check : table_Map -> table_Map -> bool
= fun a b ->
    let sub_fold : table_Map -> labeld_linstr -> constant_table -> bool -> bool
    = (fun map_to_compare a b result ->
      let result_this_loop = if(PMap.mem a map_to_compare) then table_equality_check (PMap.find a map_to_compare) b else false in
      result_this_loop && result) in
    let contains : table_Map -> table_Map -> bool
    = fun a b -> PMap.foldi (sub_fold b) a true in
  (contains a b) && (contains b a)

let find_in_out : labeld_program -> (table_Map * table_Map)
= fun pgm ->
    let rec fixed_point_iteration : ('a -> 'a) -> 'a -> 'a
    = (fun f (in_input, out_input) ->
      let (in_after, out_after) = f (in_input, out_input) in
      if((map_equality_check in_input in_after)&&(map_equality_check out_input out_after)) then (in_input, out_input) else fixed_point_iteration f (in_after, out_after)) in
  fixed_point_iteration (find_in_out_sub pgm []) (PMap.empty, PMap.empty)

let rec constant_folding_sub : (labeld_program * labeld_program) -> (table_Map * table_Map) -> labeld_program
= fun (pgm, done_pgm) (inMap,outMap) ->
  let unlabeling : labeld_program -> T.program
  = fun pgm -> List.fold_left (fun result labeld -> result@[(snd labeld)]) [] pgm in
    let mem : constant_table -> (T.var*int) -> bool
    = (fun table input ->
    match PMap.find input table with
    |Constant c -> true
    |_ -> false) in
    let find = fun table input -> AValue.decapsule (PMap.find input table) in
    let continue = fun () -> constant_folding_sub ((List.tl pgm), (done_pgm@[List.hd pgm])) (inMap, outMap) in
    let find_num_label = fun () -> let (num, (label, _)) = List.hd pgm in (num, label) in
    let change
    = fun changed ->
    let (num, label) = find_num_label () in
    constant_folding_sub ((List.tl pgm), done_pgm@(List.map (fun x -> (num,(label,x))) changed)) (inMap, outMap) in
  match pgm with
  |[] -> done_pgm
  |(_,(label, instr))::tl ->
    let out_table = PMap.find (List.hd pgm) outMap in
    let in_table = PMap.find (List.hd pgm) inMap in
    match instr with
    | ASSIGNV (x,bop,y,z) -> (* x = y bop z *)
      if(mem out_table (x,-1)) then change [T.COPYC (x, find out_table (x,-1))]
      else
      (match bop with
      |SUB|DIV|LT|LE|GT|GE ->
        if(mem in_table (z,-1)) then change [ASSIGNC (x,bop,y,find in_table (z,-1))] else continue ()
      |_ ->
        if(mem in_table (z,-1)) then change [ASSIGNC (x,bop,y,find in_table (z,-1))]
        else (if(mem in_table (y,-1)) then change [ASSIGNC (x,bop,z,find in_table (y,-1))]
        else continue ()))
    | ASSIGNC (x,bop,y,n) -> (* x = y bop n *)
      if(mem out_table (x,-1)) then change [COPYC (x, find out_table (x,-1))] else continue ()
    | ASSIGNU (x,uop,y) -> (* x = uop y *)
      if(mem out_table (x,-1)) then change [COPYC (x, find out_table (x,-1))] else continue ()
    | COPY (x,y) ->    (* x = y *)
      if(mem out_table (x,-1)) then change [COPYC (x, find out_table (x,-1))] else continue ()
    | CJUMP (x,l) -> (* if x goto L *)
      if(mem out_table (x,-1) && ((String.get x 0) <> '.'))
      then
        (let tmp = new_tmp_var () in
        change [COPYC (tmp, find out_table (x,-1));CJUMP (tmp, l)]) else continue ()
    | CJUMPF (x,l) -> (* ifFalse x goto L *)
      if(mem out_table (x,-1) && ((String.get x 0) <> '.'))
      then
        (let tmp = new_tmp_var () in
        change [COPYC (tmp, find out_table (x,-1));CJUMPF (tmp, l)]) else continue ()
    | LOAD (x, (a,i)) ->     (* x = a[i] *)
      if(mem out_table (x,-1)) then change [COPYC (x, find out_table (x,-1))] else continue ()
    |_ -> continue () (* |STORE|READ|WRITE|UJUMP|HALT|SKIP|ALLOC|COPYC *) 

  (*
| SKIP
| ALLOC of var * int  (* x = alloc(n) *)
| ASSIGNV of var * bop * var * var (* x = y bop z *)
| ASSIGNC of var * bop * var * int (* x = y bop n *)
| ASSIGNU of var * uop * var  (* x = uop y *)
| COPY of var * var           (* x = y *)
| COPYC of var * int          (* x = n *)
| UJUMP of label              (* goto L *)
| CJUMP of var * label        (* if x goto L *)
| CJUMPF of var * label       (* ifFalse x goto L *)
| LOAD of var * arr           (* x = a[i] *)
| STORE of arr * var          (* a[i] = x *)
| READ of var                 (* read x *)
| WRITE of var                (* write x *)
| HALT
  *)

let constant_folding : T.program -> T.program
= fun pgm ->
    let labeling : T.program -> labeld_program
    = fun pgm -> snd (List.fold_left (fun (num,result) linstr -> (num+1,result@[(num, linstr)])) (0,[]) pgm) in
    let unlabeling : labeld_program -> T.program
    = fun pgm -> List.fold_left (fun result labeld -> result@[(snd labeld)]) [] pgm in
    let rec fixed_point_iteration : ((labeld_program * labeld_program) -> (table_Map * table_Map) -> labeld_program) -> T.program -> T.program
    = (fun f input ->
      let labeld = labeling input in
      let (inMap,outMap) = find_in_out labeld in
      let input_after = unlabeling (f (labeld, []) (inMap,outMap)) in
      if(input_after=input) then input else fixed_point_iteration f input_after) in
    fixed_point_iteration constant_folding_sub pgm

  (*
| SKIP
| ALLOC of var * int  (* x = alloc(n) *)
| ASSIGNV of var * bop * var * var (* x = y bop z *)
| ASSIGNC of var * bop * var * int (* x = y bop n *)
| ASSIGNU of var * uop * var  (* x = uop y *)
| COPY of var * var           (* x = y *)
| COPYC of var * int          (* x = n *)
| UJUMP of label              (* goto L *)
| CJUMP of var * label        (* if x goto L *)
| CJUMPF of var * label       (* ifFalse x goto L *)
| LOAD of var * arr           (* x = a[i] *)
| STORE of arr * var          (* a[i] = x *)
| READ of var                 (* read x *)
| WRITE of var                (* write x *)
| HALT
  *)
end

let rec omit_skip : T.program -> T.program -> T.program
= fun upper lower  ->
  let continue = fun () -> omit_skip (upper@(List.hd lower)::[]) (List.tl lower) in
  match lower with
  |[] -> upper
  |(label, T.SKIP)::tl ->
    (match tl with
    |[] -> raise (Failure "optimizer : HALT가 없음!")
    |(0, instr_2)::tl2 -> omit_skip (upper@(label, instr_2)::[]) tl2 
    |_ -> continue ()) (* SKIP 다음 instr에 label이 있을 경우, 합치지 않고 넘어감 *)
  |_ -> continue ()

  let rec optimize_unncessary_temp_var : T.program -> T.program -> T.program
  = fun done_block todo ->
      let continue = fun () -> optimize_unncessary_temp_var (done_block@[List.hd todo]) (List.tl todo) in
      let change_instr : T.linstr -> T.linstr -> T.program -> T.program
      = fun from to_linstr pgm -> List.fold_left (fun result linstr -> if(linstr=from) then result@[to_linstr] else result@[linstr]) [] pgm in
      let merge : T.linstr -> T.linstr -> T.program
      = (fun from to_linstr ->
        let todo_new = change_instr from to_linstr (List.tl todo) in
        optimize_unncessary_temp_var done_block todo_new) in
      let remove = fun () -> optimize_unncessary_temp_var (done_block) (List.tl todo) in
      let rec find_used_instr (* 쓰는 건 좀 더 생각해보자 *)
      = (fun var pgm ->
          let continue = fun () -> find_used_instr var (List.tl pgm) in
          let return = fun () -> true,List.hd pgm in
        let (label, instr) = List.hd pgm in
        match instr with
        | T.HALT -> if((List.length pgm)=1) then false,List.hd pgm else continue ()
        | T.ASSIGNV (_, _, y, z) -> if(y=var || z=var) then return () else continue ()
        | ASSIGNC (_, _, y, _) -> if(y=var) then return () else continue ()
        | ASSIGNU (_, _, y) -> if(y=var) then return () else continue ()
        | COPY (_, y) -> if(y=var) then return () else continue ()
        | CJUMP (x, _) -> if(x=var) then return () else continue ()
        | CJUMPF (x, _) -> if(x=var) then return () else continue () 
        | LOAD (x,(a,i)) -> if(i=var) then return () else continue () 
        | STORE ((a,i),x) -> if(x=var||i=var) then return () else continue ()
        | WRITE v -> if(v=var) then return () else continue () 
        |_ -> continue ()) in
      let calc : (T.bop*int*int) -> int
      = (fun (bop,v1,v2) ->
        (* 수정 필요. 반례)test2.s, 다른 bop연산일 경우 프로그램 죽음 *)
        match bop with
        |ADD -> v1+v2
        |SUB -> v1-v2
        |MUL -> v1*v2
        |DIV -> v1/v2
        |LT -> if(v1<v2) then 1 else 0
        |LE -> if(v1<=v2) then 1 else 0
        |GT -> if(v1>v2) then 1 else 0
        |GE -> if(v1>=v2) then 1 else 0
        |EQ -> if(v1=v2) then 1 else 0
        |OR -> if((v1<>0)||(v2<>0)) then 1 else 0
        |AND -> if((v1<>0)&&(v2<>0)) then 1 else 0) in
    match todo with
    |[] -> done_block
    |[(_,T.HALT)] -> done_block@todo  (* 여기서 걸리지 않으면 todo는 무조건 길이 2 이상 *)
    |(label,instr)::tl ->
      match instr with
      |ASSIGNV(tmp, bop, v1, v2) ->
        if(not ((String.get tmp 0) = '.')) then continue ()
        else begin
          let (bool_flag,(label_2,instr_2)) = find_used_instr tmp tl in
          if(not bool_flag) then remove () else
          (if(label_2 <> 0) then continue () else
          (match instr_2 with
          |COPY(v3, v4) -> if(tmp=v4) then merge (label_2,instr_2) (label, ASSIGNV(v3, bop, v1, v2)) else continue ()
          |_ -> continue ()))
        end
      |ASSIGNC(tmp, bop, v1, num) ->
        if(not ((String.get tmp 0) = '.')) then continue ()
        else begin
          let (bool_flag,(label_2,instr_2)) = find_used_instr tmp tl in
          if(not bool_flag) then remove () else
          (if(label_2 <> 0) then continue () else
          (match instr_2 with
          |COPY(v3, v4) ->
            if(tmp=v4) then merge (label_2,instr_2) (label, ASSIGNC(v3, bop, v1, num)) else continue ()
          |_ -> continue ()))
        end
      |COPYC (tmp, num) -> (* tmp=정수 꼴 *)
        if(not ((String.get tmp 0) = '.')) then continue ()
        else begin
          let (bool_flag,(label_2,instr_2)) = find_used_instr tmp tl in
          if(not bool_flag) then remove () else
          (if(label_2 <> 0) then continue () else
          (match instr_2 with
          |ASSIGNC(target, bop, v1, num2) -> if(tmp=v1) then merge (label_2,instr_2) (label, COPYC(target, calc(bop, num, num2))) else continue ()
          |ASSIGNV(target, bop, v1, v2) ->
            (match bop with
            |SUB|DIV|LT|LE|GT|GE -> if(v2=tmp) then merge (label_2,instr_2) (label, ASSIGNC(target, bop, v1, num)) else continue ()
            |_ ->
              if(v1=tmp) then merge (label_2,instr_2) (label, ASSIGNC(target, bop, v2, num)) (* SUB/DIV/LT/LE/GT/GE 순서가 연산 결과에 영향을 주는 경우 결과가 달라질 수 있음*)
              else (if(v2=tmp) then merge (label_2,instr_2) (label, ASSIGNC(target, bop, v1, num))
              else continue ()))
          |COPY (v1, v2) -> if(v2=tmp) then merge (label_2,instr_2) (label, COPYC(v1, num)) else continue ()
          |ASSIGNU (x, T.MINUS, v) -> if(tmp=v) then merge (label_2,instr_2) (label, COPYC(x, -num)) else continue ()
          |ASSIGNU (x, T.NOT, v) ->
            let result = if(num=0) then 1 else 0 in
            if(tmp=v) then merge (label_2,instr_2) (label, COPYC(x, result)) else continue ()
          |_ -> continue ()))
        end
      |COPY(tmp, var) ->
        if(not ((String.get tmp 0) = '.')) then continue ()
        else begin
          let (bool_flag,(label_2,instr_2)) = find_used_instr tmp tl in
          if(not bool_flag) then remove () else
          (if(label_2 <> 0) then continue () else
          (match instr_2 with
          |ASSIGNV(target, bop, v1, v2) ->
            (* 임시변수 tmp에 값을 대입한 후 바로 다른 값의 연산에 tmp를 사용하는 경우 *)                  
            if(tmp=v1) then merge (label_2,instr_2) (label, ASSIGNV(target, bop, var, v2))
            else (if(tmp=v2) then merge (label_2,instr_2) (label, ASSIGNV(target, bop, v1, var))
            else continue ())
          |ASSIGNC(target, bop, v1, num) -> if(tmp=v1) then merge (label_2,instr_2) (label, ASSIGNC(target, bop, var, num)) else continue ()
          |ASSIGNU (x, T.NOT, v) -> if(tmp=v) then merge (label_2,instr_2) (label, ASSIGNU (x, T.NOT, var)) else continue ()
          |COPY (v1, v2) -> if(v2=tmp) then merge (label_2,instr_2) (label, COPY(v1, var)) else continue ()
          |CJUMP (v, l) -> if(tmp=v) then merge (label_2,instr_2) (label, CJUMP(var, l)) else continue ()
          |CJUMPF (v, l) -> if(tmp=v) then merge (label_2,instr_2) (label, CJUMPF(var, l)) else continue ()
          |LOAD(x,(a,i)) -> if(tmp=i) then merge (label_2,instr_2) (label, LOAD(x,(a,var))) else continue ()
          |STORE((a,i),x) ->
            if(i=tmp) then merge (label_2,instr_2) (label, STORE((a,var), x))
            else (if(x=tmp) then merge (label_2,instr_2) (label, STORE((a,i), var))
            else continue ())
          |WRITE v -> if(v=tmp) then merge (label_2,instr_2) (label, WRITE var) else continue ()
          |_ -> continue ()))
        end
      |LOAD(tmp, (a,i)) ->
        if(not ((String.get tmp 0) = '.')) then continue ()
        else begin
          let (bool_flag,(label_2,instr_2)) = find_used_instr tmp tl in
          if(not bool_flag) then remove () else
          (if(label_2 <> 0) then continue () else
          (match instr_2 with
          |COPY (v1, v2) -> if(v2=tmp) then merge (label_2,instr_2) (label, LOAD(v1, (a,i))) else continue ()
          |_ -> continue ()))
        end
      |_ -> continue ()

(* 질문, char 타입 비교를 = 으로 해도 되느냐? *)

let rec optimize_unncessary_algebra : T.program -> T.program -> T.program
= fun done_block todo ->
  let continue = fun () -> optimize_unncessary_algebra (done_block@[List.hd todo]) (List.tl todo) in
  let merge = fun linstr -> optimize_unncessary_algebra (done_block@linstr::[]) (List.tl todo) in
  let remove = fun () -> optimize_unncessary_algebra done_block (List.tl todo) in
  match todo with
  |[] -> done_block
  |(label,instr)::tl ->
    match instr with
    |ASSIGNC (v1, (ADD|SUB), v2, 0) -> merge (label, COPY(v1, v2))
    |ASSIGNC (v1, MUL, v2, 0) -> merge (label, COPYC(v1, 0))
    |ASSIGNC (v1, MUL, v2, 1) -> merge (label, COPY(v1, v2))
    |ASSIGNC (v1, MUL, v2, 2) -> merge (label, ASSIGNV(v1, T.ADD, v2, v2))
    |ASSIGNC (v1, DIV, v2, 1) -> merge (label, COPY(v1, v2))
    |ASSIGNC (v1, AND, v2, 0) -> merge (label, COPYC(v1, 0))
    |ASSIGNC (v1, AND, v2, num) -> merge (label, COPY(v1, v2))
    |ASSIGNC (v1, OR, v2, 0) -> merge (label, COPY(v1, v2))
    |ASSIGNC (v1, OR, v2, num) -> merge (label, COPYC(v1, 1))
    |COPY (v1, v2) -> if(v1=v2) then remove () else continue ()
    |_ -> continue ()

let rec fixed_point_iteration : (T.program -> T.program -> T.program) -> T.program -> T.program
= fun f input ->
  let rec equal_check : T.program -> T.program -> bool
  = (fun a b ->
    match a,b with
    |[], [] -> true
    |_, []|[], _ -> false
    |hd::tl, hd2::tl2 -> if(hd=hd2) then equal_check tl tl2 else false) in
  let input_after = f [] input in
  if(equal_check input input_after) then input else fixed_point_iteration f input_after

let rec remove_unnecessary_goto : T.program -> T.program -> T.program
= fun done_block todo ->

  let replace_goto : T.label -> T.label -> T.program -> T.linstr -> T.program
  = fun from to_label result (label,instr) ->
    (match instr with
    | UJUMP l -> if(l=from) then result@[(label, UJUMP to_label)] else result@[(label,instr)]              (* goto L *)
    | CJUMP (x, l) -> if(l=from) then result@[(label, CJUMP (x, to_label))] else result@[(label,instr)]        (* if x goto L *)
    | CJUMPF (x,l) -> if(l=from) then result@[(label, CJUMPF (x, to_label))] else result@[(label,instr)]       (* ifFalse x goto L *)
    |_ -> result@[(label,instr)]) in

  let rec is_label_HALT : T.program -> T.label -> bool
  = fun pgm target_label ->
    (match pgm with
    |[(label,HALT)] -> if(label=target_label) then true else false
    |_ -> is_label_HALT (List.tl pgm) target_label) in

  let continue = fun () -> remove_unnecessary_goto (done_block@[List.hd todo]) (List.tl todo) in
  let remove = fun () -> remove_unnecessary_goto done_block (List.tl todo) in
  let change_to_HALT = fun () -> remove_unnecessary_goto (done_block@[(0, HALT)]) (List.tl todo) in
  match todo with
  |[] -> done_block
  |[(_,T.HALT)] -> done_block@todo  (* 여기서 걸리지 않으면 todo는 무조건 길이 2 이상 *)
  |(0, UJUMP l)::tl ->
    let (label_2, _) = (List.hd tl) in
    if(label_2 = l)
      then remove ()
      else (if(is_label_HALT tl l) then change_to_HALT () else continue ())
  |(label, UJUMP l)::tl ->
    let done_new = List.fold_left (replace_goto label l) [] done_block in
    let todo_new = List.fold_left (replace_goto label l) [] tl in
    remove_unnecessary_goto done_new todo_new
  |_ -> continue ()

let rec find_true_false_branch : T.program -> (T.label * T.label * T.label) -> (T.program * T.program) -> (T.program * T.program)
= fun pgm (label_t, label_f, label_exit) (branch_t, branch_f) -> (* progress_flag가 true면 true branch에 붙이고, false면 F에 붙임 *)
    let next_step = fun () -> if((List.length branch_f)=0) then find_true_false_branch (List.tl pgm) (label_t, label_f, label_exit) (branch_t@[List.hd pgm], branch_f) else find_true_false_branch (List.tl pgm) (label_t, label_f, label_exit) (branch_t, branch_f@[List.hd pgm]) in
    let false_branch_start
    = fun () ->
      let (0, UJUMP l) = List.hd (List.rev branch_t) in
      let label_exit = l in
      find_true_false_branch (List.tl pgm) (label_t, label_f, label_exit) (branch_t, [List.hd pgm]) in
  match pgm with
  |(label, _)::tl ->
    if(label = label_f) then false_branch_start ()
    else (if(label = label_exit) then ((branch_t, branch_f))
    else (next_step ()))
  |_ -> next_step ()

let rec eliminate_code
= fun pgm_todo pgm_done pgm_to_eliminate ->
    let remove = fun () -> eliminate_code (List.tl pgm_todo) pgm_done (List.tl pgm_to_eliminate) in
    let continue = fun () -> eliminate_code (List.tl pgm_todo) (pgm_done@[List.hd pgm_todo]) pgm_to_eliminate in
  match pgm_to_eliminate with
  |[] -> pgm_done@pgm_todo
  |hd::tl -> if(hd=(List.hd pgm_todo)) then remove () else continue ()

[@@@warning "-8"]
let rec always_true_false_opt : T.program -> T.program -> T.program
= fun done_block todo ->
    let continue = fun () -> always_true_false_opt (done_block@[List.hd todo]) (List.tl todo) in
    let remove_branch
    = (fun which_branch (label_t, label_f) ->
      let (branch_t, branch_f) = find_true_false_branch (List.tl (List.tl todo)) (label_t, label_f, -1) ([], []) in
      let todo_new = if(which_branch) then eliminate_code (List.tl (List.tl todo)) [] (branch_t@[List.hd branch_f]) else eliminate_code (List.tl (List.tl todo)) [] ((List.hd branch_t)::branch_f) in
      (*always_true_false_opt done_block todo_new*) (List.rev(List.tl(List.rev done_block)))@todo_new) in
  match todo with
  |[] -> done_block
  |(0, CJUMP(t1, label_t))::tl ->
    let done_rev = List.rev done_block in
    let (label_before, instr) = List.hd done_rev in
    if(label_before <> 0) then continue ()
    else begin
      match instr with
      |COPYC (x,num) ->
        let (_, UJUMP label_f) = List.hd tl in
        remove_branch (num=0) (label_t, label_f)
      |_ -> continue ()
    end
  |_ -> continue ()
[@@@warning "+8"]

let rec if_to_iffalse : T.program -> T.program -> T.program
= fun done_block todo ->
  let continue = fun () -> if_to_iffalse (done_block@[List.hd todo]) (List.tl todo) in
  let merge = fun linstr -> if_to_iffalse done_block (linstr::(List.tl (List.tl todo))) in
  match todo with
  |[] -> done_block
  |(0, CJUMP(t1, label_t))::tl ->
    (match tl with
    |(0, UJUMP label_f)::tl2 -> merge (0, CJUMPF(t1, label_f))
    |_ -> continue ())
  |_ -> continue ()
    
let optimize_sub : T.program -> T.program
= fun t ->
  let tmp_omitted = fixed_point_iteration optimize_unncessary_temp_var t in
  let algebra_optimized = optimize_unncessary_algebra [] tmp_omitted in
  let tmp_omitted = fixed_point_iteration optimize_unncessary_temp_var algebra_optimized in
  let branch_optimized = always_true_false_opt [] tmp_omitted in
  (*goto_optimized*)
  let liveness = Liveness.deadcode_elimination branch_optimized in
  let constant = Constant.constant_folding liveness in
  constant

  let rec fixed_point_iteration2 : (T.program -> T.program -> T.program) -> T.program -> T.program
  = fun f input ->
    let rec equal_check : T.program -> T.program -> bool
    = (fun a b ->
      match a,b with
      |[], [] -> true
      |_, []|[], _ -> false
      |hd::tl, hd2::tl2 -> if(hd=hd2) then equal_check tl tl2 else false) in
    let input_after = f [] input in
    if(equal_check input input_after) then input else fixed_point_iteration f input_after

let optimize : T.program -> T.program
= fun t ->
    let rec fixed_point_iteration : (T.program -> T.program) -> T.program -> T.program
    = (fun f input ->
        let rec equal_check : T.program -> T.program -> bool
        = (fun a b ->
          match a,b with
          |[], [] -> true
          |_, []|[], _ -> false
          |hd::tl, hd2::tl2 -> if(hd=hd2) then equal_check tl tl2 else false) in
        let input_after = f input in
        if(equal_check input input_after) then input else fixed_point_iteration f input_after) in
  let after_fix = fixed_point_iteration optimize_sub t in
  let if_optimized = if_to_iffalse [] after_fix in
  let skip_omitted = omit_skip [] if_optimized in
  let goto_optimized = fixed_point_iteration2 remove_unnecessary_goto skip_omitted in
  goto_optimized