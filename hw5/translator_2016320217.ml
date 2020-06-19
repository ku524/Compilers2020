let label = ref 0
let tmp_var_num = ref 0

let new_label : unit -> int
= fun () ->
  label := !label+1;!label

let new_tmp_var : unit -> string
= fun () ->
  tmp_var_num := !tmp_var_num + 1 ; ".t"^(string_of_int !tmp_var_num)

let translate_declaration : S.decl -> T.program
= fun (typ, var) ->
  match typ with
  |TINT -> [(0, T.COPYC (var, 0))]
  |TARR n -> [(0, T.ALLOC (var,n))]

let trans_decl_fold : T.program -> S.decl -> T.program
= fun result decl ->
  result@(translate_declaration decl)

[@@@warning "-8"]
let find_bop : S.exp -> T.bop
= fun exp ->
  match exp with
  | ADD (e1, e2) -> T.ADD
  | SUB (e1, e2) -> T.SUB
  | MUL (e1, e2) -> T.MUL
  | DIV (e1, e2) -> T.DIV
  | LT (e1, e2) -> T.LT
  | LE (e1, e2) -> T.LE
  | GT (e1, e2) -> T.GT
  | GE (e1, e2) -> T.GE
  | EQ (e1, e2) -> T.EQ
  | AND (e1, e2) -> T.AND
  | OR  (e1, e2) -> T.OR

let find_uop : S.exp -> T.uop
= fun exp ->
  match exp with
  | MINUS e -> T.MINUS
  | NOT e -> T.NOT
[@@@warning "+8"]

let rec translate_exp : S.exp -> (T.var *  T.program)
= fun exp ->
  match exp with
  | NUM n ->
    let tmp = new_tmp_var () in
    (tmp, (0, COPYC (tmp, n))::[])
  | LV lv ->
    begin
      match lv with
      |ID id ->
        let tmp = new_tmp_var () in
        (tmp, (0, COPY (tmp, id))::[])
      |ARR (id, exp_sub) ->
        let (var, pgm1) = translate_exp exp_sub in
        let tmp = new_tmp_var () in
        (tmp, pgm1@[(0, LOAD (tmp, (id, var)))])
    end
  | MINUS e | NOT e ->
    let (t1, code1) = translate_exp e in
    let tmp = new_tmp_var () in
    (tmp, code1@[(0, ASSIGNU (tmp, find_uop exp, t1))])
  | ADD(e1,e2)|SUB(e1,e2)|MUL(e1,e2)|DIV (e1,e2)|LT(e1,e2)|LE(e1,e2)|GT(e1,e2)|GE(e1,e2)|EQ(e1,e2)|AND(e1,e2)|OR(e1,e2) ->
    let (t1, code1) = translate_exp e1 in
    let (t2, code2) = translate_exp e2 in
    let tmp = new_tmp_var () in
    (tmp, code1@code2@[(0, ASSIGNV (tmp, find_bop exp, t1, t2))])

let rec translate_stmt : S.stmt -> T.program
= fun stmt ->
  match stmt with
  | ASSIGN (lv, e) -> (* lv = exp *)
    let (t1, code1) = translate_exp e in
    begin
      match lv with
      |ID id ->
        code1@[(0, COPY(id, t1))]
      |ARR (id, exp_sub) ->
        let (t2, code2) = translate_exp exp_sub in
        code1@code2@[(0, STORE((id, t2), t1))]
    end
  | IF (e, s1, s2) ->
    let (t1, code1) = translate_exp e in
    let code_t = translate_stmt s1 in
    let code_f = translate_stmt s2 in
    let label_t = new_label () in
    let label_f = new_label () in
    let label_exit = new_label () in
    code1@
    ((0, T.CJUMP(t1, label_t))
    ::(0, T.UJUMP label_f)
    ::(label_t, T.SKIP)::[])
    @code_t@
    ((0, T.UJUMP label_exit)
    ::(label_f, T.SKIP)::[])
    @code_f@
    ((0, T.UJUMP label_exit)
    ::(label_exit, T.SKIP)::[])
  | WHILE (e, stmt_sub) ->
    let (t1, code1) = translate_exp e in
    let code_b = translate_stmt stmt_sub in
    let label_enter = new_label () in
    let label_exit = new_label () in
    [(label_enter, T.SKIP)]@
    code1@
    [(0, T.CJUMPF (t1, label_exit))]@
    code_b@
    [(0, (T.UJUMP label_enter))]@
    [(label_exit, T.SKIP)]
  | DOWHILE (stmt_sub, e) ->
    (translate_stmt stmt_sub)@(translate_stmt (S.WHILE (e, stmt_sub)))
  | READ id -> [(0, T.READ id)]
  | PRINT e ->
    let (t1, code1) = translate_exp e in
    code1@[(0, T.WRITE t1)]
  | BLOCK (dec_list, stmt_list) ->
    let trans_stmt_fold : T.program -> S.stmt -> T.program
    = (fun result stmt ->
      result@(translate_stmt stmt)) in
    let pgm_after_decl = List.fold_left trans_decl_fold [] dec_list in
    List.fold_left trans_stmt_fold pgm_after_decl stmt_list

let trans_stmt_fold : T.program -> S.stmt -> T.program
= fun result stmt ->
  result@(translate_stmt stmt)

let translate : S.program -> T.program
= fun (dec_list, stmt_list) -> 
  let pgm_after_decl = List.fold_left trans_decl_fold [] dec_list in
  (List.fold_left trans_stmt_fold pgm_after_decl stmt_list)
  @[(0,T.HALT)]