open Ast


let rec command_list_2_str (cs: command list) : string =
  let format_command (c: command) : string = 
    command2str c in
  let command_strs = List.map format_command cs in
  String.concat "\n" command_strs

and command2str (c: command) : string =
  match c with
  | Def {x; t; e} -> 
      Printf.sprintf "Def %s : %s := %s." x (term2str t) (term2str e)
  | DefWithoutType {x; e} -> 
      Printf.sprintf "Def %s := %s." x (term2str e)
  | Var {x; t}    -> 
      Printf.sprintf "Var %s : %s." x (term2str t) 
  | Check e      -> 
      Printf.sprintf "Check %s." (term2str e)
  | Show x       ->
      Printf.sprintf "Show %s." x
  | ShowAll      ->
      Printf.sprintf "ShowAll."
  | Undo         ->
      Printf.sprintf "Undo."
  | Pause       ->
      Printf.sprintf "Pause."
  | Prove {x; p}  ->
      Printf.sprintf "Prove %s : %s." x (term2str p)
  | Tactic t      ->
      (tactic2str t)
  | QED -> "QED."

and tactic2str (t: tactic) : string =
  match t with
  | Sorry -> "sorry."
  | Expand x -> Printf.sprintf "expand %s." x
  | Refl -> "refl."
  | Destruct v -> Printf.sprintf "destruct %s." v
  | Case e -> Printf.sprintf "case %s." (term2str e)
  | Intro v -> Printf.sprintf "intro %s." v
  | Revert v -> Printf.sprintf "revert %s." v
  | Apply e -> Printf.sprintf "apply %s." (term2str e)
  | Choose i -> Printf.sprintf "choose %d." i
  | Split -> "split."
  | ByLean -> "by_lean."
  | Simpl -> "simpl."
  | Rewrite_L2R e -> Printf.sprintf "rewrite %s." (term2str e)
  | Rewrite_R2L e -> Printf.sprintf "rewrite <- %s." (term2str e)
  | RWRULE r -> Printf.sprintf "rwrule %s." (rwrule2str r)

  | R_PRE e -> Printf.sprintf "r_pre %s." (term2str e)
  | R_POST e -> Printf.sprintf "r_post %s." (term2str e)
  | R_SKIP -> "r_skip."
  | R_SEQ (n1, n2, t) -> Printf.sprintf "r_seq %d %d %s." n1 n2 (term2str t)
  | R_ASSIGN      ->   "r_assign."
  | R_INITQ         -> "r_initq."
  | R_UNITARY       -> "r_unitary."
  | R_MEAS          -> "r_meas."
  | R_IF qs          -> Printf.sprintf "r_if %s." (term2str qs)
  | R_WHILE (qs, phi) -> Printf.sprintf "r_while %s %s." (term2str qs) (term2str phi)
  | R_WHILE_WHILE (qs, phi) -> Printf.sprintf "r_while_while %s %s." (term2str qs) (term2str phi)
  | R_MEAS_MEAS switch -> if switch then "r_meas_meas id." else "r_meas_meas swap."
  | R_MEAS_SAMPLE switch -> if switch then "r_meas_sample id." else "r_meas_sample swap."

  | JUDGE_SWAP -> "judge_swap."
  | CQ_ENTAIL -> "cq_entail."
  | DIRAC -> "dirac."
  | SIMPL_ENTAIL -> "simpl_entail."
  | ENTAIL_TRANS e -> Printf.sprintf "entail_trans %s." (term2str e)
  | CYLINDER_EXT e -> Printf.sprintf "cylinder_ext %s." (term2str e)

and term2str (e: terms) : string =
    match e with
    (* special case, nondependent forall is printed as arrow *)
    | Fun {head; args=[Symbol x; t; t']} when head = _forall && not (List.mem x (get_symbols t')) ->
        Printf.sprintf "(%s -> %s)" (term2str t) (term2str t')

    | Fun {head; args=[Symbol x; t; t']} when head = _forall->
        Printf.sprintf "(forall (%s : %s), %s)" x (term2str t) (term2str t')
    | Fun {head; args=[Symbol x; t; e]} when head = _fun->
        Printf.sprintf "(fun (%s : %s) => %s)" x (term2str t) (term2str e)
    | Fun {head; args=[f; t]} when head = _apply->
        Printf.sprintf "(%s @ %s)" (term2str f) (term2str t)

    (* star *)
    | Fun {head; args=[t1; t2]} when head = _star ->
        Printf.sprintf "(%s * %s)" (term2str t1) (term2str t2)

    (* pair *)
    | Fun {head; args=[t1; t2]} when head = _pair ->
        Printf.sprintf "(%s, %s)" (term2str t1) (term2str t2)

    (* list *)
    | Fun {head; args=tls} when head = _list ->
        let args_str = List.map term2str tls |> String.concat ", " in
        Printf.sprintf "[%s]" args_str

    (* dirac notation *)
    | Fun {head; args =[t]} when head = _ket ->
        Printf.sprintf "|%s>" (term2str t)
    | Fun {head; args=[t]} when head = _bra ->
        Printf.sprintf "<%s|" (term2str t)
    | Fun {head; args=[t]} when head = _adj ->
        Printf.sprintf "(%s^D)" (term2str t)

    | Fun {head; args=[t1; t2]} when head = _zeroo ->
        Printf.sprintf "0O[%s, %s]" (term2str t1) (term2str t2)
    | Fun {head; args=[t]} when head = _oneo ->
        Printf.sprintf "1O[%s]" (term2str t)

    | Fun {head; args=[t1; t2]} when head = _plus ->
        Printf.sprintf "(%s + %s)" (term2str t1) (term2str t2)
    
    | Fun {head; args=[q; t2]} when head = _tr ->
        Printf.sprintf "tr_%s(%s)" (term2str q) (term2str t2)


    | Fun {head; args=[t1; t2]} when head = _subscript ->
        Printf.sprintf "%s_%s" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _eqeq ->
        Printf.sprintf "(%s == %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _wedge ->
        Printf.sprintf "(%s /\\ %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _vee ->
        Printf.sprintf "(%s \\/ %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t]} when head = _not ->
        Printf.sprintf "(~ %s)" (term2str t)

    | Fun {head; args=[t1; t2]} when head = _imply ->
        Printf.sprintf "(%s -> %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _guarded ->
        Printf.sprintf "(%s |-> %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _atat ->
        Printf.sprintf "(%s @@ %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _vbar ->
        Printf.sprintf "(%s | %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _eq ->
        Printf.sprintf "(%s = %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _entailment ->
        Printf.sprintf "(%s <= %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[pre; s1; s2; post]} when head = _judgement ->
        Printf.sprintf "\n{%s}\n%s\n ~ \n%s\n{%s}" 
          (term2str pre) (term2str s1) (term2str s2) (term2str post)

    | Fun {head; args=[t1; t2; t3]} when head = _qcoupling ->
        Printf.sprintf "(%s, %s #, %s)" 
          (term2str t1) (term2str t2) (term2str t3)

    (* program statements *)
    | Symbol x when x = _skip ->
        "skip"
      
    | Fun {head; args=[Symbol x; t]} when head = _assign ->
        Printf.sprintf "%s := %s" x (term2str t)

    | Fun {head; args=[Symbol x; t]} when head = _passign ->
        Printf.sprintf "%s <-$ %s" x (term2str t)
    
    | Fun {head; args=[q]} when head = _init_qubit ->
        Printf.sprintf "init %s" (term2str q)
    
    | Fun {head; args=[u_opt; qs]} when head = _unitary ->
        Printf.sprintf "unitary %s %s" (term2str u_opt) (term2str qs)
    
    | Fun {head; args=[Symbol x; m_opt; qs]} when head = _meas ->
        Printf.sprintf "%s := meas %s %s" x (term2str m_opt) (term2str qs)

    | Fun {head; args=[b; s1; s2]} when head = _if ->
        Printf.sprintf "if %s then %s else %s end" 
          (term2str b) (term2str s1) (term2str s2)
  
    | Fun {head; args=[b; s]} when head = _while ->
        Printf.sprintf "while %s do %s end" 
          (term2str b) (term2str s)

    | Fun {head; args} when head = _seq ->
        let args_str = List.map term2str args |> String.concat ";\n" in
        Printf.sprintf "%s;" args_str

    | Symbol x -> 
        Printf.sprintf "%s" x

    | Fun {head; args} ->
        let args_str = List.map term2str args |> String.concat ", " in
        Printf.sprintf "%s[%s]" head args_str

    | Opaque ->
        Printf.sprintf "<opaque>"

and rwrule2str (r: rewriting_rule) : string =
  match r with
  | {lhs; rhs; typings = []} ->
      Printf.sprintf "%s --> %s" (term2str lhs) (term2str rhs)
  
  | {lhs; rhs; typings} ->
    let typings_str =
        (List.map (fun (x, t) -> Printf.sprintf "%s : %s" (term2str x) (term2str t)) typings)
    |> String.concat ", " in
    Printf.sprintf "%s |- %s --> %s" typings_str (term2str lhs) (term2str rhs)
