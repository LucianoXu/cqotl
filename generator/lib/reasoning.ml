
open Ast
open Ast_transform
open Utils 
open Parser_utils
open Typing
(* open Pretty_printer *)


(** the term rewriting rules in *)
let simpl_rules = [  
  parse_rw_rule "X /\\ (true = true) --> X";
  parse_rw_rule "(true = true) /\\ X --> X";

  parse_rw_rule "false /\\ false --> false";
  parse_rw_rule "true -> false --> false";
  parse_rw_rule "A : CTerm[BIT] |- true -> A --> A";
  parse_rw_rule "A : CTerm[BIT] |- false -> A --> true";
  parse_rw_rule "A -> true --> true";
  parse_rw_rule "A -> false --> ~ A";

  parse_rw_rule "A -> A --> true";
  parse_rw_rule "~ ~ A --> A";
  parse_rw_rule "~ A -> A --> A";
  parse_rw_rule "A /\\ true --> A";
  parse_rw_rule "true /\\ A --> A";
  parse_rw_rule "true \\/ A --> true";
  parse_rw_rule "A \\/ true --> true";
  parse_rw_rule "false \\/ A --> A";
  parse_rw_rule "A \\/ false --> A";

  parse_rw_rule "true |-> A --> A";
  parse_rw_rule "A : OType[T, T] |- false |-> A_q --> 1O[T]_q";
  parse_rw_rule "true -> true --> true";
  parse_rw_rule "A == A --> true";
  parse_rw_rule "true == false --> false";
  parse_rw_rule "false == true --> false";
  parse_rw_rule "A : CTerm[BIT] |- ~ A \\/ A --> true";
  parse_rw_rule "~ true --> false";
  parse_rw_rule "~ false --> true";

  parse_rw_rule "(~ b1 -> 0O[T, T]_(q, q)) /\\ (~ b2 -> 0O[T, T]_(q, q)) --> (~ (b1 /\\ b2) -> 0O[T, T]_(q, q))";
]


let simpl (typing: wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms =
  let simpl_transforms = List.map (fun r -> apply_rewriting_rule_all r typing wfctx) simpl_rules
  in
  (* apply_rewriting_rule  *)
  repeat_transforms simpl_transforms t

(* destruct the cq-assertion entailment *)
let cq_entailment_destruct (t : terms) : terms option = 
  (* get /\_{i: cj -> bi} Pi *)
  let rec aux_i cj qj t : terms option =
    match t with
    (* boundary case: bi -> pi *)
    | Fun {head; args=[bi; pi]} when head = _imply -> 
      Some (
        Fun {
          head = _guarded;
          args = [
            Fun {
              head = _imply;
              args = [cj; bi]
            };
            pi;
          ]
        }
      )
    | Fun {head; args=[phi1; phi2]} when head = _wedge ->
      begin
        match aux_i cj qj phi1, aux_i cj qj phi2 with
        | Some p, Some q -> 
          Some (Fun {head=_wedge; args=[p; q]})
        | _ -> None
      end
    | _ -> None
  in
  let rec aux_j right t =
    match right with
    (* boundary case: cj -> qj *)
    | Fun {head; args=[cj; qj]} when head = _imply -> 
      begin
        match aux_i cj qj t with
        | Some p -> Some (
          imply_type 
          (bitterm_to_type cj) 
          (Fun {head=_entailment; args=[p; qj]})
        )
        | None -> None
      end
    | Fun {head; args=[psi1; psi2]} when head = _wedge ->
      begin
        match aux_j psi1 t, aux_j psi2 t with
        | Some p1, Some p2 -> Some (
          Fun {
            head = _wedge;
            args = [p1; p2];
          }
        )
        | _ -> None
      end
    | _ -> None
    in

    (* matching the whole term t *)
    match t with
    | Fun {head=head_entail; args=[left; right]} when head_entail = _entailment ->
      aux_j right left
    | _ -> None


(** a helper function to remove Dirac notation label in forall. *)
let get_type_qreg_from_qvlist (wfctx: wf_ctx) (qvlist: terms list) : (terms * terms) option =
  let rec aux (qvlist: terms list) = 
    match qvlist with
    | [] -> None
    | [qv] ->
      begin
        match calc_type wfctx qv with
        | Type (Fun {head; args=[tt]}) when head = _qreg ->
          Some (
            tt,
            qv
          )
        | _ -> None
        end
    | qv :: rest ->
      begin
        match calc_type wfctx qv with
        | Type (Fun {head; args=[tt]}) when head = _qreg ->
          begin
            match aux rest with
            | Some (tt', qv') ->
              Some (
                Fun {head=_star; args=[tt; tt']},
                Fun {head=_pair; args=[qv; qv']}
              )
            | None -> None
          end
        | _ -> None
      end
  in
  aux qvlist

let forall_label_remove (wfctx: wf_ctx) (t : terms) : terms option =
  match t with
  | Fun {head; args=[
      Symbol x; 
      Fun{head=head_dtype; args=[
        Fun{head=head_list1; args=ls1;}; 
        Fun{head=head_list2; args=ls2;};
        ];}; 
      t'
    ]} when (head = _forall && head_dtype = _dtype && head_list1 = _list && head_list2 = _list) ->
    begin
      match get_type_qreg_from_qvlist wfctx ls1, 
            get_type_qreg_from_qvlist wfctx ls2 with
      | Some (tt1, qv1), Some (tt2, qv2) ->
        let new_t' = substitute t' x (Fun{head=_subscript; args=[Symbol x; Fun{head=_pair; args=[qv1; qv2]}]}) in
        Some (
          Fun {
            head = _forall;
            args = [
              Symbol x;
              Fun {head = _otype; args = [tt1; tt2];};
              new_t'
            ]
          }
        )
        | _ -> None
    end
  | _ -> None


(** the term rewriting rules in *)
let dirac_rules = [

  parse_rw_rule "A : OType[T2, T2] |- 0O[T1, T1] * A --> 0O[T1 * T2, T1 * T2]";
  parse_rw_rule "x^D^D --> x";

  parse_rw_rule "A_q /\\ B_q --> (A /\\ B)_q";

  parse_rw_rule "1O[T] /\\ A --> A";
  parse_rw_rule "A /\\ 1O[T] --> A";

  parse_rw_rule "1O[T] @ A --> A";
  parse_rw_rule "A @ 1O[T] --> A";

  parse_rw_rule "0O[T, T] /\\ B --> 0O[T, T]";
  parse_rw_rule "1O[T] /\\ B --> B";
  parse_rw_rule "B /\\ 1O[T] --> B";

  parse_rw_rule "1O[T]_(q, q) /\\ B --> B";
  parse_rw_rule "B /\\ 1O[T]_(q, q) --> B";

  (* parse_rw_rule "1O[BIT]_(q, q) /\\ 1O[BIT]_(q, q) --> 1O[BIT]_(q, q)"; *)

  parse_rw_rule "A_q @ B_q --> (A @ B)_q";
  parse_rw_rule "A_q /\\ B_q --> (A /\\ B)_q";
  parse_rw_rule "A_q \\/ B_q --> (A \\/ B)_q";
  parse_rw_rule "A_q -> B_q --> (A -> B)_q";
  parse_rw_rule "(A_(q1, q2))^D --> (A^D)_(q2, q1)";

  parse_rw_rule "A : OType[T, T] |- A -> A --> 1O[T]";

  parse_rw_rule "SUM[S, fun (i : T) => A_q] --> SUM[S, fun (i : T) => A]_q";


  parse_rw_rule "A : OType[T1, T2] |- A @ 0O[T2, T3] --> 0O[T1, T3]";
  parse_rw_rule "B : OType[T2, T3] |- 0O[T1, T2] @ B --> 0O[T1, T3]";
  parse_rw_rule "SUM[S, fun (i : T) => 0O[T1, T2]] --> 0O[T1, T2]";

  parse_rw_rule "U @@ (psi | A) --> (U @@ psi) | (U @@ A)";
  parse_rw_rule "U @@ (p /\\ q) --> (U @@ p) /\\ (U @@ q)";
  parse_rw_rule "U @@ (psi -> P) --> psi -> (U @@ P)";
  parse_rw_rule "U @@ A --> (U @ A) @ U^D";

  parse_rw_rule "INSPACE[rho_(q, q), P_(q, q)] --> INSPACE[rho, P]";
  parse_rw_rule "tr[P_(q, q)] --> tr[P]";
]



let dirac_simpl (typing : wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms =
  let dirac_transforms = 
    forall_label_remove wfctx ::
    (List.map (fun r -> apply_rewriting_rule_all r typing wfctx) dirac_rules)
  in
  (* apply_rewriting_rule  *)
  repeat_transforms dirac_transforms t
    

let simpl_entail_rules = [
  parse_rw_rule "A <= A --> true = true";
  parse_rw_rule "A <= 1O[BIT] --> true = true";
  parse_rw_rule "psi | A <= phi | B --> (phi <= psi) /\\ (A <= B)";
  parse_rw_rule "A_q <= B_q --> (A <= B)";
  parse_rw_rule "0O[T, T] <= A --> true = true";
  parse_rw_rule "0O[T, T]_(q, q) <= A --> true = true";
  parse_rw_rule "X : DType[ls1, ls2] |- A /\\ X <= X --> true = true";
  parse_rw_rule "X : DType[ls1, ls2] |- X /\\ A <= X --> true = true";
]

let simpl_entail (typing : wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms =
  let simpl_entail_transforms = List.map (fun r -> apply_rewriting_rule_all r typing wfctx) simpl_entail_rules
  in
  (* apply_rewriting_rule  *)
  repeat_transforms simpl_entail_transforms t
    

  
let _measure_wp_goal (x : string) (pre: terms) (post: terms) (m_opt: terms) (q: terms) : terms option =
  let get_subst bi x j =
    let s = [
      (x, j);
    ] in
    apply_subst s bi
  in
  let template = parse_terms "bisubst -> (Mj_(q, q) -> Pisubst)" in
  match m_opt, post with
  | Fun {head=head_pair; args=[m0; m1]}, Fun {head=head_vbar; args=[phi; a]} when head_pair = _pair && head_vbar = _vbar ->
    begin
      (* the auxiliary function to calculate proj part *)
      let rec aux_i (t: terms) : terms option =
        match t with
        (* boundary condition *)
        | Fun {head; args=[bi; pi]} when head = _imply ->
          let s0 = [
            ("bisubst", get_subst bi x (Symbol _false));
            ("Mj", m0);
            ("q", q);
            ("Pisubst", get_subst pi x (Symbol _false));
          ] in
          let term0 = apply_subst_unique_var s0 template in

          let s1 = [
            ("bisubst", get_subst bi x (Symbol _true));
            ("Mj", m1);
            ("q", q);
            ("Pisubst", get_subst pi x (Symbol _true));
          ] in 
          let term1 = apply_subst_unique_var s1 template in
          Some (Fun {head=_wedge; args=[term0; term1]})

        | Fun {head; args=[phi1; phi2]} when head = _wedge ->
          begin
            match aux_i phi1, aux_i phi2 with
            | Some p, Some q -> Some (Fun {head=_wedge; args=[p; q]})
            | _ -> None
          end
        | _ -> None
      in
      let aux_a (a : terms) (m_opt_q: terms) (j : terms) : terms =
        let asubst = apply_subst [(x, j)] a in
          Fun {
            head = _apply;
            args = [
              m_opt_q;
              Fun {
                head = _apply;
                args = [
                  asubst;
                  m_opt_q;
                ]
              }
            ]
          }
        in
      match aux_i phi with
      | Some rhs ->
        let pair_q = 
          Fun {head=_pair; args=[q; q]} in
        let wp_a_false = 
          aux_a a (Fun{head=_subscript; args=[m0; pair_q]}) (Symbol _false) in
        let wp_a_true =
          aux_a a (Fun{head=_subscript; args=[m1; pair_q]}) (Symbol _true) in
        (* return the goal *)
        let wp = Fun {head=_vbar; args=[rhs; Fun {head=_wedge; args=[wp_a_false; wp_a_true]};]} in
        Some (Fun {head = _entailment; args = [wp; pre]})
      | None -> None
    end
  | _ -> None


(** Calculation for measure-sample rule 
    /\_i (bi->Pi) ==> \/i bi
*)
let _measure_sample_or_bj (t: terms) : terms option =
  let rec aux t =
    match t with
    | Fun {head; args=[t1; _]} when head = _imply ->
        Some t1
    | Fun {head; args=[t1; t2]} when head = _wedge ->
      let p1 = aux t1 in
      let p2 = aux t2 in
      begin
        match p1, p2 with
        | Some t1', Some t2' -> Some (Fun {head=_vee; args=[t1'; t2']})
        | _ -> None
      end
    | _ -> None
  in
  match aux t with
  | Some t -> Some (Fun {head=_eq; args=[t; Symbol _true]})
  | None -> None

let _bijection_mapping (switch: bool) (t: terms) : terms =
  match t with
  | Symbol x when x = _true ->
    if switch then (Symbol _true) else (Symbol _false)
  | Symbol x when x = _false ->
    if switch then (Symbol _false) else (Symbol _true)
  | _ -> failwith ("_bijection_mapping: unexpected term.")
      

let _measure_sample_trace_goal (wfctx: wf_ctx) (preproj: terms) (m_opt: terms) (q: terms) (mu: terms) (switch: bool) : terms option =

  (* The function that outputs 
    bj' -> forall (rho in Pj'), tr(Mi_q rho_q) = mu(f(i))
  *)
  let aux (bj': terms) (pj': terms) (mi: terms) (q: terms) (fi: terms) : terms option = 
    match calc_type wfctx pj' with
    | Type (Fun {head; args=[ls1; ls2]}) when head = _dtype ->
      let name_pfbj' = fresh_name_for_ctx wfctx "pfbj'" in
      let name_rho = fresh_name_for_ctx wfctx "rho" in
      let name_pfspace = fresh_name_for_ctx wfctx "pfspace" in
      let template = parse_terms ("forall ( "^ name_pfbj' ^": bj'= true), forall ("^ name_rho ^": DType[ls1, ls2]), forall ("^ name_pfspace ^": INSPACE["^ name_rho ^", Pj']), tr[Mi_(q, q) @ "^ name_rho ^"] = mu @ fi") in
      let s = [
        ("bj'", bj');
        ("ls1", ls1);
        ("ls2", ls2);
        ("Pj'", pj');
        ("Mi", mi);
        ("q", q);
        ("mu", mu);
        ("fi", fi);
      ]
      in
      let goal = apply_subst_unique_var s template in
       Some goal

    | _ -> None
  in
  match m_opt with
  | Fun {head; args=[m0; m1]} when head = _pair ->
    begin
      let rec aux_pre preproj =
        match preproj with
        | Fun {head; args=[bj'; pj']} when head = _imply ->
          begin
            let termv0 = aux bj' pj' m0 q (_bijection_mapping switch (Symbol _false)) in
            let termv1 = aux bj' pj' m1 q (_bijection_mapping switch (Symbol _true)) in
            match termv0, termv1 with
            | Some termv0', Some termv1' ->
              (* return the goal *)
              Some (Fun {head=_wedge; args=[termv0'; termv1']})
            | _ -> None
          end
        | Fun {head; args=[t1; t2]} when head = _wedge ->
          begin
            match aux_pre t1, aux_pre t2 with
            | Some t1', Some t2' -> Some (Fun {head=_wedge; args=[t1'; t2']})
            | _ -> None
          end
        | _ -> None
      in 
      aux_pre preproj
    end
  | _ -> None

let _measure_sample_proj_goal (x : string) (y : string) (preproj: terms) (postproj: terms) (m_opt: terms) (q: terms) (switch: bool) : terms option =
  let get_subst bi x y j fj =
    let s = [
      (x, j);
      (y, fj);
    ] in
    apply_subst s bi
  in
  let template = parse_terms "bisubst -> (Mj_(q, q) -> Pisubst)" in
  match m_opt with
  | Fun {head; args=[m0; m1]} when head = _pair ->
    begin
      let rec aux_i (t: terms) : terms option =
        match t with
        (* boundary condition *)
        | Fun {head; args=[bi; pi]} when head = _imply ->
          let fj = _bijection_mapping switch (Symbol _false) in
          let s0 = [
            ("bisubst", get_subst bi x y (Symbol _false) fj);
            ("Mj", m0);
            ("q", q);
            ("Pisubst", get_subst pi x y (Symbol _false) fj);
          ] in
          let term0 = apply_subst_unique_var s0 template in

          let fj = _bijection_mapping switch (Symbol _true) in
          let s1 = [
            ("bisubst", get_subst bi x y (Symbol _true) fj);
            ("Mj", m1);
            ("q", q);
            ("Pisubst", get_subst pi x y (Symbol _true) fj);
          ] in 
          let term1 = apply_subst_unique_var s1 template in
          Some (Fun {head=_wedge; args=[term0; term1]})

        | Fun {head; args=[phi1; phi2]} when head = _wedge ->
          begin
            match aux_i phi1, aux_i phi2 with
            | Some p, Some q -> Some (Fun {head=_wedge; args=[p; q]})
            | _ -> None
          end
        | _ -> None
      in
      match aux_i postproj with
      | Some rhs ->
        Some (Fun {head = _entailment; args = [preproj; rhs]})
      | None -> None
    end
  | _ -> None

let _meas_meas_coupling_goal (wfctx: wf_ctx) (x: string) (y: string) (preproj: terms) (postproj: terms) (m_opt1: terms) (qs1: terms) (m_opt2: terms) (qs2: terms) (switch: bool) : terms option =

  let get_subst bi x y j k =
    let s = [
      (x, j);
      (y, k);
    ] in
    apply_subst s bi
  in

  let qcoupling_mid_template = parse_terms "bksubst -> ~(bj') |-> Pksubst" in
  let rec create_qcoupling_mid (bj': terms) (post: terms) (switch: bool) =
    match post with
    | Fun {head; args=[bk; pk]} when head = _imply ->
      let fj = _bijection_mapping switch (Symbol _false) in
      let bksubst = get_subst bk x y (Symbol _false) fj in
      let pksubst = get_subst pk x y (Symbol _false) fj in
      let s0 = [
        ("x", Symbol _false);
        ("y", fj);
        ("bj'", bj');
        ("bksubst", bksubst);
        ("Pksubst", pksubst);
      ] in
      let term0 = apply_subst_unique_var s0 qcoupling_mid_template in
      let fj = _bijection_mapping switch (Symbol _true) in
      let bksubst = get_subst bk x y (Symbol _true) fj in
      let pksubst = get_subst pk x y (Symbol _true) fj in
      let s1 = [
        ("x", Symbol _true);
        ("y", fj);
        ("bj'", bj');
        ("bksubst", bksubst);
        ("Pksubst", pksubst);
      ] in
      let term1 = apply_subst_unique_var s1 qcoupling_mid_template in
      Some (Fun {head=_wedge; args=[term0; term1]})

    | Fun {head; args=[t1; t2]} when head = _wedge ->
      begin
        match create_qcoupling_mid bj' t1 switch, create_qcoupling_mid bj' t2 switch with
        | Some t1', Some t2' -> Some (Fun {head=_wedge; args=[t1'; t2']})
        | _ -> None
      end
    | _ -> None
  in
  
  (* The function that outputs 
    bj' -> forall (rho in Pj'), 
      (Mi_q1 tr_q2(rho) (Mi^D)_q1, 
      /\_k (bk[i/x, fi/y] -> ~bj') |-> Pk[i/x, fi/y] #, 
      Nfi_q2 tr_q1(rho) Nfi^D_q2)
  *)
  let aux (bj': terms) (pj': terms) (mi: terms) (q1: terms) (nfi: terms) (q2: terms): terms option = 
    match calc_type wfctx pj' with
    | Type (Fun {head; args=[ls1; ls2]}) when head = _dtype ->
      begin
        match create_qcoupling_mid bj' postproj switch with
        | None -> None
        | Some couping_mid ->

          let name_pfbj' = fresh_name_for_ctx wfctx "pfbj'" in
          let name_rho = fresh_name_for_ctx wfctx "rho" in
          let name_pfspace = fresh_name_for_ctx wfctx "pfspace" in
          let template = parse_terms ("forall ( "^ name_pfbj' ^": bj'= true), forall ("^ name_rho ^": DType[ls1, ls2]), forall ("^ name_pfspace ^": INSPACE["^ name_rho ^", Pj']), (Mi_(q1, q1) @ tr_q2("^ name_rho ^") @ Mi^D_(q1, q1), couplingmid #, Nfi_(q2, q2) @ tr_q1("^ name_rho ^") @ Nfi^D_(q2, q2))") in

          let s = [
            ("bj'", bj');
            ("ls1", ls1);
            ("ls2", ls2);
            ("Pj'", pj');
            ("Mi", mi);
            ("q1", q1);
            ("Nfi", nfi);
            ("q2", q2);
            ("couplingmid", couping_mid);
          ]
          in
          let goal = apply_subst_unique_var s template in
          Some goal
      end

    | _ -> None
  in
  match m_opt1, m_opt2 with
  | Fun {head=head1; args=[m0; m1]}, Fun {head=head2; args=[n0; n1]} when head1 = _pair && head2 = _pair ->
    begin
      let rec aux_pre preproj =
        (* match the precondition *)
        match preproj with
        | Fun {head; args=[bj'; pj']} when head = _imply ->
          begin
            let nf0 = if switch then n0 else n1 in
            let nf1 = if switch then n1 else n0 in
            let termv0 = aux bj' pj' m0 qs1 nf0 qs2 in
            let termv1 = aux bj' pj' m1 qs1 nf1 qs2 in
            match termv0, termv1 with
            | Some termv0', Some termv1' ->
              (* return the goal *)
              Some (Fun {head=_wedge; args=[termv0'; termv1']})
            | _ -> None
          end

        | Fun {head; args=[t1; t2]} when head = _wedge ->
          begin
            match aux_pre t1, aux_pre t2 with
            | Some t1', Some t2' -> Some (Fun {head=_wedge; args=[t1'; t2']})
            | _ -> None
          end
        | _ -> None
      in 
      aux_pre preproj
    end
  | _ -> None

let cylinder_ext (wfctx : wf_ctx) (qs : terms) (s : terms) : terms option =
  match s, calc_type wfctx s with
  | Fun {head=head_subscript; args=[opt; Fun {args=[qs'1; qs'2]; _}]},
    Type (Fun {head=head_dtype; _}) when
      head_subscript = _subscript && qs'1 = qs'2 && head_dtype = _dtype
     ->
    begin match qs, calc_type wfctx qs with
    | Fun {head=head_pair; args=[qsl; qsr]},
      Type (Fun {head=head_qreg; args=[_]}) when
      head_pair = _pair &&
      head_qreg = _qreg ->
      begin
        (* extend on the right *)
        if qs'1 = qsl then
          match calc_type wfctx qsr with
          | Type (Fun {head=head_qreg; args=[tt']}) when head_qreg = _qreg ->
            Some (
              Fun {
                head = _subscript;
                args = [
                  (* tensor product *)
                  Fun {
                    head = _star;
                    args = [
                      opt;
                      Fun {
                        head = _oneo;
                        args = [tt'];
                      };
                    ]
                  }
                  ;
                  (* the extended quantum register *)
                  Fun {
                    head = _pair;
                    args = [qs; qs]
                  }
                ]
              }
            )
          | _ -> None

        (* extend on the left *)
        else if qs'1 = qsr then
          match calc_type wfctx qsl with
          | Type (Fun {head=head_qreg; args=[tt']}) when head_qreg = _qreg ->
            Some (
              Fun {
                head = _subscript;
                args = [
                  (* tensor product *)
                  Fun {
                    head = _star;
                    args = [
                      Fun {
                        head = _oneo;
                        args = [tt'];
                      };
                      opt;
                    ]
                  }
                  ;
                  (* the extended quantum register *)
                  Fun {
                    head = _pair;
                    args = [qs; qs]
                  }
                ]
              }
            )
          | _ -> None
        else
          None
      end
    | _ -> None
    end
    
  | _ -> None