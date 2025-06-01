
open Ast
open Ast_transform
open Utils 
open Parser_utils
open Typing

(** the term rewriting rules in *)
let simpl_rules = [
  parse_rw_rule "true -> false --> false";
  parse_rw_rule "true |-> A --> A";
  parse_rw_rule "A : OTYPE[T, T] |- false |-> A_q --> 0O[T, T]_q";
  parse_rw_rule "true -> true --> true";
  parse_rw_rule "A == A --> true";
  parse_rw_rule "~ true --> false";
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


(** the term rewriting rules in *)
let dirac_rules = [
  parse_rw_rule "x^D^D --> x";

  parse_rw_rule "A_q /\\ B_q --> (A /\\ B)_q";
  parse_rw_rule "0O[T, T] /\\ B --> 0O[T, T]";
  parse_rw_rule "A_q @ B_q --> (A @ B)_q";
  parse_rw_rule "(A_(q1, q2))^D --> (A^D)_(q2, q1)";

  parse_rw_rule "SUM[S, fun (i : T) => A_q] --> SUM[S, fun (i : T) => A]_q";


  parse_rw_rule "A : OTYPE[T1, T2] |- A @ 0O[T2, T3] --> 0O[T1, T3]";
  parse_rw_rule "B : OTYPE[T2, T3] |- 0O[T1, T2] @ B --> 0O[T1, T3]";
  parse_rw_rule "SUM[S, fun (i : T) => 0O[T1, T2]] --> 0O[T1, T2]";

  parse_rw_rule "U @@ (psi | A) --> (U @@ psi) | (U @@ A)";
  parse_rw_rule "U @@ (p /\\ q) --> (U @@ p) /\\ (U @@ q)";
  parse_rw_rule "U @@ (psi -> P) --> psi -> (U @@ P)";
  parse_rw_rule "U @@ A --> (U @ A) @ U^D";
]



let dirac_simpl (typing : wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms =
  let dirac_transforms = List.map (fun r -> apply_rewriting_rule_all r typing wfctx) dirac_rules
  in
  (* apply_rewriting_rule  *)
  repeat_transforms dirac_transforms t
    

let simpl_entail_rules = [
  parse_rw_rule "psi | A <= phi | B --> (phi <= psi) /\\ (A <= B)";
  parse_rw_rule "A_q <= B_q --> (A <= B)";
  parse_rw_rule "0O[T1, T2] <= A --> true = true";
]

let simpl_entail (typing : wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms =
  let simpl_entail_transforms = List.map (fun r -> apply_rewriting_rule_all r typing wfctx) simpl_entail_rules
  in
  (* apply_rewriting_rule  *)
  repeat_transforms simpl_entail_transforms t
    


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


let _measure_sample_trace_goal (wfctx: wf_ctx) (preproj: terms) (m_opt: terms) (q: terms) (miu: terms) : terms option =

  (* The function that outputs 
    bj' -> forall (rho in Pj'), tr(Mi_q rho_q) = miu(f(i))
  *)
  let aux (bj': terms) (pj': terms) (mi: terms) (q: terms) (fi: terms) : terms option = 
    match calc_type wfctx pj' with
    | Type (Fun {head; args=[ls1; ls2]}) when head = _dtype ->
      let name_pfbj' = fresh_name_for_ctx wfctx "pfbj'" in
      let name_rho = fresh_name_for_ctx wfctx "rho" in
      let name_pfspace = fresh_name_for_ctx wfctx "pfspace" in
      let template = parse_terms ("forall ( "^ name_pfbj' ^": bj'= true), forall ("^ name_rho ^": DTYPE[ls1, ls2]), forall ("^ name_pfspace ^": INSPACE["^ name_rho ^", Pj']), tr[Mi_(q, q) @ "^ name_rho ^"] = miu @ fi") in
      let s = [
        ("bj'", bj');
        ("ls1", ls1);
        ("ls2", ls2);
        ("Pj'", pj');
        ("Mi", mi);
        ("q", q);
        ("miu", miu);
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
            let termv0 = aux bj' pj' m0 q (Symbol _false) in
            let termv1 = aux bj' pj' m1 q (Symbol _true) in
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

let _measure_sample_proj_goal (x : string) (y : string) (preproj: terms) (postproj: terms) (m_opt: terms) (q: terms) : terms option =
  let template = parse_terms "bisubst -> (Mj_(q, q) -> Pisubst)" in
  match m_opt with
  | Fun {head; args=[m0; m1]} when head = _pair ->
    begin
      let rec aux_i (t: terms) : terms option =
        match t with
        (* boundary condition *)
        | Fun {head; args=[bi; pi]} when head = _imply ->
          let get_subst bi x y j =
            let s = [
              (x, j);
              (y, j);
            ] in
            apply_subst s bi
          in
          let s0 = [
            ("bisubst", get_subst bi x y (Symbol _false));
            ("Mj", m0);
            ("q", q);
            ("Pisubst", get_subst pi x y (Symbol _false));
          ] in
          let term0 = apply_subst_unique_var s0 template in
          let s1 = [
            ("bisubst", get_subst bi x y (Symbol _true));
            ("Mj", m1);
            ("q", q);
            ("Pisubst", get_subst pi x y (Symbol _true));
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