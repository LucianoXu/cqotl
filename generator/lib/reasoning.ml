
open Ast
open Ast_transform
open Utils 
open Parser_utils

(* open Typing *)

(** the term rewriting rules in *)
let simpl_rules = [
  parse_rw_rule "true -> false --> false";
  parse_rw_rule "true |-> A --> A";
  parse_rw_rule "A : OTYPE[T, T] |- false |-> A_q --> 0O[T, T]_q";
  parse_rw_rule "true -> true --> true";
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
  parse_rw_rule "A_q /\\ B_q --> (A /\\ B)_q";
  parse_rw_rule "0O[T, T] /\\ B --> 0O[T, T]";
  parse_rw_rule "A_q @ B_q --> (A @ B)_q";
  parse_rw_rule "SUM[S, fun (i : T) => A_q] --> SUM[S, fun (i : T) => A]_q";


  parse_rw_rule "A : OTYPE[T1, T2] |- A @ 0O[T2, T3] --> 0O[T1, T3]";
  parse_rw_rule "B : OTYPE[T2, T3] |- 0O[T1, T2] @ B --> 0O[T1, T3]";
  parse_rw_rule "SUM[S, fun (i : T) => 0O[T1, T2]] --> 0O[T1, T2]";
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
    
