open Ast
open Pretty_printer

(***************************************************************)
(* term transformation *)

(** transformation type *)
type transform = terms -> terms option [@@deriving show]

(** Repeatedly apply the list of transformation once on a term and return the result. *)
let rec apply_transforms (transforms: transform list) (t: terms) : terms option =
  match transforms with
  | [] -> None
  | f :: fs ->
      match f t with
      | Some t' -> Some t'
      | None -> apply_transforms fs t

(** Repeat apply_transforms. *)
let rec repeat_transforms (transforms: transform list) (t: terms) : terms =
  match apply_transforms transforms t with
  | Some t' -> repeat_transforms transforms t'
  | None -> t

(***************************************************************)
(* Term Rewriting System *)

(** substitution type *)
type subst = (string * terms) list [@@deriving show]

let subst_remove (s: subst) (x: string) : subst =
  List.filter (fun (y, _) -> y <> x) s

let subst_exist (s: subst) (x: string) : bool =
  List.exists (fun (y, _) -> y = x) s

(** apply a substitution to a term *)
let rec apply_subst (s: subst) (t: terms) : terms =
  match t with
  | Symbol x -> 
      begin
        match List.assoc_opt x s with
        | Some v -> v
        | None -> t
      end
  | Fun {head; args} ->
      let args' = List.map (apply_subst s) args in
      Fun {head; args = args'}
  | Opaque -> Opaque


(** matching algorithm *)

(***************************************************************)
(* Matching (pattern-matching, **not** full unification)       *)
(***************************************************************)

(** is the symbol a pattern-variable? *)
let is_var (x : string) : bool =
  not (List.mem x reserved_symbols)

(** does the substitution already bind x? *)
let indom (x : string) (s : subst) : bool =
  List.exists (fun (y, _) -> x = y) s

(** lookup – pre-condition: x ∈ dom s *)
let app (s : subst) (x : string) : terms =
  match List.assoc_opt x s with
  | Some t -> t
  | None   -> failwith "internal error: variable not in substitution"

(** The heart of the algorithm – straight from Fig. 4.6             *)
let rec matchs ?(is_var = is_var) (pairs : (terms * terms) list) (s : subst)  : subst option =
  match pairs with
  | [] -> Some s                                              (* all done *)
  | (Symbol x, t) :: ls when is_var x ->                      (* V x ↦ t  *)
      if indom x s then
        if app s x = t then matchs ls s                       (* same binding – ok *)
        else None                                             (* incompatible *)
      else
        matchs ls ((x, t) :: s)                               (* extend θ *)
  | (_, Symbol x) :: _ when is_var x ->                       (* obj side var – forbid *)
      None
  | (Fun {head = f; args = ts}, Fun {head = g; args = us}) :: ls ->
      if f = g && List.length ts = List.length us then
        let zipped = List.combine ts us in
        matchs (zipped @ ls) s                                (* descend *)
      else
        None
  | (Symbol c1, Symbol c2) :: ls ->                            (* constants *)
      if c1 = c2 then matchs ls s else None
  | (Opaque, Opaque) :: ls ->                                  (* identical opaques *)
      matchs ls s
  | _ -> None                                                  (* every other mismatch *)


let rwrule2str (r: rewriting_rule) : string =
  match r with
  | {lhs; rhs; typings = []} ->
      Printf.sprintf "%s --> %s" (term2str lhs) (term2str rhs)
  
  | {lhs; rhs; typings} ->
    let typings_str =
        (List.map (fun (x, t) -> Printf.sprintf "%s : %s" (term2str x) (term2str t)) typings)
    |> String.concat ", " in
    Printf.sprintf "%s |- %s --> %s" typings_str (term2str lhs) (term2str rhs)

let rec term_fresh_name (boundvars: string list) (t: terms) : terms =
    match t with
    | Symbol x when is_var x && not (List.mem x boundvars) -> Symbol ("$" ^ x)  (* prepend '$' to variable names *)
    | Symbol x -> Symbol x  (* keep other symbols unchanged *)
    | Fun {head; args = [Symbol v; t; s]} when head = _forall || head = _fun ->
        let fresh_t = term_fresh_name boundvars t in
        let fresh_s = term_fresh_name (v::boundvars) s in
        Fun {head; args = [Symbol v; fresh_t; fresh_s]}  (* keep the variable name, but prepend '$' *)
    | Fun {head; args} ->
        let args' = List.map (term_fresh_name boundvars) args in
        Fun {head; args = args'}
    | Opaque -> Opaque

let rec term_fresh_bound_name (boundvars: string list) (t: terms) : terms =
  match t with
  | Symbol x when List.mem x boundvars -> Symbol ("$" ^ x)  (* prepend '$' to variable names *)
  | Symbol x -> Symbol x  (* keep other symbols unchanged *)
  | Fun {head; args = [Symbol v; t; s]} when head = _forall || head = _fun ->
      let new_t = term_fresh_bound_name boundvars t in
      let new_s = term_fresh_bound_name (v::boundvars) s in
      Fun {head; args = [Symbol ("$" ^ v); new_t; new_s]}
  | Fun {head; args} ->
      let args' = List.map (term_fresh_bound_name boundvars) args in
      Fun {head; args = args'}
  | Opaque -> Opaque



(** Apply the substitution. Modify the variable name so that they will never conflict with values in the substitution. *)
let apply_subst_unique_var (s: subst) (t: terms) : terms =
  let new_s = List.map (fun (x, v) -> ("$" ^ x, v)) s in
  let new_t = term_fresh_name [] t in
  apply_subst new_s new_t


(** Add a '$' symbol before all variables of the rule *)
let rwrule_fresh_name (rule: rewriting_rule) : rewriting_rule =
  {
    lhs = term_fresh_name [] rule.lhs;
    rhs = term_fresh_name [] rule.rhs;
    typings = List.map (fun (t1, t2) -> (term_fresh_name [] t1, term_fresh_name [] t2)) rule.typings;
  }
  

let apply_rewriting_rule 
  (rule: rewriting_rule) (typing: wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t: terms) : terms option =
  (* match the left-hand side of the rule against the term t *)
  match matchs [(rule.lhs, t)] [] with
    | Some subst ->
        (* check all the typing conditions *)
        let rec check_typings typings subst : subst option =
          match typings with
          | [] -> Some subst  (* all typing conditions satisfied *)
          | (t1, t2) :: rest ->
              let t1_substituted = apply_subst subst t1 in
              let t2_substituted = apply_subst subst t2 in
                match typing wfctx t1_substituted with 
                | None -> None (* if the typing fails, return None *)
                | Some type_t1 ->
                  (* if the typing succeeds, try matching the typing condition. *)
                  match matchs [(t2_substituted, type_t1)] subst with
                  | Some new_subst ->
                      (* if the typing condition is satisfied, continue with the rest *)
                      check_typings rest new_subst
                  | None -> None (* if the typing condition is not satisfied, return None *)
        in  begin
              match check_typings rule.typings subst with
              | None        -> None  (* if typing conditions are not satisfied, return None *)
              | Some subst  ->
                (* if matched, apply the substitution to the right-hand side *)
                let rhs_substituted = apply_subst subst rule.rhs in
                  Some rhs_substituted
            end
    | None -> None  (* if not matched, return None *)


(**  Depth-first, left-to-right search.
     – If the rule matches the whole term, rewrite immediately.
     – Otherwise descend into the first sub-term that can be rewritten
       and rebuild the parent on the way back. *)
let rec apply_rewriting_rule_all
    (rule : rewriting_rule) (typing: wf_ctx -> terms -> terms option) (wfctx : wf_ctx)(t : terms) : terms option =
  match apply_rewriting_rule rule typing wfctx t with
  | Some t' -> Some t'                         (* hit at the root *)
  | None ->
      begin match t with

      (* special handling for forall and fun (wfctx adjustment) *)
      | Fun { head; args = [Symbol v; t; s]} when head = _fun || head = _forall ->
        begin
          match apply_rewriting_rule_all rule typing wfctx t with
          | Some t_rewritten -> 
              Some (Fun { head; args = [Symbol v; t_rewritten; s] })
          | None ->
              let new_wfctx = {
                env = wfctx.env;
                ctx = Assumption {name = v; t = t} :: wfctx.ctx;
              } in
              begin match apply_rewriting_rule_all rule typing new_wfctx s with
              | Some s_rewritten -> Some (Fun { head; args = [Symbol v; t; s_rewritten] })
              | None -> None
              end
        end
        
      | Fun { head; args } ->
          (* walk through the argument list until one rewrites *)
          let rec search done_so_far wfctx todo =
            match todo with
            | [] -> None                       (* no sub-term matches *)
            | a :: rest ->
                begin match apply_rewriting_rule_all rule typing wfctx a with
                | Some a' ->                   (* rewrite inside a *)
                    let args' =
                      List.rev done_so_far @ (a' :: rest) in
                    Some (Fun { head; args = args' })
                | None ->
                    search (a :: done_so_far) wfctx rest
                end
          in
          search [] wfctx args
      | _ -> None                              (* Symbol / Opaque – leaves *)
      end

(***************************************************************)
(* Convenience helpers for whole systems of rules              *)
(***************************************************************)

(** Try every rule once, returning the first successful rewrite. *)
let rec rewrite_once (rules : rewriting_rule list) (typing: wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms option =
  match rules with
  | [] -> None
  | r :: rs ->
      begin match apply_rewriting_rule_all r typing wfctx t with
      | Some t' -> Some t'
      | None     -> rewrite_once rs typing wfctx t
      end

(** Normal-form computation: keep rewriting until nothing changes. *)
let rec rewrite (rules : rewriting_rule list) (typing: wf_ctx -> terms -> terms option) (wfctx : wf_ctx) (t : terms) : terms =
  match rewrite_once rules typing wfctx t with
  | Some t' -> rewrite rules typing wfctx t'
  | None    -> t