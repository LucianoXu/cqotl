(************************************************************************************)
(* This file holds the mechanism to generate LEAN4_AST from the CQOTL Prover syntax *)
(************************************************************************************)

open Ast
open Quantum_ast
open Typing

(* Frame to hold relevant information for generating LEAN4 file *)
type transform_quantum_result   = (quantumTerm, string) lean4Result
type transform_prop_result      = (proposition, string) lean4Result
type obligation_frame_result    = (obligation_proof_frame, string) lean4Result [@@deriving show]

(* We assume this function doesn't has non-empty goals *)
let proof_frame_to_lean_frame (f : proof_frame) : obligation_frame_result =
    match f.goals with
    | []                -> LeanTranslationError "No proof obligation to be translated to LEAN."
    | (ctx, goal_term) :: rest_goals ->
        (* only the first goal goes to LEAN *)
        let obligation_frame = {
            env     = f.env;
            context = ctx;
            goal    = goal_term;
        }
        in  Result (obligation_frame)

(* This function will return the list of symbols/free variables in the AST *)
let extract_symbols_from_goal (s : terms) : string list =
    let rec aux acc term =
        match term with
        | Symbol sym            ->
            if List.mem sym reserved_symbols || List.mem sym acc then
                acc
            else
                sym :: acc
        | Fun {head = _; args}  ->
            List.fold_left aux acc args
        | Opaque                -> acc
    in List.rev (aux [] s)



(* let transform_term_to_prop () *)
let transform_term_to_prop (wfctx : wf_ctx) (s : terms) : transform_prop_result =
  match s with
    | Symbol sym when sym = _type                               ->
        LeanTranslationError "_type is not a proposition to LEAN4."
    | Fun {head; args=[Symbol x; t; t']} when head = _forall    ->
        LeanTranslationError "_forall is correct proposition to LEAN4. To be implemented."
    | Fun {head; args=[Symbol x; t; t']} when head = _fun       ->
        LeanTranslationError "Not implemented to LEAN4"
    | Fun {head; args=[Symbol x; t; t']} when head = _apply     ->
        LeanTranslationError "Not implemented to LEAN4"
    (* eqeq = equality for booleans *)
    | Fun {head; args=[t1; t2]} when head = _eqeq               ->
        LeanTranslationError "_eqeq is correct proposition to LEAN4. To be implemented."
    (* wedge -- conjunction *)
    | Fun {head; args=[t1; t2]} when head = _wedge              ->
        LeanTranslationError "_wedge is correct proposition to LEAN4. To be implemented."
    (* vee -- disjunction *)
    | Fun {head; args=[t1; t2]} when head = _vee                ->
        LeanTranslationError "_vee is correct proposition to LEAN4. To be implemented."
    (* not *)
    | Fun {head; args=[t]} when head = _not                     ->
        LeanTranslationError "_not is correct proposition to LEAN4. To be implemented."
    (* imply *)
    | Fun {head; args=[t1; t2]} when head = _imply              ->
        LeanTranslationError "_imply is correct proposition to LEAN4. To be implemented."
    (* Eq *)
    | Fun {head; args=[t1; t2]} when head = _eq                 ->
        LeanTranslationError "_eq is an equality between general terms (hence, prop); not implemented to LEAN4"
    (* Inspace *)
    | Fun {head; args=[t1; t2]} when head = _inspace            ->
        LeanTranslationError "_inspace means whether one is a subspace; not implemented to LEAN4"
    | _     ->
        LeanTranslationError "Not a proposition."
    
let transform_term_to_quantum (wfctx : wf_ctx) (s : terms) : transform_quantum_result = 
  match s with  
  | Symbol sym when sym = _type                             ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x]}                             ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; t; t']} when head = _forall  ->
      LeanTranslationError "_forall is not a quantum term; it is a proposition."
  | Fun {head; args=[Symbol x; t; t']} when head = _fun     ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; t; t']} when head = _apply   ->
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _ctype                            ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _cvar                  ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _cterm                 ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _pdist                 ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _set                   ->
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _bit                              ->
      LeanTranslationError "Not implemented to LEAN4"  
  | Symbol sysm when sysm = _qvlist                         ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _optpair               ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _qreg                  ->
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _stype                            ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _ktype                 ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _btype                 ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t1; t2]} when head = _otype            ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[r1; r2]} when head = _dtype            ->
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _progstt                          -> 
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _prog                             -> 
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _cqproj                           -> 
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _assn                             -> 
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args} when head = _seq                       ->
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol sym when sym = _skip                             -> 
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; t]} when head = _assign      ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; miu]} when head = _passign   ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[qs]} when head = _init_qubit             ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[u; qs]} when head = _unitary             ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; m_opt; qs]} when head = _meas  ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[b; s1; s2]} when head = _if              ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[b; s']} when head = _while               ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t1; t2]} when head = _star               ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args=[t1; t2]} when head = _pair               ->
      LeanTranslationError "Not implemented to LEAN4"
  | Fun {head; args} when head = _list                        ->
      LeanTranslationError "Not implemented to LEAN4"
  (**************************************)
  (* Dirac Notation *)
  (* ket *)
  | Fun {head; args=[t]} when head = _ket                     ->
        begin
            match t with
            | Symbol sym when sym = _false  ->
                Result (Q_Ket0)
            | Symbol sym when sym = _true   ->
                Result (Q_Ket1)
            | _ -> LeanTranslationError "Expected |false> ~~> |0> or |true> ~~> |1> only."
        end
  (* bra *)
  | Fun {head; args=[t]} when head = _bra                     ->
      LeanTranslationError "Not implemented to LEAN4"
  (* adj *)
  | Fun {head; args=[t]} when head = _adj                     ->  
      LeanTranslationError "Not implemented to LEAN4"
  (* zeroo *)
  | Fun {head; args=[t1; t2]} when head = _zeroo              ->
        begin
            match calc_type wfctx t1, calc_type wfctx t2 with
            | Type (Symbol sym1), Type (Symbol sym2) when sym1 = _ctype && sym2 = _ctype ->
                Result (Q_ZeroOperator)
            | _ ->  LeanTranslationError "Not implemented to LEAN4"
        end
  (* oneo *)
  | Fun {head; args=[t]} when head = _oneo                    ->
        begin
            match calc_type wfctx t with
            | Type (Symbol sym1) when sym1 = _ctype ->
                Result (Q_IdOperator)
            | _     ->  LeanTranslationError "Not implemented to LEAN4"
        end
  (* plus *)
  | Fun {head; args=[t1; t2]} when head = _plus               ->
        LeanTranslationError "Not implemented to LEAN4"
  (* sum *)
  | Fun {head; args=[s'; f]} when head = _sum                 ->
      LeanTranslationError "Not implemented to LEAN4"
  (* trace *)
  | Fun {head; args=[t]} when head = _tr                      ->
      LeanTranslationError "Not implemented to LEAN4"
  (* uset *)
  | Fun {head; args=[t]} when head = _uset                    ->
      LeanTranslationError "Not implemented to LEAN4"
  (* subscript, opt pair*)
  | Fun {head; args=[t1; Fun {head=pair_head; args=[s1; s2]}]} when head = _subscript && pair_head = _pair  ->
      LeanTranslationError "Not implemented to LEAN4"
  (* true *)
  | Symbol sym when sym = _true                               -> 
      LeanTranslationError "Not implemented to LEAN4"
  (* false *)
  | Symbol sym when sym = _false                              -> 
      LeanTranslationError "Not implemented to LEAN4"
  (* guarded quantum operator *)
  | Fun {head; args=[t1; t2]} when head = _guarded            ->
      LeanTranslationError "Not implemented to LEAN4"
  (* atat: unitary transformation on projectors *)
  | Fun {head; args=[t1; t2]} when head = _atat               ->
      LeanTranslationError "Not implemented to LEAN4"
  (* vbar (cq-assertion) *)
  | Fun {head; args=[t1; t2]} when head = _vbar               ->
      LeanTranslationError "Not implemented to LEAN4"
  (* Eq *)
  | Fun {head; args=[t1; t2]} when head = _eq                 ->
      LeanTranslationError "Not implemented to LEAN4"
  (* inspace *)
  | Fun {head; args=[t1; t2]} when head = _inspace            ->
      LeanTranslationError "Not implemented to LEAN4"
  (* Entailment *)
  | Fun {head; args=[t1; t2]} when head = _entailment         -> 
      LeanTranslationError "Not implemented to LEAN4"
  (* Judgement *)
  | Fun {head; args=[pre; s1; s2; post]} when head = _judgement ->
      LeanTranslationError "Not implemented to LEAN4"
  | Symbol x                                                  ->
      LeanTranslationError "Not implemented to LEAN4"
  (* default *)
  | _                                                         -> 
    LeanTranslationError "Not a quantum term to LEAN4"
 