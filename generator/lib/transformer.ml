(************************************************************************************)
(* This file holds the mechanism to generate LEAN4_AST from the CQOTL Prover syntax *)
(************************************************************************************)

open Ast
open Quantum_ast
open Typing

type transform_quantum_result =
  | QuantumResult               of quantumTerm
  | TranslationQuantumError     of string

type transform_prop_result =
  | PropositionResult       of proposition
  | TranslationPropError    of string

let transform_term_to_prop (wfctx : wf_ctx) (s : terms) : transform_prop_result =
  match s with
    | Symbol sym when sym = _type                               ->
        TranslationPropError "_type is not a proposition to LEAN4."
    | Fun {head; args=[Symbol x; t; t']} when head = _forall    ->
        TranslationPropError "_forall is correct proposition to LEAN4. To be implemented."
    | Fun {head; args=[Symbol x; t; t']} when head = _fun       ->
        TranslationPropError "Not implemented to LEAN4"
    | Fun {head; args=[Symbol x; t; t']} when head = _apply     ->
        TranslationPropError "Not implemented to LEAN4"
    (* eqeq = equality for booleans *)
    | Fun {head; args=[t1; t2]} when head = _eqeq               ->
        TranslationPropError "_eqeq is correct proposition to LEAN4. To be implemented."
    (* wedge -- conjunction *)
    | Fun {head; args=[t1; t2]} when head = _wedge              ->
        TranslationPropError "_wedge is correct proposition to LEAN4. To be implemented."
    (* vee -- disjunction *)
    | Fun {head; args=[t1; t2]} when head = _vee                ->
        TranslationPropError "_vee is correct proposition to LEAN4. To be implemented."
    (* not *)
    | Fun {head; args=[t]} when head = _not                     ->
        TranslationPropError "_not is correct proposition to LEAN4. To be implemented."
    (* imply *)
    | Fun {head; args=[t1; t2]} when head = _imply              ->
        TranslationPropError "_imply is correct proposition to LEAN4. To be implemented."
    (* Eq *)
    | Fun {head; args=[t1; t2]} when head = _eq                 ->
        TranslationPropError "_eq is an equality between general terms (hence, prop); not implemented to LEAN4"
    (* Inspace *)
    | Fun {head; args=[t1; t2]} when head = _inspace            ->
        TranslationPropError "_inspace means whether one is a subspace; not implemented to LEAN4"
    | _     ->
        TranslationPropError "Not a proposition."
    
let transform_term_to_quantum (wfctx : wf_ctx) (s : terms) : transform_quantum_result = 
  match s with  
  | Symbol sym when sym = _type                             ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x]}                             ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; t; t']} when head = _forall  ->
      TranslationQuantumError "_forall is not a quantum term; it is a proposition."
  | Fun {head; args=[Symbol x; t; t']} when head = _fun     ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; t; t']} when head = _apply   ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _ctype                            ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _cvar                  ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _cterm                 ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _pdist                 ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _set                   ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _bit                              ->
      TranslationQuantumError "Not implemented to LEAN4"  
  | Symbol sysm when sysm = _qvlist                         ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _optpair               ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _qreg                  ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _stype                            ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _ktype                 ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t]} when head = _btype                 ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t1; t2]} when head = _otype            ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[r1; r2]} when head = _dtype            ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _progstt                          -> 
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _prog                             -> 
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _cqproj                           -> 
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _assn                             -> 
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args} when head = _seq                       ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol sym when sym = _skip                             -> 
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; t]} when head = _assign      ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; miu]} when head = _passign   ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[qs]} when head = _init_qubit             ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[u; qs]} when head = _unitary             ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[Symbol x; m_opt; qs]} when head = _meas  ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[b; s1; s2]} when head = _if              ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[b; s']} when head = _while               ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t1; t2]} when head = _star               ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args=[t1; t2]} when head = _pair               ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Fun {head; args} when head = _list                        ->
      TranslationQuantumError "Not implemented to LEAN4"
  (**************************************)
  (* Dirac Notation *)
  (* ket *)
  | Fun {head; args=[t]} when head = _ket                     ->
        begin
            match t with
            | Symbol sym when sym = _false  ->
                Obligation (Q_Ket0)
            | Symbol sym when sym = _true   ->
                Obligation (Q_Ket1)
            | _ -> TranslationQuantumError "Expected |false> ~~> |0> or |true> ~~> |1> only."
        end
  (* bra *)
  | Fun {head; args=[t]} when head = _bra                     ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* adj *)
  | Fun {head; args=[t]} when head = _adj                     ->  
      TranslationQuantumError "Not implemented to LEAN4"
  (* zeroo *)
  | Fun {head; args=[t1; t2]} when head = _zeroo              ->
        begin
            match calc_type wfctx t1, calc_type wfctx t2 with
            | Type (Symbol sym1), Type (Symbol sym2) when sym1 = _ctype && sym2 = _ctype ->
                Obligation (Q_ZeroOperator)
            | _ ->  TranslationQuantumError "Not implemented to LEAN4"
        end
  (* oneo *)
  | Fun {head; args=[t]} when head = _oneo                    ->
        begin
            match calc_type wfctx t with
            | Type (Symbol sym1) when sym1 = _ctype ->
                Obligation (Q_IdOperator)
            | _     ->  TranslationQuantumError "Not implemented to LEAN4"
        end
  (* plus *)
  | Fun {head; args=[t1; t2]} when head = _plus               ->
        TranslationQuantumError "Not implemented to LEAN4"
  (* sum *)
  | Fun {head; args=[s'; f]} when head = _sum                 ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* trace *)
  | Fun {head; args=[t]} when head = _tr                      ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* uset *)
  | Fun {head; args=[t]} when head = _uset                    ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* subscript, opt pair*)
  | Fun {head; args=[t1; Fun {head=pair_head; args=[s1; s2]}]} when head = _subscript && pair_head = _pair  ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* true *)
  | Symbol sym when sym = _true                               -> 
      TranslationQuantumError "Not implemented to LEAN4"
  (* false *)
  | Symbol sym when sym = _false                              -> 
      TranslationQuantumError "Not implemented to LEAN4"
  (* guarded quantum operator *)
  | Fun {head; args=[t1; t2]} when head = _guarded            ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* atat: unitary transformation on projectors *)
  | Fun {head; args=[t1; t2]} when head = _atat               ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* vbar (cq-assertion) *)
  | Fun {head; args=[t1; t2]} when head = _vbar               ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* Eq *)
  | Fun {head; args=[t1; t2]} when head = _eq                 ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* inspace *)
  | Fun {head; args=[t1; t2]} when head = _inspace            ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* Entailment *)
  | Fun {head; args=[t1; t2]} when head = _entailment         -> 
      TranslationQuantumError "Not implemented to LEAN4"
  (* Judgement *)
  | Fun {head; args=[pre; s1; s2; post]} when head = _judgement ->
      TranslationQuantumError "Not implemented to LEAN4"
  | Symbol x                                                  ->
      TranslationQuantumError "Not implemented to LEAN4"
  (* default *)
  | _                                                         -> 
    TranslationQuantumError "Not a quantum term to LEAN4"
 