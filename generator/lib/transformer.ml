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

let (>>=) (res : ('a, 'b) lean4Result) (f : 'a -> ('c, 'b) lean4Result) : ('c, 'b) lean4Result =
  match res with
  | Result v -> f v
  | LeanTranslationError msg -> LeanTranslationError msg

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

(* Utility function to extract the name from an envItem *)
let name_of_env_item (item : envItem) : string =
    match item with
    | Assumption {name; _} -> name
    | Definition {name; _} -> name

(* Refine Frame to only keep relevant symbols in the context and environment *)
let refine_lean_frame (f : obligation_proof_frame) : obligation_proof_frame =
    let symbols_in_goal = extract_symbols_from_goal f.goal in
    let is_relevant (item : envItem) : bool = 
        let item_name = name_of_env_item item in
        List.mem item_name symbols_in_goal 
    in {
        env     = List.filter is_relevant f.env;
        context = List.filter is_relevant f.context;
        goal    = f.goal
    }

(* Common Quantum Terms *)
let ket0bra0    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "false")]}; Fun {head = "BRA"; args = [(Symbol "false")]}]}
let ket0bra1    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "true")]};  Fun {head = "BRA"; args = [(Symbol "true")]}]}
let ket1bra0    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "true")]};  Fun {head = "BRA"; args = [(Symbol "true")]}]}
let ket1bra1    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "false")]}; Fun {head = "BRA"; args = [(Symbol "false")]}]}

let q_mappings  = [
    (ket0bra0, Q_Apply (Q_Ket0, Q_Bra0));
    (ket0bra1, Q_Apply (Q_Ket0, Q_Bra1));
    (ket1bra0, Q_Apply (Q_Ket1, Q_Bra0));
    (ket1bra1, Q_Apply (Q_Ket1, Q_Bra1));
    ]

(* Common Types *)
(* OTYPE[BIT, BIT] *)
let operatorType    = Fun {head = "OTYPE"; args = [(Symbol "BIT"); (Symbol "BIT")]}
(* CVAR[BIT] *)
let cvarbitType     = Fun {head = "CVAR"; args = [(Symbol "BIT")]}
(* CVAR[INT] *)
let cvarintType     = Fun {head = "CVAR"; args = [(Symbol "INT")]}
(* CTERM[BIT] *)
let ctermbitType    = Fun {head = "CTERM"; args = [(Symbol "BIT")]}
(* CTERM[INT] *)
let ctermintType    = Fun {head = "CTERM"; args = [(Symbol "INT")]}
(* PDIST[BIT] *)
let pdistType       = Fun {head = "PDIST"; args = [(Symbol "BIT")]}
(* KTYPE[INT] *)
let ktypeIntType    = Fun {head = "KTYPE"; args = [(Symbol "BIT")]}

(* Common type mappings *)
let type_mappings = [
    (operatorType,  Q_OperatorType);
    (cvarbitType,   Q_Bool);
    (cvarintType,   Q_Int);
    (ctermbitType,  Q_Bool);
    (ctermintType,  Q_Int);
    (pdistType,     Q_Arrow (Q_Bool, Q_KField));
    (ktypeIntType,  Q_VectorType);
]

let rec transform_term_to_qtype (wfctx : wf_ctx) (t : terms) : (qType, string) lean4Result = 
    match List.assoc_opt t type_mappings with
    | Some qt   -> Result qt
    | None      ->
        match t with
        | Fun {head; args=[Symbol x; var_ty; body]} when head = _forall     ->
            transform_term_to_qtype wfctx var_ty >>= 
                fun qt ->   transform_term_to_qtype {wfctx with ctx = Assumption {name = x; t = var_ty} :: wfctx.ctx} body >>= 
                    fun body_qt -> Result (Q_Arrow (qt, body_qt))
        | Fun {head; args=[Symbol x; var_ty; body]} when head = _fun        ->
            LeanTranslationError "Type translation for FUN[...] not implemented to LEAN4."
        | Symbol sym when sym = _bit                                        ->
            Result Q_Bool
        | Symbol sym when sym = _int                                        ->
            Result Q_Int
        | _ ->
            LeanTranslationError ("Unsopported type for LEAN4 translation: " ^ (show_terms t))
            

(* The reserved symbols for the LEAN4 translation *)

(* PDIST[CTYPE] *)
(* PDIST[BIT] *)
(* The reserved symbols for the LEAN4 translation *)
(* let transform_term_to_classical () *)
(* let transform_term_to_prop () *)
let rec transform_term_to_prop (wfctx : wf_ctx) (s : terms) : transform_prop_result =
    match s with
        | Symbol sym when sym = _type                               ->
            LeanTranslationError "_type is not a proposition to LEAN4."
        (*          Γ, a : T₁ ⊢ e : T₂ ~~~~> e'
            ---------------------------------------------------
            Γ ⊢ FORALL a : T₁, e : T₁ → T₂ ~~~> ∀ a : |T₁|,  e' *)
        | Fun {head; args=[Symbol x; t; t']} when head = _forall    ->
            begin
                match type_check wfctx t (Symbol _type) with
                | Type _ ->
                    begin
                        let new_wfctx = {wfctx with ctx = Assumption {name = x; t = t} :: wfctx.ctx} in
                        match transform_term_to_prop new_wfctx t' with
                        | Result prop ->
                            transform_term_to_qtype new_wfctx t >>=
                                fun q_type  ->  Result (Prop_Forall (x, q_type, prop))
                        | LeanTranslationError msg ->
                            LeanTranslationError msg
                    end
                | TypeError msg ->
                    LeanTranslationError msg
            end
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
    
let rec transform_term_to_quantum (wfctx : wf_ctx) (s : terms) : transform_quantum_result = 
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
        | Fun {head; args=[t]} when head = _ket                         ->
            begin
                match t with
                | Symbol sym when sym = _false  ->
                    Result (Q_Ket0)
                | Symbol sym when sym = _true   ->
                    Result (Q_Ket1)
                | _                             -> 
                    LeanTranslationError "Expected |false> ~~> |0> or |true> ~~> |1> only."
            end
        (* bra *)
        | Fun {head; args=[t]} when head = _bra                     ->
            LeanTranslationError "Not implemented to LEAN4"
        (* adj *)
        | Fun {head; args=[t]} when head = _adj                     ->
            transform_term_to_quantum wfctx t >>= fun qt -> Result (Q_Adjoint qt)
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
        