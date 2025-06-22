(************************************************************************************)
(* This file holds the mechanism to generate LEAN4_AST from the CQOTL Prover syntax *)
(************************************************************************************)

open Ast
open Quantum_ast
open Typing
open Pretty_printer

(* Frame to hold relevant information for generating LEAN4 file *)
type transform_quantum_result   = (quantumTerm, string) lean4Result [@@deriving show]
type transform_prop_result      = (proposition, string) lean4Result [@@deriving show]
type obligation_frame_result    = (obligation_proof_frame, string) lean4Result [@@deriving show]
type lean_obligation_result     = (lean_obligation, string) lean4Result [@@deriving show]

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
(* OType[bit, bit] *)
let operatorType    = Fun {head = "OType"; args = [(Symbol "bit"); (Symbol "bit")]}
(* CVar[bit] *)
let cvarbitType     = Fun {head = "CVar"; args = [(Symbol "bit")]}
(* CVar[int] *)
let cvarintType     = Fun {head = "CVar"; args = [(Symbol "int")]}
(* CTerm[bit] *)
let ctermbitType    = Fun {head = "CTerm"; args = [(Symbol "bit")]}
(* CTerm[int] *)
let ctermintType    = Fun {head = "CTerm"; args = [(Symbol "int")]}
(* PDist[bit] *)
let pdistType       = Fun {head = "PDist"; args = [(Symbol "bit")]}
(* KType[int] *)
let ktypeIntType    = Fun {head = "KType"; args = [(Symbol "bit")]}

(* Common type mappings *)
let type_mappings = [
    (operatorType,  TyOperatorType);
    (cvarbitType,   TyBool);
    (cvarintType,   TyInt);
    (ctermbitType,  TyBool);
    (ctermintType,  TyInt);
    (pdistType,     TyArrow (TyBool, TyKField));
    (ktypeIntType,  TyVectorType);
]

let rec transform_term_to_qtype (t : terms) : (qType, string) lean4Result = 
    match List.assoc_opt t type_mappings with
    | Some qt   -> Result qt
    | None      ->
        match t with
        | Fun {head; args=[Symbol x; var_ty; body]} when head = _forall     ->
            transform_term_to_qtype var_ty >>= 
                fun qt ->   transform_term_to_qtype body >>= 
                    fun body_qt -> Result (TyArrow (qt, body_qt))
        | Fun {head; args=[Symbol x; var_ty; body]} when head = _fun        ->
            LeanTranslationError "Type translation for FUN[...] not implemented to LEAN4."
        | Symbol sym when sym = _bit                                        ->
            Result TyBool
        | Symbol sym when sym = _int                                        ->
            Result TyInt
        | _                                                                 ->
            LeanTranslationError ("Unsopported type for LEAN4 translation: " ^ (show_terms t))

let rec ast_cqotl_to_expr (term : terms) : (expr, string) lean4Result =
    match term with
    | Ast.Symbol s ->
        begin
            match s with
            | "true"    -> Result (EBool true)
            | "false"   -> Result (EBool false)
            | _         -> Result (EVar s)
        end
    | Ast.Fun {head; args}  ->
        begin
            match head, args with
            | "EQ", [t1; t2]    ->  
                ast_cqotl_to_expr t1 >>= fun e1 ->
                ast_cqotl_to_expr t2 >>= fun e2 ->
                Result (E_Eq (e1, e2))
            | "EQEQ", [t1; t2]  ->
                ast_cqotl_to_expr t1 >>= fun e1 ->
                ast_cqotl_to_expr t2 >>= fun e2 ->
                Result (E_Eqeq (e1, e2))
            | "IMPLY", [t1; t2] ->
                ast_cqotl_to_expr t1 >>= fun e1 ->
                ast_cqotl_to_expr t2 >>= fun e2 ->
                Result (EImply (e1, e2))
            | "WEDGE", [t1; t2]  ->
                ast_cqotl_to_expr t1 >>= fun e1 ->
                ast_cqotl_to_expr t2 >>= fun e2 ->
                Result (EAnd (e1, e2))
            | "VEE", [t1; t2]    ->
                ast_cqotl_to_expr t1 >>= fun e1 ->
                ast_cqotl_to_expr t2 >>= fun e2 ->
                Result (EOr (e1, e2))
            | "APPLY", [f; t]                ->
                ast_cqotl_to_expr f >>= fun e1 ->
                ast_cqotl_to_expr t >>= fun e2 ->
                Result (EApply (e1, e2))
            | "FORALL", [Symbol x; t; body]  ->
                ast_cqotl_to_expr t >>= fun qt  ->
                ast_cqotl_to_expr body >>= fun body_e ->
                Result (EForall (x, qt, body_e))
            | "ENTAILMENT", [t1; t2]         ->
                ast_cqotl_to_expr t1 >>= fun qt1 ->
                ast_cqotl_to_expr t2 >>= fun qt2 ->
                Result (ESubspace (qt1, qt2))
            | "NOT", [t]                    ->
                ast_cqotl_to_expr t >>= fun qt ->
                Result (ENot qt)
            | "KET", [t]                    ->
                ast_cqotl_to_expr t >>= fun qt ->
                Result (EKet qt)
            | "BRA", [t]                    ->
                ast_cqotl_to_expr t >>= fun qt ->
                Result (EBra qt)
            | "ADJ", [t]                    ->
                ast_cqotl_to_expr t >>= fun qt ->
                Result (EAdjoint qt)
            | "INSPACE", [t1; t2]           ->
                ast_cqotl_to_expr t1 >>= fun qt1 ->
                ast_cqotl_to_expr t2 >>= fun qt2 ->
                Result (ESubspace (qt1, qt2))
            | "ZEROO", [t1; t2]             ->
                Result (EZeroOp)
            | "ONEO", _                     ->
                Result (EIdentOp)
            | "tr", [t]                     ->
                ast_cqotl_to_expr t >>= fun qt ->
                Result (ETrace qt)
            | _ -> 
                begin 
                    match transform_term_to_qtype term with
                    |   Result ty                   -> Result (EType ty)
                    |   LeanTranslationError err    ->
                            LeanTranslationError ("Unsupported function head: " ^ head)
                end
        end
    | Ast.Opaque ->
        LeanTranslationError "Opaque terms are not supported in LEAN4 translation."

(* This function is not implemented yet, as the focus is on quantum terms and propositions. *)
let rec transform_term_to_classical (wfctx : wf_ctx) (t : terms) : (classicalTerm, string) lean4Result =
    match t with
    | Symbol x ->
        begin
            match find_item wfctx x with
            | Some (Assumption {name; t})           -> Result (C_ClassicalVar name)
            | Some (Definition {name; t; e=_})      -> Result (C_ClassicalVar name)
            | None                                  -> LeanTranslationError ("Symbol " ^ x ^ " not found in context.")
        end
    (* We need to deal with the case when something is applied *)
    | Fun {head; args=[t1; t2]} when head = _apply      ->
        transform_term_to_classical wfctx t1 >>= fun c1 ->
        transform_term_to_classical wfctx t2 >>= fun c2 ->
        Result (C_Apply (c1, c2))
    
    | Fun {head; args}                                  ->
        LeanTranslationError ("Classical term translation not implemented for Fun term: " ^ (show_terms t))
    | Opaque                                            ->
        LeanTranslationError ("Classical term translation not implemented for Opaque term: " ^ (show_terms Opaque))


(* The reserved symbols for the LEAN4 translation *)
let rec transform_term_to_prop (wfctx : wf_ctx) (s : terms) : transform_prop_result =
    match s with
        | Symbol sym when sym = _type                               ->
            LeanTranslationError "_type is not a proposition to LEAN4."
        (* true *)
        | Symbol sym when sym = _true   -> 
            Result (Prop_True)
        (* false *)
        | Symbol sym when sym = _false  -> 
            Result (Prop_False)
        (* Forall *)
        | Fun {head; args=[Symbol x; t; t']} when head = _forall    ->
            begin
                match type_check wfctx t (Symbol _type) with
                | Type _ ->
                    begin
                        let new_wfctx = {wfctx with ctx = Assumption {name = x; t = t} :: wfctx.ctx} in
                        match transform_term_to_prop new_wfctx t' with
                        | Result prop ->
                            transform_term_to_qtype t >>=
                                fun q_type  ->  Result (Prop_Forall (x, q_type, prop))
                        | LeanTranslationError msg ->
                            LeanTranslationError msg
                    end
                | TypeError msg ->
                    LeanTranslationError msg
            end
        (* eqeq = equality for booleans *)
        | Fun {head; args=[t1; t2]} when head = _eqeq               ->
            begin
                match is_cterm wfctx t1, is_cterm wfctx t2 with
                | Type type_t1, Type type_t2 when type_t1 = type_t2 ->
                    begin
                        match type_t1 with
                        | Fun {head=head; args=[Symbol _]} when head = _cterm   ->
                            transform_term_to_classical wfctx t1 >>= fun c1     ->
                            transform_term_to_classical wfctx t2 >>= fun c2     ->
                            Result (Prop_EqualsC (c1, c2))
                        | _                                                     ->
                            LeanTranslationError "LEAN4 Translation Failed."
                    end
                | _ ->
                    LeanTranslationError "Not a valid equality proposition."
            end
        (* Eq between propositions *)
        (* This needs adding cases where both terms are not simply propositions *)
        (* In this case, we need to keep attempting conversion of *)
        (* term1 to prop *)
        (* if failed, then term1 to quantum term *)
        (* if failed, then it actually fails *)
        | Fun {head; args=[t1; t2]} when head = _eq         ->
            begin
                transform_term_to_prop wfctx t1 >>= fun prop1 ->
                transform_term_to_prop wfctx t2 >>= fun prop2 ->
                Result (Prop_EqualsP (prop1, prop2))
            end
        (* wedge -- conjunction *)
        | Fun {head; args=[t1; t2]} when head = _wedge          ->
            begin
                match calc_type wfctx t1, calc_type wfctx t2 with
                | Type type_t1, Type type_t2    ->
                    begin
                        match type_t1, type_t2 with
                        (* type conjunction *)
                        | _ when type_t1 = Symbol _type && type_t2 = Symbol _type ->
                            LeanTranslationError "Type conjunction not implemented to LEAN4."
                        (* boolean conjunction *)
                        | _ when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 ->
                            transform_term_to_classical wfctx t1 >>= fun c1 ->
                            transform_term_to_classical wfctx t2 >>= fun c2 ->
                            Result (Prop_AndC (c1, c2))
                        (* cq-projector conjunction *)
                        | _ when type_t1 = Symbol _cqproj && type_t2 = Symbol _cqproj ->
                            LeanTranslationError "Conjunction for CQ-Projector not implemented to LEAN4."
                        (* otype projector conjunction *)
                        | Fun {head=head1; _} , _ when head1 = _otype && type_t1 = type_t2 ->
                            LeanTranslationError "Otype projector conjunction not implemented to LEAN4."
                        (* dtype projector conjunction *)
                        | Fun {head=head1; args=[Fun{args=s1; _}; Fun{args=s2; _}]},
                          Fun {head=head2; args=[Fun{args=s1'; _}; Fun{args=s2'; _}]} when head1 = _dtype && head2 = _dtype && s1 = s2 && s1' = s2' ->
                            LeanTranslationError "Dtype projector conjunction not implemented to LEAN4."
                        | _ ->
                            LeanTranslationError "Not a valid conjunction proposition to send to LEAN4."

                    end
                | TypeError msg, _ ->
                    LeanTranslationError (Printf.sprintf "LEAN4 Translation failed %s is not well typed. %s" (term2str s) msg)
                | _, _             ->
                    LeanTranslationError (Printf.sprintf "LEAN4 Translation failed %s is not well typed." (term2str s))
            end
        (* guarded *)
        (* |  *)
        (* vee -- disjunction *)
        | Fun {head; args=[t1; t2]} when head = _vee                ->
            LeanTranslationError "_vee is correct proposition to LEAN4. To be implemented."
        (* not *)
        | Fun {head; args=[t]} when head = _not                     ->
            LeanTranslationError "_not is correct proposition to LEAN4. To be implemented."
        (* imply *)
        | Fun {head; args=[t1; t2]} when head = _imply              ->
            begin 
            transform_term_to_prop wfctx t1 >>= fun prop1 ->
            transform_term_to_prop wfctx t2 >>= fun prop2 ->
            (* Terms are already well-typed, and only boolean implication we assume *)
                Result (Prop_Implies (prop1, prop2))
            end
        (* Inspace *)
        | Fun {head; args=[t1; t2]} when head = _inspace            ->
            LeanTranslationError "_inspace means whether one is a subspace; not implemented to LEAN4"
        | _     ->
            LeanTranslationError (Printf.sprintf "Not a proposition. %s" (term2str s))

let rec transform_term_to_quantum (wfctx : wf_ctx) (s : terms) : transform_quantum_result = 
    match s with  
        | Symbol sym when sym = _type                               ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[Symbol x]}                               ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[Symbol x; t; t']} when head = _forall    ->
            LeanTranslationError "_forall is not a quantum term; it is a proposition."
        | Fun {head; args=[Symbol x; t; t']} when head = _fun       ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[Symbol x; t; t']} when head = _apply     ->
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _ctype                              ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _cvar                    ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _cterm                   ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _pdist                   ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _set                     ->
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _bit                                ->
            LeanTranslationError "Not implemented to LEAN4"  
        | Symbol sysm when sysm = _qvlist                           ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _optpair                 ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _qreg                    ->
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _stype                              ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _ktype                   ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t]} when head = _btype                   ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[t1; t2]} when head = _otype              ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[r1; r2]} when head = _dtype              ->
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _progstt                            -> 
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _prog                               -> 
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _cqproj                             -> 
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _assn                               -> 
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args} when head = _seq                         ->
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol sym when sym = _skip                               -> 
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[Symbol x; t]} when head = _assign        ->
            LeanTranslationError "Not implemented to LEAN4"
        | Fun {head; args=[Symbol x; mu]} when head = _passign     ->
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
        | Fun {head; args=[pre; s1; s2; post]} when head = _judgement   ->
            LeanTranslationError "Not implemented to LEAN4"
        | Symbol x                                                      ->
            LeanTranslationError "Not implemented to LEAN4"
        (* default *)
        | _                                                             -> 
            LeanTranslationError "Not a quantum term to LEAN4"

(* Transform an environment item to a quantum environment item *)
let transform_env_item (wfctx : wf_ctx) (item :envItem) : (quantumEnv, string) lean4Result =
    match item with
    | Assumption { name; t }        ->
        transform_term_to_qtype t     >>= fun q_type  -> 
            Result (QuantumAssumption { name = name; t = q_type })
    | Definition { name; t; e }     ->
        transform_term_to_qtype t     >>= fun q_type  -> 
        ast_cqotl_to_expr e           >>= fun e'      -> 
            Result (QuantumDefinition { name = name; t = q_type; e = e' })
    
(* Transform a list of environment items to a list of quantum environment items *)
let transform_context_to_variable (wfctx : wf_ctx) (item : envItem) : ((string * qType), string) lean4Result =
    match item with
    | Assumption {name; t}      ->
        transform_term_to_qtype t     >>= fun q_type  -> 
            Result (name, q_type)
    | _                         ->
        LeanTranslationError ("Unsupported context item (only assumptions supported) for LEAN4 translation: " ^ (show_envItem item))

(* Partial processor for a definition list *)
(* It takes a list of environment items    *)
(* and returns list if quantum Environment (Definitions + Assumption) and list of error messages *)
(* error messages are related to defintiions that failed to translate to LEAN4 *)
let create_definition_list (items : envItem list) : (quantumEnv list * string list) =
    let fold_fn (acc_defs, acc_errors, wfctx) item =
        match transform_env_item wfctx item with
        | Result def ->
            (def :: acc_defs, acc_errors, { wfctx with env = item :: wfctx.env })
        | LeanTranslationError msg ->
            (acc_defs, msg :: acc_errors, { wfctx with env = item :: wfctx.env })
    in
    let (defs, errors, _) = List.fold_left fold_fn ([], [], {env = []; ctx = []}) items in
    (List.rev defs, List.rev errors)

(* Similar to the above function, but specifically for converting context *)
(* to a list of variables *)
let create_variable_list (global_env : envItem list) (items : envItem list) : (string * qType) list * string list =
    let fold_fn (acc_vars, acc_errors, curr_wfctx) item =
        match transform_context_to_variable curr_wfctx item with
        | Result (var, q_type)  ->
            let next_wfctx = { curr_wfctx with env = item :: curr_wfctx.env } in
                ((var, q_type) :: acc_vars, acc_errors, next_wfctx)
        | LeanTranslationError msg ->
            (acc_vars, msg :: acc_errors, curr_wfctx)
    in
    let (vars, errors, _) =
        List.fold_left fold_fn ([], [], {env = global_env; ctx = []}) items
    in
    (List.rev vars, List.rev errors)

let obligation_frame_to_lean_obligation (frame : obligation_proof_frame) : lean_obligation_result =
    let (q_definitions, def_errors) = create_definition_list frame.env              in
    let (q_variables, var_errors)   = create_variable_list frame.env frame.context  in
    List.iter (fun err -> Printf.eprintf "Error in ENV conversion during LEAN4 generation: %s\n" err)       def_errors;
    List.iter (fun err -> Printf.eprintf "Error in Context conversion during LEAN4 generation: %s\n" err)   var_errors;
    (* Here we assume that the goal is a proposition, and we need to convert it *)
    ast_cqotl_to_expr frame.goal >>= fun goal_expr ->
    Result {
        definitions = q_definitions;
        variables   = q_variables;
        goal        = goal_expr; (* Place holder for now *)
    }
