(************************************************************************************)
(* This file holds the mechanism to generate LEAN4_AST from the CQOTL Prover syntax *)
(************************************************************************************)

open Ast
open Quantum_ast

(* Frame to hold relevant information for generating LEAN4 file *)
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
    in {    env     = List.filter is_relevant f.env;
            context = List.filter is_relevant f.context;
            goal    = f.goal    }

(* Common Quantum Terms *)
let ket0bra0    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "false")]}; Fun {head = "BRA"; args = [(Symbol "false")]}]}
let ket0bra1    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "true")]};  Fun {head = "BRA"; args = [(Symbol "true")]}]}
let ket1bra0    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "true")]};  Fun {head = "BRA"; args = [(Symbol "true")]}]}
let ket1bra1    = Fun {head = "APPLY"; args =  [Fun {head = "KET"; args = [(Symbol "false")]}; Fun {head = "BRA"; args = [(Symbol "false")]}]}

(* Common Types *)
(* OType[bit, bit] *)
let operatorType    = Fun {head = "OType";  args = [(Symbol "bit"); (Symbol "bit")]}
(* CVar[bit] *)
let cvarbitType     = Fun {head = "CVar";   args = [(Symbol "bit")]}
(* CVar[int] *)
let cvarintType     = Fun {head = "CVar";   args = [(Symbol "int")]}
(* CTerm[bit] *)
let ctermbitType    = Fun {head = "CTerm";  args = [(Symbol "bit")]}
(* CTerm[int] *)
let ctermintType    = Fun {head = "CTerm";  args = [(Symbol "int")]}
(* PDist[bit] *)
let pdistType       = Fun {head = "PDist";  args = [(Symbol "bit")]}
(* KType[int] *)
let ktypeIntType    = Fun {head = "KType";  args = [(Symbol "bit")]}

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
                Result (ELownerOrder (qt1, qt2))
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
