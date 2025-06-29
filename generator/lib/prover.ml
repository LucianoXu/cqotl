open Ast
open Ast_transform
open Pretty_printer
open Typing
open Reasoning
open Utils
open Parser_utils
open Transformer
open Quantum_ast
open Mapper
open Printf

let config_file = "cqotl_path.config"

(* Define the relative path from the base CQOTL directory to the Lean Examples directory *)
let relative_lean_examples_dir = "lean-veri/LeanVeri/GENERATED_OBLIGATIONS"

(* Function to read the base path from the config file *)
let read_cqotl_base_path config_path =
  try
    let ic = open_in config_path in
    let raw_path = input_line ic in
    close_in ic;
    (* Key point: if the path in the config file is relative,
       interpret it as an absolute path relative to the current
       working directory (Sys.getcwd ()). *)
    let base_path =
      if Filename.is_relative raw_path then
        Filename.concat (Sys.getcwd ()) raw_path
      else
        raw_path
    in
    Some base_path
  with
  | Sys_error msg ->
      Printf.eprintf "Error: Could not open or read config file '%s' - %s\n" config_path msg;
      None
  | End_of_file ->
      Printf.eprintf "Error: Config file '%s' is empty. Please provide the base CQOTL path.\n" config_path;
      None

(* Function to write content to a file *)
let write_content_to_file filepath content =
  try
    let oc = open_out filepath in
    fprintf oc "%s" content; (* Use %s not %s\n because lean_ast_to_lean_file already adds a newline *)
    close_out oc;
    printf "  -> Successfully wrote Lean code to '%s'\n" filepath;
    true
  with
  | Sys_error msg ->
      eprintf "Error: Could not write to file '%s' - %s\n" filepath msg;
      false

(** Create a well-formed context from an environment with empty context. *)
let env2wfctx env = {env=env; ctx=[]}

let get_pf_wfctx (pf : proof_frame) : wf_ctx =
  match pf.goals with
  | []          -> env2wfctx pf.env
  | (ctx, _)::_ -> 
      {env = pf.env; ctx = ctx}
  
(** Get the environment from the frame. *)
let get_frame_wfctx (f: frame) : wf_ctx =
  match f with
  | NormalFrame {env} -> env2wfctx env
  | ProofFrame  pf -> get_pf_wfctx pf
  
let add_envItem (f: normal_frame) (item: envItem) : frame =
  NormalFrame {env = item::f.env}

(*************************************************************)
(* Proof Frame Operations *)

let open_proof (f: normal_frame) (name: string) (prop: terms) : frame =
  ProofFrame {
    env         = f.env;
    proof_name  = name;
    proof_prop  = prop;
    goals       = [([], prop)];
    lean_goals  = [];
  }

let close_proof (f: proof_frame) : frame =
  NormalFrame {
    env = (Definition {name = f.proof_name; t=f.proof_prop; e=Opaque}) :: f.env
  }

let discharge_first_goal (f: proof_frame) : proof_frame =
  match f.goals with
  | [] -> f
  | _ :: tl ->
      let new_frame = {
        env         = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = tl;
        lean_goals  = f.lean_goals;
      } in
      new_frame

(** Add a new goal to the proof_frame with empty local context. *)
let add_goal (f: proof_frame) (goal: terms) : proof_frame =
  let new_frame = {
        env = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = ([], goal)::f.goals;
        lean_goals  = f.lean_goals
      } in
  new_frame

(*************************************************************)

(** Initialize the prover with an empty stack. *)
let init_prover () : prover = 
  {stack = []}

let get_frame (p: prover) : frame =
  match p.stack with
  | [] -> NormalFrame {env = []}
  | f :: _ -> f

(* formatting *)
let envItem2str (item: envItem ): string = 
  match item with
  | Assumption {name; t} -> 
      Printf.sprintf "%s : %s" name (term2str t)
  | Definition {name; t; e} -> 
      Printf.sprintf "%s := %s : %s" name (term2str e) (term2str t)

let env2str (env: envItem list): string =
  let env_str = List.map envItem2str env in
    String.concat "\n" env_str
    |> Printf.sprintf "Environment: [\n%s\n]"

let wfctx2str (wfctx: wf_ctx): string =
  let env_str = List.map envItem2str wfctx.env in
  let ctx_str = List.map envItem2str wfctx.ctx in
    Printf.sprintf "Environment: [\n%s\n]\nContext: [\n%s\n]"
      (String.concat "\n" env_str)
      (String.concat "\n" ctx_str)

let goals2str (f: proof_frame): string =
  match f.goals with
  | [] -> "All Goals Clear.\n"
  | _ ->
    let total = List.length f.goals in
    let goals_str = List.mapi 
      (fun i (_, p) -> Printf.sprintf "(%d/%d) %s" (i + 1) total (term2str p))
      f.goals
    in
    String.concat "\n\n" goals_str
    |> Printf.sprintf "[Goals]\n\n%s\n"

let leangoals2str (f: proof_frame): string =
  match f.lean_goals with
  | [] -> "NO LEAN4 Goals.\n"
  | _ ->
    let total = List.length f.lean_goals in
    let goals_str = List.mapi 
      (fun i (_, p) -> Printf.sprintf "(%d/%d) %s" (i + 1) total (term2str p))
      f.lean_goals
    in
    String.concat "\n\n" goals_str

(* The whole information about the frame *)
let frame2str (f: frame): string =
  match f with
  | NormalFrame {env} -> 
      let env_str = env2str env in
        Printf.sprintf "%s" env_str
  | ProofFrame f ->
    let env_str         = wfctx2str (get_pf_wfctx f) 
    in  let proof_mode_str  = 
          Printf.sprintf "\n---------------------------------------------------------------\n[Proof Mode]\n\n%s"  (goals2str f)   
    in  let lean_goals_str  = 
          Printf.sprintf "\n---------------------------------------------------------------\n[LEAN4 Goals]\n\n%s" (leangoals2str f)
    in  Printf.sprintf "%s%s%s" env_str proof_mode_str lean_goals_str

let prover2str (p: prover): string =
  let frame = get_frame p in
    (frame2str frame)
    |> Printf.sprintf "%s" 

(***********************************************************************)
(* The main function that evaluates the command and updates the state. *)
let rec eval (p: prover) (cmd: command) : eval_result =
  let res =
    match cmd with
    | Def {x; t; e} -> 
        eval_def p x t e
    | DefWithoutType {x; e} ->
        eval_def_without_type p x e
    | Var {x; t} -> 
        eval_var p x t
    | Check e ->
        eval_check p e
    | Show x ->
        eval_show p x
    | ShowAll -> 
        eval_showall p
    | Undo -> 
        eval_undo p
    | Pause ->
        Pause
    | Prove { x = x; p = prop} ->
        eval_prove p x prop
    | Tactic t ->
        eval_tactic p t
    | QED ->
        eval_QED p
    (* | _ -> raise (Failure "Command not implemented yet") *)
  in match res with
    | ProverError msg -> 
        ProverError (msg ^ "\n\nFor the command:\n" ^ (command2str cmd))
    | _ -> res

and eval_def (p: prover) (name: string) (t: terms) (e: terms) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ -> 
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      let wfctx : wf_ctx = normal_f.env |> env2wfctx  in
      match find_item wfctx name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None -> 
        (* Type check here *)
        match type_check wfctx e t with
        | Type _ -> 
            (* Add the new definition to the frame. *)
            p.stack <- (add_envItem normal_f (Definition {name; t; e})) :: p.stack;
            Success
        | TypeError msg -> 
            ProverError (Printf.sprintf "The term %s is not well typed as %s. %s" (term2str e) (term2str t) msg)

and eval_def_without_type (p: prover) (name: string) (e: terms) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ -> 
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      let wfctx : wf_ctx = normal_f.env |> env2wfctx in
      match find_item wfctx name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None ->
        (* Type check here *)
        match calc_type wfctx e with
        | Type t ->   
            (* Add the new definition to the frame. *)
            p.stack <- (add_envItem normal_f (Definition {name; t; e})):: p.stack;
            Success
        | TypeError msg ->
            ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)


and eval_var (p: prover) (name: string) (t: terms) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ ->
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      let wfctx : wf_ctx = normal_f.env |> env2wfctx in
      match find_item wfctx name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None ->
          (* Type check needed here *)
          (* Add the new variable to the frame. *)
          match is_type wfctx t with
          | Some _ -> 
            p.stack <- (add_envItem normal_f (Assumption {name; t})) :: p.stack;
            Success
          | _ -> ProverError (Printf.sprintf "The type %s is not typed as Type, Prop or CType." (term2str t))

and eval_check (p: prover) (e: terms) : eval_result =
  let wfctx = get_frame_wfctx (get_frame p) in
  let calc_type_res = calc_type wfctx e in
  match calc_type_res with
  | Type t -> Printf.printf "Check %s : %s.\n" (term2str e) (term2str t); Success
  | TypeError msg ->
    ProverError (Printf.sprintf "Typing error: %s" msg)

and eval_show (p: prover) (x: string) : eval_result =
  let frame = get_frame p in
    let wfctx : wf_ctx = get_frame_wfctx frame in
    let item = find_item wfctx x in
      match item with
      | Some (Assumption {name; t}) -> 
          Printf.printf "Show %s : %s.\n" name (term2str t);
          Success
      | Some (Definition {name; t; e}) -> 
          Printf.printf "Show %s := %s : %s.\n" name (term2str e) (term2str t);
          Success
      | None -> 
          ProverError (Printf.sprintf "Name %s is not defined." x)

and eval_showall (p: prover) : eval_result =
  let frame = get_frame p in
  Printf.printf "ShowAll:\n%s\n" (env2str (get_frame_wfctx frame).env);
  Success
    

and eval_prove (p: prover) (x : string) (prop: terms) : eval_result =
  let frame = get_frame p in
  (* check whether it is in proof mode *)
  match frame with
  | ProofFrame _ -> 
    ProverError "The prover is in proof mode."
  | NormalFrame normal_f ->
    (* check whether the name is already defined *)
    let wfctx : wf_ctx = normal_f.env |> env2wfctx in
    match find_item wfctx x with
    | Some _ -> 
      ProverError (Printf.sprintf "Name %s is already declared." x)
    | None ->
      (* check whether can be typed as Type. *)
      match is_type wfctx prop with
      | Some _ -> 
          p.stack <- (open_proof normal_f x prop) :: p.stack;
          Success
      | None -> 
          ProverError (Printf.sprintf "%s cannot be typed as Type, therfore witness cannot be proved." (term2str prop))


and eval_undo (p: prover) : eval_result =
  match p.stack with
  | [] -> ProverError "No frame to undo."
  | _ :: rest -> p.stack <- rest; Success


and eval_QED (p: prover) : eval_result =
  let frame = get_frame p in
  (* check whether it is in proof mode and all goals are clear *)
  match frame with
  | NormalFrame _ -> 
      ProverError "The prover is not in proof mode."
  | ProofFrame proof_f ->
    if List.length proof_f.goals > 0 then
      ProverError "Goals Remains."
    else
      (* Add the proof to the frame. *)
      let new_frame = close_proof proof_f in
      p.stack <- new_frame :: p.stack;
      Success

and eval_tactic (p: prover) (tac : tactic) : eval_result =
  let frame = get_frame p in
    (* Check whether it is in proof mode *)
    match frame with
    | NormalFrame _ -> 
        ProverError "The prover is not in proof mode."
    | ProofFrame proof_f ->
        (* check tactic *)
        let tac_res = 
        begin
          match tac with
          | Sorry         -> eval_tac_sorry proof_f
          | Expand v      -> eval_tac_expand proof_f v
          | Refl          -> eval_tac_refl proof_f
          | Destruct v    -> eval_tac_destruct proof_f v
          | Case e        -> eval_tac_case proof_f e
          | Intro v       -> eval_tac_intro proof_f v
          | Revert v      -> eval_tac_revert proof_f v
          | Apply e       -> eval_tac_apply proof_f e
          | Choose i      -> eval_tac_choose proof_f i
          | Split         -> eval_tac_split proof_f
          | ByLean        -> eval_tac_by_lean proof_f
          | Simpl         -> eval_tac_simpl proof_f
          | Rewrite_L2R t -> eval_tac_rewrite proof_f t true
          | Rewrite_R2L t -> eval_tac_rewrite proof_f t false
          | RWRULE r      -> eval_tac_RWRULE proof_f r

          | R_PRE pre     -> eval_tac_R_PRE proof_f pre
          | R_POST post   -> eval_tac_R_POST proof_f post
          | R_SKIP        -> eval_tac_R_SKIP proof_f
          | R_SEQ (n1, n2, t) -> eval_tac_R_SEQ proof_f n1 n2 t
          | R_ASSIGN      -> eval_tac_R_ASSIGN proof_f
          | R_INITQ       -> eval_tac_R_INITQ proof_f
          | R_UNITARY     -> eval_tac_R_UNITARY proof_f
          | R_MEAS        -> eval_tac_R_MEAS proof_f
          | R_IF qs         -> eval_tac_R_IF proof_f qs
          | R_WHILE (qs, phi) -> eval_tac_R_WHILE proof_f qs phi
          | R_WHILE_WHILE (qs, phi) -> eval_tac_R_WHILE_WHILE proof_f qs phi
          | R_MEAS_MEAS switch -> eval_tac_R_MEAS_MEAS proof_f switch
          | R_MEAS_SAMPLE switch -> eval_tac_R_MEAS_SAMPLE proof_f switch

          | JUDGE_SWAP    -> eval_tac_JUDGE_SWAP proof_f
          | CQ_ENTAIL     -> eval_tac_CQ_ENTAIL proof_f
          | DIRAC         -> eval_tac_DIRAC proof_f
          | SIMPL_ENTAIL  -> eval_tac_SIMPL_ENTAIL proof_f
          | ENTAIL_TRANS e -> eval_tac_ENTAIL_TRANS proof_f e
          | CYLINDER_EXT qs -> eval_tac_CYLINDER_EXT proof_f qs
        end
        in 
        match tac_res with
        | Success new_frame -> 
            (* Update the frame *)
            p.stack <- new_frame :: p.stack;
            Success
        | TacticError msg ->
            ProverError (Printf.sprintf "[Tactic error]\n%s" msg)

and eval_tac_sorry (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | _ :: _ ->
      (* Add the proof to the frame. *)
      let new_frame = discharge_first_goal f in
      Success (ProofFrame new_frame)

and eval_tac_expand (f: proof_frame) (v: string) : tactic_result = 
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx,hd)::tl ->
    let wfctx = (get_pf_wfctx f) in
    match find_symbol wfctx v with
    | Some (Definition {e; _}) ->
      let new_goal = substitute hd v e in
      let new_frame = {
        env = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = (ctx, new_goal) :: tl;
        lean_goals  = f.lean_goals;
      } in
      Success (ProofFrame new_frame)
    | _ -> TacticError (Printf.sprintf "%s is not defined in the context." v)


and eval_tac_refl (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (_, hd) :: _ ->
      (* Check the application condition *)
      match hd with
      | Fun {head; args=[t1; t2]} when head = _eq && t1 = t2 ->
      (* Add the proof to the frame. *)
        let new_frame = discharge_first_goal f in
        Success (ProofFrame new_frame)
      | _ -> 
        TacticError (Printf.sprintf "The tactic is not applicable to the current goal: %s" (term2str hd))

and eval_tac_destruct (f: proof_frame) (v: string) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (_, _) :: tl ->
      (* Check whether the given premise v discharges the goal *)
      match calc_type (get_pf_wfctx f) (Symbol v) with
      | Type type_v ->
        begin
          match type_v with
          | Fun {head; args=[t1; t2]} when head = _eq ->
            if t1 = Symbol _true && t2 = Symbol _false ||
               t1 = Symbol _false && t2 = Symbol _true then
                (* The premise is a boolean value, we can destruct it *)
                let new_frame = {
                  env = f.env;
                  proof_name = f.proof_name;
                  proof_prop = f.proof_prop;
                  goals = tl;
                  lean_goals = f.lean_goals;
                } in
                Success (ProofFrame new_frame)
            else
              TacticError (Printf.sprintf "The term %s is not a boolean value." v)
          | _ -> 
            TacticError (Printf.sprintf "The term %s is not a valid equality witness." v)
        end
      | TypeError msg ->
          TacticError (Printf.sprintf "The term %s is not well typed: %s" v msg)
        
and eval_tac_case (f: proof_frame) (e: terms) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    (* check wehterh e is typed as CTerm[BIT] *)
    let wfctx = get_pf_wfctx f in
    match type_check wfctx e (Fun {head=_cterm; args=[Symbol _bit]}) with
    | TypeError msg ->
      TacticError (Printf.sprintf "The term %s is not well typed as CTerm[BIT]: %s" (term2str e) msg)
    | Type _ ->
      let name0 = fresh_name_for_ctx wfctx "CASE0" in
      let name1 = fresh_name_for_ctx wfctx "CASE1" in
      let new_ctx_goal_0 = 
        (Assumption {name=name0; t=Fun{head=_eq; args=[e; Symbol _true]}} :: ctx, hd) in
      let new_ctx_goal_1 =
        (Assumption {name=name1; t=Fun{head=_eq; args=[e; Symbol _false]}} :: ctx, hd) in
      let new_frame = {
        env = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = new_ctx_goal_0 :: new_ctx_goal_1 :: tl;
        lean_goals  = f.lean_goals
      } in
      Success (ProofFrame new_frame)

and eval_tac_intro (f: proof_frame) (v: string) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | hd :: tl ->
      (* Check the application condition *)
      match hd with
      | (ctx, Fun {head; args=[Symbol x; t; t']}) when head = _forall ->
        let name = fresh_name_for_ctx (get_pf_wfctx f) v in
        let new_frame = {
          env = f.env;
          proof_name  = f.proof_name;
          proof_prop  = f.proof_prop;
          goals       = (Assumption {name; t}::ctx, substitute t' x (Symbol name)) :: tl;
          lean_goals  = f.lean_goals
        } in
        Success (ProofFrame new_frame)
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")
  
and eval_tac_revert (f: proof_frame) (v: string) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    (* Check whether the given premise v is in the context *)
    let rec aux (reverted: envItem list) (unrelated: envItem list) (remaining: envItem list) : (envItem list * envItem list) option =
      match remaining with
      | [] -> None
      | item :: rest ->
        match item with
        | Assumption {name; _} when name = v ->
          Some (item :: reverted, unrelated @ rest)
        (* if the assumption depends on the symbol to revert, then is should also be reverted *)
        | Assumption {t;_ } when List.mem v (get_symbols t) ->
          aux (item :: reverted) unrelated rest
        | Assumption _ ->
          aux reverted (item :: unrelated) rest
        | Definition {t; e; _} when List.mem v (get_symbols t) || List.mem v (get_symbols e) -> 
          None
        | Definition _ ->
          aux reverted (item :: unrelated) rest
    in
    match aux [] [] ctx with
    | Some (reverted, remaining) ->
      let rec add_forall (t: terms) (reverted: envItem list) : terms =
        match reverted with
        | [] -> t
        | Assumption {name; t = tt} :: ls ->
          let new_t = add_forall t ls in
          Fun {head = _forall; args = [Symbol name; tt; new_t]}

        (* will never revert definitions *)
        | _ -> 
          failwith "Unexpected item in context during revert."
      in
      let new_goal = add_forall hd reverted in
      let new_frame = {
        env         = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = (remaining, new_goal) :: tl;
        lean_goals  = f.lean_goals
      } in
      Success (ProofFrame new_frame)
    | None ->
      TacticError (Printf.sprintf "The variable %s is not in the context." v)

(* because we don't allow existential variables to be unified, we will limit the premises to A -> (B -> ...) only. *)
and eval_tac_apply (f: proof_frame) (e: terms) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    (* Check whether the term e is a valid witness for the current goal *)
    let wfctx = get_pf_wfctx f in
    let rec get_premise (vars: string list) (pattern: terms) : (terms * subst) option =
      (* first check whether the goal can be matched *)
      let is_var v = List.mem v vars in
      let res = matchs ~is_var:is_var 
        [(pattern, hd)]
        []
      in
      match res with
      | Some s ->
        Some (Fun{head=_eq; args=[Symbol _true; Symbol _true]}, s)
      | None ->
        match pattern with
        (* if the subterm is forall, look into it*)
        | Fun {head; args=[Symbol v; t; t']} when head = _forall ->
          begin
            match get_premise (v::vars) t' with
            | Some (pre', s) ->
              (* check whether the symbol v is free in pre' *)
              (* if v appears in pre' then we cannot support apply the lemma because existential instantiation is not supported *)
              if List.mem v (get_symbols pre') then
                None
              else 
                let new_s = List.filter (fun (y, _) -> y <> v) s in
                (* else, if v appears in the substitution, it means the variable is already instantiated. we just forward the premise. *)
                if subst_exist s v then
                (* remove the item of v *)
                Some (pre', new_s)
              else
                (* else, v goes into the premise. *)
                let new_pre = Fun {head=_wedge; args=[
                  apply_subst s t;
                  pre';
                ]} in
                Some (new_pre, new_s)
            | None -> None
          end
        | _ -> None
    in
    match calc_type wfctx e with
    | TypeError msg -> 
      TacticError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)
    | Type t ->
      match get_premise [] (term_fresh_bound_name [] t) with
      | Some (pre, _) ->
        let new_frame = {
          env         = f.env;
          proof_name  = f.proof_name;
          proof_prop  = f.proof_prop;
          goals       = (ctx, pre) :: tl;
          lean_goals  = f.lean_goals;
        } in
        Success (ProofFrame new_frame)
      | None ->
        TacticError (Printf.sprintf "The term %s is not a valid witness for the current goal: %s" (term2str e) (term2str hd))
    


and eval_tac_choose (f: proof_frame) (i: int) : tactic_result =
  if i < 1 || i > List.length f.goals then
    TacticError (Printf.sprintf "The index %d is out of range." i)
  else
    Success (ProofFrame {
      env         = f.env;
      proof_name  = f.proof_name;
      proof_prop  = f.proof_prop;
      goals       = move_to_front f.goals i;
      lean_goals  = f.lean_goals
    })

and eval_tac_split (f: proof_frame) : tactic_result =
    match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    let wfctx = get_pf_wfctx f in
    match hd with
    | Fun {head; args=[t1; t2]} when head=_wedge ->
      begin
        match 
          is_type wfctx t1, 
          is_type wfctx t2 with
        | Some _, Some _ ->
          let new_frame = {
            env         = f.env;
            proof_name  = f.proof_name;
            proof_prop  = f.proof_prop;
            goals       = (ctx, t1) :: (ctx, t2) :: tl;
            lean_goals  = f.lean_goals
          }
          in 
          Success (ProofFrame new_frame)
        | None, _ -> TacticError (Printf.sprintf "splic tactic cannot apply here. The terms %s is not typed as Type." (term2str t1))
        | _, None -> TacticError (Printf.sprintf "splic tactic cannot apply here. The terms %s is not typed as Type." (term2str t2))
      end
    | _ -> TacticError "split tactic cannot apply here. The current goal is not a conjunction."

and eval_tac_by_lean (f: proof_frame) : tactic_result =
  match f.goals with
  | []                              -> TacticError "Nothing to prove. No proof obligation to translate to Lean."
  | (ctx, goal_term) :: rest_goals  ->
      Printf.printf "-------- ByLean Tactic Invokved --------\n\n";
      let initial_obligation_frame  = proof_frame_to_lean_frame f   in
      match initial_obligation_frame with
      | LeanTranslationError err ->
          Printf.printf "Error creating initial obligation frame: %s\n" err;
          TacticError ("Failed to prepare goal for Lean: " ^ err)
      | Result lean_frame ->
          let refined_lean_frame      = refine_lean_frame lean_frame in
          let lean_obligation_result  = obligation_frame_to_lean_obligation refined_lean_frame in
          begin
            match lean_obligation_result with
            | LeanTranslationError msg  ->
                Printf.printf "CRITICAL: Failed to create Quantum_ast.lean_obligation: %s\n" msg;
                TacticError ("Failed to create intermediate Lean obligation: " ^ msg)
            | Result lean_obl ->
                Printf.printf "Successfully transformed to lean_obligation:\n%s\n" (show_lean_obligation lean_obl);
                let obligation_name = Printf.sprintf "obligation_%d" (List.length f.lean_goals + 1) in
                let lean_file_ast_result = transform_obligation_to_lean_file obligation_name lean_obl in
                match lean_file_ast_result with
                | LeanTranslationError msg ->
                    Printf.printf "CRITICAL: Failed to transform to Lean_ast.lean_file: %s\n" msg;
                    TacticError ("Failed to transform to Lean_ast.lean_file: " ^ msg)
                | Result lean_file_ast ->
                    Printf.printf "\n--- Generated Lean 4 AST ---\n%s\n-----------------------------\n\n" (Lean_ast.show_lean_file lean_file_ast);
                    let lean_code_string = Lean_printer.lean_ast_to_lean_file lean_file_ast in
                    let filename = Printf.sprintf "%s.lean" obligation_name in
                    
                    Printf.printf "\n--- Generated Lean 4 Code ---\n%s\n-----------------------------\n\n" lean_code_string;

                    (* --- CORRECTED FILE WRITING LOGIC --- *)
                    (* The 'match' statement is now the final expression within the 'let' scope *)
                    match read_cqotl_base_path config_file with
                    | None ->
                        TacticError ("Could not read base path from '" ^ config_file ^ "'. Cannot write Lean file.")
                    | Some base_path ->
                        let dir_components = String.split_on_char '/' relative_lean_examples_dir in
                        let full_examples_dir = List.fold_left Filename.concat base_path dir_components in
                        let full_lean_path = Filename.concat full_examples_dir filename in

                        if write_content_to_file full_lean_path lean_code_string then
                          let new_frame_state = {
                            env = f.env;
                            proof_name = f.proof_name;
                            proof_prop = f.proof_prop;
                            goals = rest_goals;
                            lean_goals = f.lean_goals @ [(ctx, goal_term)]
                          } in
                          Printf.printf "------- Goal processed for Lean and moved from active goals --------\n\n";
                          Success (ProofFrame new_frame_state)
                        else
                          let error_msg = Printf.sprintf "Failed to write Lean file to '%s'." full_lean_path in
                          TacticError error_msg
          end


and eval_tac_simpl (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: ls ->
      (* create the typing function *)
      let typing wfctx t =
        match calc_type wfctx t with
        | Type type_t -> Some type_t
        | TypeError _ -> None
      in
      let new_goal = simpl typing (get_pf_wfctx f) hd in
      let new_frame = {
        env = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = (ctx, new_goal) :: ls;
        lean_goals  = f.lean_goals;
      } in
      Success (ProofFrame new_frame)

and eval_tac_rewrite (f: proof_frame) (t: terms) (l2r: bool) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: ls ->
      let wfctx = get_pf_wfctx f in
      (* Check the application condition *)
      (* check the type of witness t *)
      match calc_type wfctx t with
      | Type (Fun {head; args=[lhs; rhs]}) when head = _eq ->
        let from_ = if l2r then lhs else rhs in
        let to_ = if l2r then rhs else lhs in
        let new_goal = 
          replace hd from_ to_
        in
        let new_frame = {
          env         = f.env;
          proof_name  = f.proof_name;
          proof_prop  = f.proof_prop;
          goals       = (ctx, new_goal) :: ls;
          lean_goals  = f.lean_goals
        } in
        Success (ProofFrame new_frame)
        
      | _ -> 
        TacticError (Printf.sprintf "The term %s is not a valid equality witness." (term2str t))

and eval_tac_RWRULE (f : proof_frame) (r: rewriting_rule) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      let typing wfctx t = 
        match calc_type wfctx t with
        | Type type_t -> Some type_t
        | TypeError _ -> None
      in
      (* Check the application condition *)
      let new_goal = 
        match apply_rewriting_rule_all r typing (get_pf_wfctx f) hd with
        | Some new_goal -> new_goal
        | None -> hd
      in
      let new_frame = {
        env = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = (ctx, new_goal) :: tl;
        lean_goals  = f.lean_goals;
      } in
      (* Add the proof to the frame. *)
      Success (ProofFrame new_frame)

and eval_tac_R_PRE (f: proof_frame) (new_pre: terms): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: ls ->
    match hd with
    | Fun {head=head; args=[pre; s1; s2; post]} when 
      (
        head = _judgement
      ) ->
      begin
        match type_check (get_pf_wfctx f) new_pre (Symbol _assn) with
        | Type _ ->
          let new_goal1 = 
            Fun {head=_entailment; args=[new_pre; pre]} in
          let new_goal2 = 
            Fun {head=_judgement; args=[new_pre; s1; s2; post]} in
          let new_frame = {
            env = f.env;
            proof_name  = f.proof_name;
            proof_prop  = f.proof_prop;
            goals       = (ctx, new_goal1) :: (ctx, new_goal2) :: ls;
            lean_goals  = f.lean_goals;
          } in
          Success (ProofFrame new_frame)
        | TypeError msg -> TacticError (Printf.sprintf "r_pre application error. %s is not an assertion. %s" (term2str new_pre) msg)
      end
    | _ -> TacticError "r_pre cannot apply here."



and eval_tac_R_POST (f: proof_frame) (new_post: terms): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: ls ->
    match hd with
    | Fun {head=head; args=[pre; s1; s2; post]} when 
      (
        head = _judgement
      ) ->
      begin
        match type_check (get_pf_wfctx f) new_post (Symbol _assn) with
        | Type _ ->
          let new_goal1 = 
            Fun {head=_entailment; args=[post; new_post]} in
          let new_goal2 = 
            Fun {head=_judgement; args=[pre; s1; s2; new_post]} in
          let new_frame = {
            env = f.env;
            proof_name  = f.proof_name;
            proof_prop  = f.proof_prop;
            goals       = (ctx, new_goal1) :: (ctx, new_goal2) :: ls;
            lean_goals  = f.lean_goals;
          } in
          Success (ProofFrame new_frame)
        | TypeError msg -> TacticError (Printf.sprintf "r_post application error. %s is not an assertion. %s" (term2str new_post) msg)
      end
    | _ -> TacticError "r_post cannot apply here."

and eval_tac_R_SKIP (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: ls ->
    (* Check the application condition *)
    match hd with
    | Fun {head=head; args=[pre; s1; s2; post]} when 
      (
        head = _judgement && 
        s1 = Fun {head=_seq; args=[Symbol _skip]} &&
        s2 = Fun {head=_seq; args=[Symbol _skip]}
      ) ->
      let new_goal = Fun {
        head = _entailment;
        args = [post; pre];
      } in
      let new_frame = {
        env = f.env;
        proof_name  = f.proof_name;
        proof_prop  = f.proof_prop;
        goals       = (ctx, new_goal) :: ls;
        lean_goals  = f.lean_goals;
      } in
      (* Add the proof to the frame. *)
      Success (ProofFrame new_frame)
    | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

and eval_tac_R_ASSIGN (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      match hd with
      | Fun {head=head; args=[
          Fun {head=head_pre; args=[phi; b]}; 
          Fun {head=head_s1; args=[stt1]}; 
          Fun {head=head_s2; args=[stt2]}; 
          Fun {head=head_post; args=[psi; a]}]} when 
        (
          head = _judgement && 
          head_s1 = _seq &&
          head_s2 = _seq &&
          head_pre = _vbar &&
          head_post = _vbar
        ) ->
        let aux (x : string) (e : terms) : tactic_result = 
         let goal_template = parse_terms "psisubst | Asubst <= phi | B" in
         let s = [
            ("psisubst", substitute psi x e);
            ("Asubst", substitute a x e);
            ("phi", phi);
            ("B", b);
         ] in
         let goal = apply_subst_unique_var s goal_template in
         let new_frame = {
            env = f.env;
            proof_name = f.proof_name;
            proof_prop = f.proof_prop;
            goals = (ctx, goal) :: tl;
            lean_goals  = f.lean_goals;
          } in
          Success (ProofFrame new_frame)
        in 
        begin
          match stt1, stt2 with
          | Fun {head; args=[Symbol x; e]}, Symbol v when head = _assign && v = _skip ->
            aux x e
          | Symbol v, Fun {head; args=[Symbol x; e]} when head = _assign && v = _skip ->
            aux x e
          | _ -> 
            TacticError (Printf.sprintf "The tactic is not applicable to the current goal: %s" (term2str hd))
        end
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal: %s" (term2str hd))
            
      

and eval_tac_R_SEQ (f: proof_frame) (n1: int) (n2: int) (t : terms): tactic_result =
  let empty_to_skip ls = match ls with 
    | [] -> [Symbol _skip]
    | lst -> lst
  in
  (* Check the intermediate assertion t *)
  match type_check (get_pf_wfctx f) t (Symbol _assn) with
  | TypeError msg -> TacticError (Printf.sprintf "%s is not typed as an assertion. %s" (term2str t) msg)
  | Type _ ->
    match f.goals with
    | [] -> TacticError "Nothing to prove."
    | (ctx, hd) :: tl ->
        (* Check the application condition *)
        match hd with
        | Fun {head=head; args=[pre; Fun {args=args1; _}; Fun {args=args2; _}; post]} when 
          (
            head = _judgement
          ) ->
          (* Calculate the maximum length of sequential composition *)
          let i1 = 
            if n1 >= 0 then n1
            else List.length args1 + n1
          in
          let i2 =
            if n2 >= 0 then n2
            else List.length args2 + n2
          in

          let seq1_first = get_first_elements args1 i1 |> empty_to_skip in
          let seq1_second = get_last_elements args1 (List.length args1 - i1) |> empty_to_skip in
          let seq2_first = get_first_elements args2 i2 |> empty_to_skip in
          let seq2_second = get_last_elements args2 (List.length args2 - i2) |> empty_to_skip in

          (* Construct the new goal *)
          let new_goal1 = Fun {
            head = _judgement;
            args = [pre; Fun {head=_seq; args=seq1_first}; Fun {head=_seq; args=seq2_first}; t]
          } in
          let new_goal2 = Fun {
            head = _judgement;
            args = [t; Fun {head=_seq; args=seq1_second}; Fun {head=_seq; args=seq2_second}; post]
          } in
          let new_frame = {
            env = f.env;
            proof_name = f.proof_name;
            proof_prop = f.proof_prop;
            goals = (ctx, new_goal1) :: (ctx, new_goal2) :: tl;
            lean_goals  = f.lean_goals;
          } in
          Success (ProofFrame new_frame)

        | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

(** 
  r_initq

  ( psi | (Sum i in USet, |i><0|_(q,q) A |0><i|_(q,q)) <= (phi /\ (true -> |0><0|_(q,q))) | B 
  -----------------------------------------------
  { phi | B } q := |0>; ~ skip; { psi | A }
*)
and eval_tac_R_INITQ (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      (* Check the application condition *)
      match hd with
      | Fun {head=head; args=[
          Fun {head=head_pre; args=[phi; b]}; 
          Fun {head=head_s1; args=[stt1]}; 
          Fun {head=head_s2; args=[stt2]}; 
          Fun {head=head_post; args=[psi; a]}]} when 
        (
          head = _judgement && 
          head_s1 = _seq &&
          head_s2 = _seq &&
          head_pre = _vbar &&
          head_post = _vbar
        ) ->
        (* the function to calculate the new frame *)
        let aux q : tactic_result =
        begin
          match calc_type (get_pf_wfctx f) q with
          | Type (Fun {head=head_type_q; args=[type_q]}) when head_type_q = _qreg ->
            let name = fresh_name_for_ctx (get_pf_wfctx f) "i" in
            let goal_template = parse_terms (Printf.sprintf "
            psi | SUM[USET[T], fun (%s : CTerm[T]) => (|%s>@<false|)_(q,q) @ A @ (|false>@<%s|)_(q,q)] 
            <= (phi /\\ (true -> (|false> @ <false|)_(q,q))) | B" name name name)
            in
            let s = [
              ("phi", phi);
              ("psi", psi);
              ("A", a);
              ("B", b);
              ("q", q);
              ("T", type_q);
            ]
            in
            let goal = apply_subst_unique_var s goal_template in
            let new_frame = {
              env = f.env;
              proof_name = f.proof_name;
              proof_prop = f.proof_prop;
              goals = (ctx, goal) :: tl;
              lean_goals  = f.lean_goals;
            }
            in 
            Success (ProofFrame new_frame)

          (* if q is not well typed as qreg *)
          | _ -> TacticError (Printf.sprintf "%s is not typed as QReg." (term2str q))
        end
        in
        (* case on which side has the init *)
        begin
          match stt1, stt2 with
          | Fun {head=head1; args=[q]}, Symbol sym2 when head1 = _init_qubit && sym2 = _skip -> aux q
          | Symbol sym1, Fun {head=head2; args=[q]} when head2 = _init_qubit && sym1 = _skip -> aux q
          | _ -> TacticError (Printf.sprintf "The tactic must apply on [init q; ~ skip;] or [skip; ~ init q;]")
        end

      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

(** 
  r_unitary

  (U^D_q) @ Psi <= Phi
  -----------------------------------------------
  { Phi } q *= U; ~ skip; { Psi }
*)
and eval_tac_R_UNITARY (f: proof_frame) : tactic_result =
  match f.goals with
    | [] -> TacticError "Nothing to prove."
    | (ctx, hd) :: tl ->
        (* Check the application condition *)
        match hd with
        | Fun {head=head; args=[
            phi; 
            Fun {head=head_s1; args=[stt1]}; 
            Fun {head=head_s2; args=[stt2]}; 
            psi;]} when 
          (
            head = _judgement && 
            head_s1 = _seq &&
            head_s2 = _seq
          ) ->
          (* the function to calculate the new frame *)
          let aux u q : tactic_result =
            let goal_template = parse_terms (Printf.sprintf "(U^D_(q,q)) @@ Psi <= Phi")
            in
            let s = [
              ("Phi", phi);
              ("Psi", psi);
              ("U", u);
              ("q", q);
            ]
            in
            let goal = apply_subst_unique_var s goal_template in
            let new_frame = {
              env         = f.env;
              proof_name  = f.proof_name;
              proof_prop  = f.proof_prop;
              goals       = (ctx, goal) :: tl;
              lean_goals  = f.lean_goals
            }
            in 
            Success (ProofFrame new_frame)

          in
          (* case on which side has the init *)
          begin
            match stt1, stt2 with
            | Fun {head=head1; args=[u_opt; q]}, Symbol sym2 when head1 = _unitary && sym2 = _skip -> aux u_opt q
            | Symbol sym1, Fun {head=head2; args=[u_opt; q]} when head2 = _unitary && sym1 = _skip -> aux u_opt q
            | _ -> TacticError (Printf.sprintf "The tactic must apply on [unitary U q; ~ skip;] or [skip; ~ unitary U q;]")
          end

        | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

and eval_tac_R_MEAS (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    (* Check the application condition *)
    match hd with
    | Fun {head=head; args=[
        pre; 
        Fun {head=head_s1; args=[stt1]}; 
        Fun {head=head_s2; args=[stt2]}; 
        post;]} when 
      (
        head = _judgement && 
        head_s1 = _seq &&
        head_s2 = _seq
      ) ->
        let aux x m_opt q :  tactic_result =
          match _measure_wp_goal x pre post m_opt q with
          | Some goal_wp ->  
            let new_frame = {
              env         = f.env;
              proof_name  = f.proof_name;
              proof_prop  = f.proof_prop;
              goals       = (ctx, goal_wp) :: tl;
              lean_goals  = f.lean_goals
            } in
            Success (ProofFrame new_frame)
          | None -> 
            TacticError (Printf.sprintf "The measure tactic cannot apply to the current goal: %s" (term2str hd))
        in
        begin match stt1, stt2 with
        | Fun {head=head1; args=[Symbol x; m_opt; q]}, Symbol sym2 when head1 = _meas && sym2 = _skip -> aux x m_opt q
        | Symbol sym1, Fun {head=head2; args=[Symbol x; m_opt; q]} when head2 = _meas && sym1 = _skip -> aux x m_opt q
        | _ -> TacticError (Printf.sprintf "The tactic must apply on [measure x m_opt q; ~ skip;] or [skip; ~ measure x m_opt q;]")
        end
    | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal: %s" (term2str hd))

      

and eval_tac_R_IF (f: proof_frame) (qs: terms): tactic_result = 
  match f.goals with
    | [] -> TacticError "Nothing to prove."
    | (ctx, hd) :: tl ->
        (* Check the application condition *)
        match hd with
        | Fun {head=head; args=[
            Fun {head=head_vbar; args=[phi; bb]}; 
            Fun {head=head_s1; args=[stt1]}; 
            Fun {head=head_s2; args=[stt2]}; 
            post;]} when 
          (
            head = _judgement && 
            head_vbar = _vbar &&
            head_s1 = _seq &&
            head_s2 = _seq
          ) ->
          (* check the qs *)
          begin
            match calc_type (get_pf_wfctx f) qs with
            | Type (Fun {head; args=[tt];}) when head = _qreg ->
              (* the function to calculate the new frame *)
              let aux b s1 s2 : tactic_result =
                let goal_template = parse_terms ("{ (~ xb -> 0O[type]_(qs, qs)) /\\ phi | B } S ~ skip; { post }")
                in
                let s_true = [
                  ("xb", b);
                  ("type", tt);
                  ("qs", qs);
                  ("phi", phi);
                  ("B", bb);
                  ("S", s1);
                  ("post", post);
                ] in
                let goal_true = apply_subst_unique_var s_true goal_template in
                let s_false = [
                  ("xb", Fun {head=_not; args=[b]});
                  ("type", tt);
                  ("qs", qs);
                  ("phi", phi);
                  ("B", bb);
                  ("S", s2);
                  ("post", post);
                ] in
                let goal_false = apply_subst_unique_var s_false goal_template in
                let new_frame = {
                  env         = f.env;
                  proof_name  = f.proof_name;
                  proof_prop  = f.proof_prop;
                  goals       = (ctx, goal_true) :: (ctx, goal_false) :: tl;
                  lean_goals  = f.lean_goals
                }
                in 
                Success (ProofFrame new_frame)

            in
            (* case on which side has the init *)
            begin
              match stt1, stt2 with
              | Fun {head=head1; args=[b; s1; s2]}, Symbol sym2 when head1 = _if && sym2 = _skip -> aux b s1 s2
              | Symbol sym1, Fun {head=head2; args=[b; s1; s2]} when head2 = _if && sym1 = _skip -> aux b s1 s2
              | _ -> TacticError (Printf.sprintf "The tactic must apply on [if b then s1 end s2 end; ~ skip;] or [skip; ~ if b then s1 end s2 end;]")
            end

          | _ -> TacticError (Printf.sprintf "%s is not typed as QReg." (term2str qs))
          
          end

        | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")


and eval_tac_R_WHILE (f: proof_frame) (qs: terms) (phi: terms): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    (* Check the application condition *)
    match hd, phi with
    | Fun {head=head; args=[
        pre; 
        Fun {head=head_s1; args=[stt1]}; 
        Fun {head=head_s2; args=[stt2]}; 
        post;]},
      Fun {head=head_vbar; args=[psi; a]} when 
      (
        head_vbar = _vbar &&
        head = _judgement &&
        head_s1 = _seq &&
        head_s2 = _seq
      ) ->
      (* check the qs *)
      let aux b s : tactic_result =
        match calc_type (get_pf_wfctx f) qs with
        | Type (Fun {head; args=[tt];}) when head = _qreg ->
          (* the function to calculate the new frame *)

            let goal_template = parse_terms ("{ (~ b -> 0O[type]_(qs, qs)) /\\ psi | A } S ~ skip; { psi | A }") in
            let goal_pre_template = parse_terms ("psi | A  <= pre") in
            let goal_post_template = parse_terms ("post <= (b -> 0O[type]_(qs, qs)) /\\ psi | A") in
            let s = [
              ("b", b);
              ("type", tt);
              ("qs", qs);
              ("psi", psi);
              ("A", a);
              ("S", s);
              ("pre", pre);
              ("post", post);
            ] in
            let goal = apply_subst_unique_var s goal_template in
            let goal_pre = apply_subst_unique_var s goal_pre_template in
            let goal_post = apply_subst_unique_var s goal_post_template in
            let new_frame = {
              env         = f.env;
              proof_name  = f.proof_name;
              proof_prop  = f.proof_prop;
              goals       =  (ctx, goal_pre) :: (ctx, goal_post) :: (ctx, goal) :: tl;
              lean_goals  = f.lean_goals
            }
            in 
            Success (ProofFrame new_frame)

        | _ -> TacticError (Printf.sprintf "%s is not typed as QReg." (term2str qs))
      in 
      begin match stt1, stt2 with
      | Fun {head=head1; args=[b1; s1]}, Symbol _v when head1 = _while && _v = _skip ->
        aux b1 s1
      | Symbol _v, Fun {head=head2; args=[b2; s2]} when head2 = _while && _v = _skip ->
        aux b2 s2
      | _ -> TacticError (Printf.sprintf "The tactic must apply on [while b1 do s1 end; ~ skip;] or [skip; ~ while b1 do s1 end;].")
      end

    | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")


and eval_tac_R_WHILE_WHILE (f: proof_frame) (qs: terms) (phi: terms): tactic_result = 
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      (* Check the application condition *)
      match hd, phi with
      | Fun {head=head; args=[
          pre; 
          Fun {head=head_s1; args=[stt1]}; 
          Fun {head=head_s2; args=[stt2]}; 
          post;]},
        Fun {head=head_vbar; args=[psi; a]} when 
        (
          head_vbar = _vbar &&
          head = _judgement &&
          head_s1 = _seq &&
          head_s2 = _seq
        ) ->
        (* check the qs *)
        begin
          match calc_type (get_pf_wfctx f) qs with
          | Type (Fun {head; args=[tt];}) when head = _qreg ->
            (* the function to calculate the new frame *)
            begin
            match stt1, stt2 with
            | Fun {head=head1; args=[b1; s1]}, 
              Fun {head=head2; args=[b2; s2]} when
              head1 = _while && head2 = _while ->
                
                let goal_template = parse_terms ("{ (~ (b1 /\\ b2) -> 0O[type]_(qs, qs)) /\\ psi | A } S1 ~ S2 { (~ (b1 == b2) -> 0O[type]_(qs, qs)) /\\ psi | A }") in
                let goal_pre_template = parse_terms ("(~ (b1 == b2) -> 0O[type]_(qs, qs)) /\\ psi | A  <= pre") in
                let goal_post_template = parse_terms ("post <= (~ (~ b1 /\\ ~ b2) -> 0O[type]_(qs, qs)) /\\ psi | A") in
                let s = [
                  ("b1", b1);
                  ("b2", b2);
                  ("type", tt);
                  ("qs", qs);
                  ("psi", psi);
                  ("A", a);
                  ("S1", s1);
                  ("S2", s2);
                  ("pre", pre);
                  ("post", post);
                ] in
                let goal = apply_subst_unique_var s goal_template in
                let goal_pre = apply_subst_unique_var s goal_pre_template in
                let goal_post = apply_subst_unique_var s goal_post_template in
                let new_frame = {
                  env         = f.env;
                  proof_name  = f.proof_name;
                  proof_prop  = f.proof_prop;
                  goals       =  (ctx, goal_pre) :: (ctx, goal_post) :: (ctx, goal) :: tl;
                  lean_goals  = f.lean_goals
                }
                in 
                Success (ProofFrame new_frame)

          | _ -> TacticError (Printf.sprintf "The tactic must apply on [while b1 do s1 end; ~ while b2 do s2 end;].")
          end

        | _ -> TacticError (Printf.sprintf "%s is not typed as QReg." (term2str qs))
        end

      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

and eval_tac_R_MEAS_MEAS (f: proof_frame) (switch: bool): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      let wfctx = get_pf_wfctx f in
      (* Check the application condition *)
      let is_zeroo t =
        match t with
        | Fun {head; args=[Fun{head=head_o; _}; _]} when head = _subscript && head_o = _zeroo -> true
        | _ -> false
      in
      match hd with
      | Fun {head=head; args=[
          Fun {head=head_pre; args=[phi; zero_pre]}; 
          Fun {head=head_s1; args=[Fun {head=head_meas1; args=[Symbol x1; m_opt1; qs1]}]}; 
          Fun {head=head_s2; args=[Fun {head=head_meas2; args=[Symbol x2; m_opt2; qs2]}]}; 
          Fun {head=head_post; args=[psi; zero_post]};]} when 
        (
          head = _judgement && 
          head_pre = _vbar && (is_zeroo zero_pre) &&
          head_s1 = _seq && head_meas1 = _meas &&
          head_s2 = _seq && head_meas2 = _meas &&
          head_post = _vbar && (is_zeroo zero_post)
        ) ->
        let goal_vee_bj = _measure_sample_or_bj phi in
        let goal_qcoupling = _meas_meas_coupling_goal wfctx x1 x2 phi psi m_opt1 qs1 m_opt2 qs2 switch in
        begin
          match goal_vee_bj, goal_qcoupling with
          | Some goal_vee_bj, Some goal_qcoupling -> 
            let new_frame = {
              env         = f.env;
              proof_name  = f.proof_name;
              proof_prop  = f.proof_prop;
              goals       = (ctx, goal_vee_bj) :: 
                            (ctx, goal_qcoupling) :: tl;
              lean_goals = f.lean_goals
            } in
            Success (ProofFrame new_frame)
          | _ -> TacticError (Printf.sprintf "Format matching failed.")
        end

      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

(* switch: the flag controls the bijection between measurement and sampling *)
and eval_tac_R_MEAS_SAMPLE (f: proof_frame) (switch: bool): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      let wfctx = get_pf_wfctx f in
      (* Check the application condition *)
      let is_zeroo t =
        match t with
        | Fun {head; args=[Fun{head=head_o; _}; _]} when head = _subscript && head_o = _zeroo -> true
        | _ -> false
      in
      match hd with
      | Fun {head=head; args=[
          Fun {head=head_pre; args=[phi; zero_pre]}; 
          Fun {head=head_s1; args=[Fun {head=head_meas; args=[Symbol x1; m_opt; qs]}]}; 
          Fun {head=head_s2; args=[Fun {head=head_sample; args=[Symbol x2; mu]}]}; 
          Fun {head=head_post; args=[psi; zero_post]};]} when 
        (
          head = _judgement && 
          head_pre = _vbar && (is_zeroo zero_pre) &&
          head_s1 = _seq && head_meas = _meas &&
          head_s2 = _seq && head_sample = _passign &&
          head_post = _vbar && (is_zeroo zero_post)
        ) ->
        let goal_vee_bj = _measure_sample_or_bj phi in
        let goal_trace = _measure_sample_trace_goal wfctx phi m_opt qs mu switch in
        let goal_proj = _measure_sample_proj_goal x1 x2 phi psi m_opt qs switch in
        begin
          match goal_vee_bj, goal_trace, goal_proj with
          | Some goal_vee_bj, Some goal_trace, Some goal_proj -> 
            let new_frame = {
              env         = f.env;
              proof_name  = f.proof_name;
              proof_prop  = f.proof_prop;
              goals       = (ctx, goal_vee_bj) :: 
                            (ctx, goal_trace) :: 
                            (ctx, goal_proj) :: tl;
              lean_goals = f.lean_goals
            } in
            Success (ProofFrame new_frame)
          | _ -> TacticError (Printf.sprintf "Format matching failed.")
        end

      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")


and eval_tac_JUDGE_SWAP (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      (* Check the application condition *)
      match hd with
      | Fun {head; args=[pre; s1; s2; post]} when head = _judgement ->
        let new_goal = Fun {head; args=[pre; s2; s1; post]} in
        let new_frame = {
          env         = f.env;
          proof_name  = f.proof_name;
          proof_prop  = f.proof_prop;
          goals       = (ctx, new_goal) :: tl;
          lean_goals  = f.lean_goals
        } in
        Success (ProofFrame new_frame)
      | _ -> TacticError "judge_swap tactic must apply on judgements."

  
and eval_tac_CQ_ENTAIL (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
      let wfctx = get_pf_wfctx f in
      (* Check the application condition *)
      match hd with
      | Fun {head; args=[a; b]} when head = _entailment ->
        begin
          match 
            type_check wfctx a (Symbol _cqproj), 
            type_check wfctx b (Symbol _cqproj) with
          | Type _, Type _ -> 
            begin
              match cq_entailment_destruct hd with
              | Some p -> 
                let new_frame = {
                  env         = f.env;
                  proof_name  = f.proof_name;
                  proof_prop  = f.proof_prop;
                  goals       = (ctx, p) :: tl;
                  lean_goals  = f.lean_goals;
                } in
                Success (ProofFrame new_frame)
              | None -> TacticError "cq_entail tactic cannot apply here. cq-projector are not in normal form."
            end
          | _ -> TacticError "cq_entail tactic cannot apply here. cq-projector are not well typed."
        end
      | _ -> TacticError "cq_entail tactic must apply on cq-projector entailment."

and eval_tac_DIRAC (f: proof_frame) : tactic_result = 
  (* check the uniqueness of the quantum variable list qs *)
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    let typing wfctx t = 
      match calc_type wfctx t with
      | Type type_t -> Some type_t
      | TypeError _ -> None
    in
    let new_goal = dirac_simpl typing (get_pf_wfctx f) hd in
    let new_frame = {
      env         = f.env;
      proof_name  = f.proof_name;
      proof_prop  = f.proof_prop;
      goals       = (ctx, new_goal) :: tl;
      lean_goals  = f.lean_goals;
    } in
    Success (ProofFrame new_frame)
      
and eval_tac_SIMPL_ENTAIL (f: proof_frame) : tactic_result =
  (* check the uniqueness of the quantum variable list qs *)
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    let typing wfctx t = 
      match calc_type wfctx t with
      | Type type_t -> Some type_t
      | TypeError _ -> None
    in
    let new_goal = simpl_entail typing (get_pf_wfctx f) hd in
    let new_frame = {
      env         = f.env;
      proof_name  = f.proof_name;
      proof_prop  = f.proof_prop;
      goals       = (ctx, new_goal) :: tl;
      lean_goals  = f.lean_goals
    } in
    Success (ProofFrame new_frame)

and eval_tac_ENTAIL_TRANS (f: proof_frame) (e: terms): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    match hd with
    | Fun {head; args=[a; b]} when head = _entailment ->
      begin
        let wfctx = get_pf_wfctx f in
        match calc_type wfctx e with
        | TypeError msg -> 
          TacticError (Printf.sprintf "The term %s is not well typed. It should indicate error in the prover system. %s" (term2str e) msg)
        | Type t ->
          match type_check wfctx e t with
          | Type _ ->
            let new_goal1 = Fun {head=_entailment; args=[a; e]} in
            let new_goal2 = Fun {head=_entailment; args=[e; b]} in
            let new_frame = {
              env         = f.env;
              proof_name  = f.proof_name;
              proof_prop  = f.proof_prop;
              goals       = (ctx, new_goal1) :: (ctx, new_goal2) :: tl;
              lean_goals  = f.lean_goals;
            } in
            Success (ProofFrame new_frame)
          | TypeError msg ->
            TacticError (Printf.sprintf "The term %s is not well typed as %s. %s" (term2str e) (term2str t) msg)
      end
    | _ ->
      TacticError (Printf.sprintf "The tactic must apply on entailment goals, but got %s." (term2str hd))
    
and eval_tac_CYLINDER_EXT (f: proof_frame) (qs: terms): tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    let wfctx = get_pf_wfctx f in
    let trans = fun wfctx -> cylinder_ext wfctx qs in
    let new_goal = repeat_transforms [apply_trans_all trans wfctx] hd in 
    let new_frame = {
      env         = f.env;
      proof_name  = f.proof_name;
      proof_prop  = f.proof_prop;
      goals       = (ctx, new_goal) :: tl;
      lean_goals  = f.lean_goals;
    } in
    Success (ProofFrame new_frame)
    


let get_status (p: prover) (eval_res: eval_result) : string =
  let prover_status = prover2str p in
  match eval_res with
  | Success -> prover_status
  | ProverError msg -> prover_status ^ "\n---------------------------------------------------------------\nError: \n" ^ msg
  | Pause ->
    prover_status ^ "\n---------------------------------------------------------------\n" ^ "Paused by user."


(* the function to evaluate a command list, stops at the first error. *)
let rec eval_list (p: prover) (cmds: command list) : eval_result
  = 
  match cmds with
  | [] -> Success
  | [tail] -> eval p tail
  | cmd :: rest ->
    let res = eval p cmd in
      match res with
      | Success -> eval_list p rest
      | ProverError _ -> res
      | Pause -> Pause