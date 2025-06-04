open Ast
open Ast_transform
open Pretty_printer
open Typing
open Reasoning
open Utils
open Parser_utils

type normal_frame = {
  env: envItem list;
}

(* The environment for the whole proof *)
type proof_frame = {
  env : envItem list;
  proof_name: string;
  proof_prop: terms;
  goals: (envItem list * terms) list;
  lean_goals: (envItem list * terms) list;
}

let get_pf_wfctx (pf : proof_frame) : wf_ctx =
  match pf.goals with
  | [] -> env2wfctx pf.env
  | (ctx, _)::_ -> 
      {env = pf.env; ctx = ctx}

type frame = 
  | NormalFrame of normal_frame
  | ProofFrame  of proof_frame

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

(** The prover. 
    Initially it has empty stack and the frame is described by empty_frame. *)
type prover = {
  mutable stack: frame list;  (* The new frames *)
}

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

type tactic_result =
  | Success of frame
  | TacticError of string

type eval_result = 
  | Success
  | ProverError of string
  | Pause

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
          let type_of_t = calc_type wfctx t in
          match type_of_t with
          | Type (Symbol sym) when sym = _type -> 
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
      match type_check wfctx prop (Symbol _type) with
      | Type _ -> 
          p.stack <- (open_proof normal_f x prop) :: p.stack;
          Success
      | TypeError msg -> 
          ProverError (Printf.sprintf "%s cannot be typed as Type, therfore witness cannot be proved. %s" (term2str prop) msg)


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
          | Intro v       -> eval_tac_intro proof_f v
          | Choose i      -> eval_tac_choose proof_f i
          | Split         -> eval_tac_split proof_f
          | ByLean        -> eval_tac_by_lean proof_f
          | Simpl         -> eval_tac_simpl proof_f
          | Rewrite_L2R t -> eval_tac_rewrite proof_f t true
          | Rewrite_R2L t -> eval_tac_rewrite proof_f t false
          | R_SKIP        -> eval_tac_R_SKIP proof_f
          | R_SEQ (n1, n2, t) -> eval_tac_R_SEQ proof_f n1 n2 t
          | R_INITQ       -> eval_tac_R_INITQ proof_f
          | R_UNITARY     -> eval_tac_R_UNITARY proof_f
          | R_MEAS_SAMPLE switch -> eval_tac_R_MEAS_SAMPLE proof_f switch
          | JUDGE_SWAP    -> eval_tac_JUDGE_SWAP proof_f
          | CQ_ENTAIL     -> eval_tac_CQ_ENTAIL proof_f
          | DIRAC         -> eval_tac_DIRAC proof_f
          | SIMPL_ENTAIL  -> eval_tac_SIMPL_ENTAIL proof_f

          (*
          | R_UNITARY1 -> eval_tac_R_UNITARY1 proof_f *)
          (* | _ -> raise (Failure "Tactic not implemented yet") *)
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
          type_check wfctx t1 (Symbol _type), 
          type_check wfctx t2 (Symbol _type) with
        | Type _, Type _ ->
          let new_frame = {
            env         = f.env;
            proof_name  = f.proof_name;
            proof_prop  = f.proof_prop;
            goals       = (ctx, t1) :: (ctx, t2) :: tl;
            lean_goals  = f.lean_goals
          }
          in 
          Success (ProofFrame new_frame)
        | _ -> TacticError (Printf.sprintf "splic tactic cannot apply here. The two terms %s and %s are not typed as Type." (term2str t1) (term2str t2))
      end
    | _ -> TacticError "split tactic cannot apply here."

and eval_tac_by_lean (f: proof_frame) : tactic_result =
  match f.goals with
  | []  -> TacticError "Nothing to prove. No proof obligation to translate to Lean."
  | (ctx, goal_term) :: rest_goals -> (* Getting the first goal *)
      let new_frame = {
            env         = f.env;
            proof_name  = f.proof_name;
            proof_prop  = f.proof_prop;
            goals       = rest_goals;
            lean_goals  = f.lean_goals @ [(ctx, goal_term)]
          } 
      in  let () = Printf.printf "------- Lean obligations updated --------" 
      in  Success (ProofFrame new_frame)
    
    (*
    and eval_tac_sorry (f: proof_frame) : tactic_result =
      match f.goals with
      | [] -> TacticError "Nothing to prove."
      | _ :: _ ->
          (* Add the proof to the frame. *)
          let new_frame = discharge_first_goal f in
          Success (ProofFrame new_frame)
      
    match goal_to_lean_ast wfctx ctx 
  let output_code = frame2str (ProofFrame f) in
  Printf.printf "Lean code (Hello World):\n%s\n" output_code;
  eval_tac_sorry f *)

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




and eval_tac_R_SKIP (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (_, hd) :: _ ->
      (* Check the application condition *)
      match hd with
      | Fun {head=head; args=[pre; s1; s2; post]} when 
        (
          head = _judgement && 
          s1 = Fun {head=_seq; args=[Symbol _skip]} &&
          s2 = Fun {head=_seq; args=[Symbol _skip]} &&
          pre = post
        ) ->
        let new_frame = discharge_first_goal f in
        (* Add the proof to the frame. *)
        Success (ProofFrame new_frame)
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

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
            psi | SUM[USET[T], fun (%s : CTERM[T]) => (|%s>@<false|)_(q,q) @ A @ (|false>@<%s|)_(q,q)] 
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
          Fun {head=head_s2; args=[Fun {head=head_sample; args=[Symbol x2; miu]}]}; 
          Fun {head=head_post; args=[psi; zero_post]};]} when 
        (
          head = _judgement && 
          head_pre = _vbar && (is_zeroo zero_pre) &&
          head_s1 = _seq && head_meas = _meas &&
          head_s2 = _seq && head_sample = _passign &&
          head_post = _vbar && (is_zeroo zero_post)
        ) ->
        let goal_vee_bj = _measure_sample_or_bj phi in
        let goal_trace = _measure_sample_trace_goal wfctx phi m_opt qs miu switch in
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
      | _ -> TacticError "cq_entail tactic must apply on cq-projector entailment."

  
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