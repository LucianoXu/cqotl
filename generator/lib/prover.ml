open Ast
open Pretty_printer
open Typing
open Reasoning
open Utils

type normal_frame = {
  env: envItem list;
}

type proof_frame = {
  (* The environment for the whole proof *)
  env : envItem list;
  proof_name: string;
  proof_prop: terms;
  goals: (envItem list * terms) list;
}

let get_pf_wfctx (pf : proof_frame) : wf_ctx =
  match pf.goals with
  | [] -> env2wfctx pf.env
  | (ctx, _)::_ -> 
      {env = pf.env; ctx = ctx}


type frame = 
  | NormalFrame of normal_frame
  | ProofFrame of proof_frame


(** Get the environment from the frame. *)
let get_frame_wfctx (f: frame) : wf_ctx =
  match f with
  | NormalFrame {env} -> env2wfctx env
  | ProofFrame pf -> get_pf_wfctx pf

let add_envItem (f: normal_frame) (item: envItem) : frame =
  NormalFrame {env = item::f.env}



(*************************************************************)
(* Proof Frame Operations *)

let open_proof (f: normal_frame) (name: string) (prop: terms) : frame =
  ProofFrame {
    env = f.env;
    proof_name = name;
    proof_prop = prop;
    goals = [([], prop)]
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
        env = f.env;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = tl
      } in
      new_frame

(** Add a new goal to the proof_frame with empty local context. *)
let add_goal (f: proof_frame) (goal: terms) : proof_frame =
  let new_frame = {
        env = f.env;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = ([], goal)::f.goals
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

(* The whole information about the frame *)
let frame2str (f: frame): string =
  match f with
  | NormalFrame {env} -> 
      let env_str = env2str env in
        Printf.sprintf "%s" env_str
  | ProofFrame f ->
    let env_str = wfctx2str (get_pf_wfctx f) in
    let proof_mode_str = Printf.sprintf "\n---------------------------------------------------------------\n[Proof Mode]\n\n%s" (goals2str f)
    in
      Printf.sprintf "%s%s" env_str proof_mode_str

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
          | Sorry -> eval_tac_sorry proof_f
          | Intro v -> eval_tac_intro proof_f v
          | Choose i -> eval_tac_choose proof_f i
          | Split -> eval_tac_split proof_f
          | ByLean -> eval_tac_by_lean proof_f
          | Simpl -> eval_tac_simpl proof_f

          | R_SKIP -> eval_tac_R_SKIP proof_f
          | R_SEQ (i, t) -> eval_tac_R_SEQ proof_f i t
          | R_INITQ -> eval_tac_R_INITQ proof_f

          | CQ_ENTAIL -> eval_tac_CQ_ENTAIL proof_f
          | DELABEL -> eval_tac_DELABEL proof_f

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
          proof_name = f.proof_name;
          proof_prop = f.proof_prop;
          goals = (Assumption {name; t}::ctx, substitute t' x (Symbol name)) :: tl;
        } in
        Success (ProofFrame new_frame)
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

and eval_tac_choose (f: proof_frame) (i: int) : tactic_result =
  if i < 1 || i > List.length f.goals then
    TacticError (Printf.sprintf "The index %d is out of range." i)
  else
    Success (ProofFrame {
      env = f.env;
      proof_name = f.proof_name;
      proof_prop = f.proof_prop;
      goals = move_to_front f.goals i;
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
            env = f.env;
            proof_name = f.proof_name;
            proof_prop = f.proof_prop;
            goals = (ctx, t1) :: (ctx, t2) :: tl;
          }
          in 
          Success (ProofFrame new_frame)
        | _ -> TacticError (Printf.sprintf "splic tactic cannot apply here. The two terms %s and %s are not typed as Type." (term2str t1) (term2str t2))
      end
    | _ -> TacticError "split tactic cannot apply here."

and eval_tac_by_lean (f: proof_frame) : tactic_result =
  (*** IMPLEMENT THE CODE TO GET LEAN CODE FOR THE FIRST GOAL FROM THE proof_frame *)
  let output_code = frame2str (ProofFrame f) in
  Printf.printf "Lean code:\n%s\n" output_code;
  eval_tac_sorry f

and eval_tac_simpl (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: ls ->
      (* create the typing function *)
      let typing t =
        let wfctx = get_pf_wfctx f in
        match calc_type wfctx t with
        | Type type_t -> Some type_t
        | TypeError _ -> None
      in
      let new_goal = simpl typing hd in
      let new_frame = {
        env = f.env;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = (ctx, new_goal) :: ls;
      } in
      Success (ProofFrame new_frame)

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

and eval_tac_R_SEQ (f: proof_frame) (n: int) (t : terms): tactic_result =
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
          let i1, i2 = 
            if n >= 0 then n, n
            else (List.length args1 + n, List.length args2 + n)
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
          } in
          Success (ProofFrame new_frame)

        | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

(** 
  r_initq

  phi /\ (true -> |0><0|_(q,q)) <= psi
  Sum i in USet, |i><0|_(q,q) A |0><i|_(q,q) <= B 
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
          Fun {head=head_pre; args=[phi; a]}; 
          Fun {head=head_s1; args=[stt1]}; 
          Fun {head=head_s2; args=[stt2]}; 
          Fun {head=head_post; args=[psi; b]}]} when 
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
            (* Goal1: phi /\ (true -> |0><0|_(q,q)) <= psi *)
            let goal1 = Fun {
              head = _entailment;
              args =[
                Fun {
                  head = _wedge;
                  args = [
                    phi;
                    Fun {
                      head = _imply;
                      args = [
                        Symbol _true;
                        labelled_proj (Symbol _false) q
                      ]
                    }
                  ]
                };
                psi
              ]
            }
            in
            (* Goal2: B <= SUM[USET[T], fun (i : CTerm[T]) => |i><0|_(q,q) A |0><i|_(q,q)] *)
            let name = fresh_name_for_ctx (get_pf_wfctx f) "i" in
            let goal2 = Fun {
              head = _entailment;
              args = [
                Fun {
                  head = _sum;
                  args = [
                    (* the set USET[T] *)
                    Fun {
                      head = _uset;
                      args = [type_q];
                    };
                    (* the function *)
                    Fun {
                      head = _fun;
                      args = [
                        Symbol name;
                        (* CTerm[T] *)
                        Fun {
                          head = _cterm;
                          args = [type_q];
                        };
                        (* |i><0|_(q,q) A |0><i|_(q,q) *)
                        Fun {
                          head = _apply;
                          args = [
                            labelled_ketbra (Symbol name) (Symbol _false) q;
                            Fun {
                              head = _apply;
                              args = [
                                a;
                                labelled_ketbra (Symbol _false) (Symbol name) q;
                              ]
                            }
                          ]
                        }
                      ]
                    }
                  ]
                };
                b;
              ]
            }
            in
            let new_frame = {
              env = f.env;
              proof_name = f.proof_name;
              proof_prop = f.proof_prop;
              goals = (ctx, goal1) :: (ctx, goal2) :: tl;
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
                  env = f.env;
                  proof_name = f.proof_name;
                  proof_prop = f.proof_prop;
                  goals = (ctx, p) :: tl;
                } in
                Success (ProofFrame new_frame)
              | None -> TacticError "cq_entail tactic cannot apply here. cq-projector are not in normal form."
            end
          | _ -> TacticError "cq_entail tactic cannot apply here. cq-projector are not well typed."
        end
      | _ -> TacticError "cq_entail tactic must apply on cq-projector entailment."

and eval_tac_DELABEL (f: proof_frame) : tactic_result = 
  (* check the uniqueness of the quantum variable list qs *)
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | (ctx, hd) :: tl ->
    let typing t = 
      let wfctx = get_pf_wfctx f in
      match calc_type wfctx t with
      | Type type_t -> Some type_t
      | TypeError _ -> None
    in
    let new_goal = delabel typing hd in
    let new_frame = {
      env = f.env;
      proof_name = f.proof_name;
      proof_prop = f.proof_prop;
      goals = (ctx, new_goal) :: tl;
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