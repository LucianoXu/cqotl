open Ast
open Pretty_printer
open Typing
open Reasoning
open Utils

type normal_frame = {
  env: envItem list;
}

type proof_frame = {
  wfctx: wf_ctx;
  proof_name: string;
  proof_prop: terms;
  goals: terms list;
}

type frame = 
  | NormalFrame of normal_frame
  | ProofFrame of proof_frame


(** Get the environment from the frame. *)
let get_frame_wfctx (f: frame) : wf_ctx =
  match f with
  | NormalFrame {env} -> env2wfctx env
  | ProofFrame {wfctx; _} -> wfctx

let add_envItem (f: normal_frame) (item: envItem) : frame =
  NormalFrame {env = item::f.env}



(*************************************************************)
(* Proof Frame Operations *)

let open_proof (f: normal_frame) (name: string) (prop: terms) : frame =
  ProofFrame {
    wfctx = env2wfctx f.env;
    proof_name = name;
    proof_prop = prop;
    goals = [prop]
  }

let close_proof (f: proof_frame) : frame =
  NormalFrame {
    env = (Definition {name = f.proof_name; t=f.proof_prop; e=Opaque}) :: f.wfctx.env
  }

let discharge_first_goal (f: proof_frame) : proof_frame =
  match f.goals with
  | [] -> f
  | _ :: tl ->
      let new_frame = {
        wfctx = f.wfctx;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = tl
      } in
      new_frame

let add_goal (f: proof_frame) (goal: terms) : proof_frame =
  let new_frame = {
        wfctx = f.wfctx;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = goal::f.goals
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
      (fun i p -> Printf.sprintf "(%d/%d) %s" (i + 1) total (term2str p))
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
    let env_str = wfctx2str f.wfctx in
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
          | Choose i -> eval_tac_choose proof_f i
          | ByLean -> eval_tac_by_lean proof_f
          | Simpl -> eval_tac_simpl proof_f
          (* | R_SKIP -> eval_tac_R_SKIP proof_f
          | SEQ_FRONT t -> eval_tac_SEQ_FRONT proof_f t
          | SEQ_BACK t -> eval_tac_SEQ_BACK proof_f t
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

and eval_tac_choose (f: proof_frame) (i: int) : tactic_result =
  if i < 1 || i > List.length f.goals then
    TacticError (Printf.sprintf "The index %d is out of range." i)
  else
    Success (ProofFrame {
      wfctx = f.wfctx;
      proof_name = f.proof_name;
      proof_prop = f.proof_prop;
      goals = move_to_front f.goals i;
    })

and eval_tac_by_lean (f: proof_frame) : tactic_result =
  (*** IMPLEMENT THE CODE TO GET LEAN CODE FOR THE FIRST GOAL FROM THE proof_frame *)
  let output_code = frame2str (ProofFrame f) in
  Printf.printf "Lean code:\n%s\n" output_code;
  eval_tac_sorry f

and eval_tac_simpl (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | hd :: ls ->
      let new_goal = simpl hd in
      let new_frame = {
        wfctx = f.wfctx;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = new_goal :: ls;
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