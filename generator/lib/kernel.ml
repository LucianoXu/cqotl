open Ast
open Pretty_printer

type envItem =
  | Assumption of {name: string; t: types}
  | Definition of {name: string; t: types; e: terms}
  | Proof of {name: string; prop: props}
  | Hypothesis of {name: string; prop: props}

type context = envItem list

type normal_frame = {
  env: context;
}

type proof_frame = {
  env: context;
  proof_name: string;
  proof_prop: props;
  goals: props list;
}

(* The frame of the prover. *)
type frame = 
  | NormalFrame of normal_frame
  | ProofFrame of proof_frame

(* Find the item in the environment. *)

let get_ctx (f: frame) : context =
  match f with
  | NormalFrame {env} -> env
  | ProofFrame {env; _} -> env

let add_envItem (f: normal_frame) (item: envItem) : frame =
  NormalFrame {env = item::f.env}

let open_proof (f: normal_frame) (name: string) (prop: props) : frame =
  ProofFrame {
    env = f.env;
    proof_name = name;
    proof_prop = prop;
    goals = [prop]
  }

let close_proof (f: proof_frame) : frame =
  NormalFrame {env = (Proof {name = f.proof_name; prop=f.proof_prop}) :: f.env}

let discharge_first_goal (f: proof_frame) : frame =
  match f.goals with
  | [] -> ProofFrame f
  | _ :: tl ->
      let new_frame = {
        env = f.env;
        proof_name = f.proof_name;
        proof_prop = f.proof_prop;
        goals = tl
      } in
      ProofFrame new_frame

(* Find the item in the environment. *)

let find_item (f: frame) (name: string) : envItem option =
  List.find_opt (
    function
      | Assumption {name = n; _} -> n = name
      | Definition {name = n; _} -> n = name
      | Proof {name = n; _} -> n = name
      | Hypothesis {name = n; _} -> n = name
    ) 
  (get_ctx f)

type typing_result =
  | Type of types
  | Proof of props
  | TypeError of string

type valid_prop_result =
  | Valid
  | Invalid of string

(* decide whether the proposition is valid in the context *)
let rec valid_prop (f : frame) (prop: props) : valid_prop_result =
  match prop with
  | Unitary e -> 
      let t = calc_type f e in
      (match t with
      | Type (Opt _) -> Valid
      | Type _ -> 
          Invalid (Printf.sprintf "The term %s is not of operator type." (term2str e))
      | _ -> Invalid (Printf.sprintf "The term %s is not well typed." (term2str e))
      )
  | Assn lo ->
      let t = calc_type f lo in
      (match t with
      | Type (LOpt) -> Valid
      | Type _ -> 
          Invalid (Printf.sprintf "The term %s is not of labeled operator type." (term2str lo))
      | _ -> Invalid (Printf.sprintf "The term %s is not well typed." (term2str lo))
      )
  | Meas m -> 
      let t = calc_type f m in
      (match t with
      | Type (MeasOpt) -> Valid
      | Type _ -> 
          Invalid (Printf.sprintf "The term %s is not of measurement operator type." (term2str m))
      | _ -> Invalid (Printf.sprintf "The term %s is not well typed." (term2str m))
      )
  | Judgement {pre; s1; s2; post} -> 
      let t2 = calc_type f s1 in
      let t3 = calc_type f s2 in
      let pre_proved = prop_proved f (Assn pre) in
      let post_proved = prop_proved f (Assn post) in
        (match pre_proved, t2, t3, post_proved with
        | true, Type (Program), Type (Program), true -> Valid
        | false, _, _, _ -> 
            Invalid (Printf.sprintf "The precondition %s is not proved to be a valid assertion in the context." (term2str pre))
        | _, _, _, false -> 
            Invalid (Printf.sprintf "The postcondition %s is not proved to be a valid assertion in the context." (term2str post))
        | _, TypeError msg, _, _ -> 
            Invalid (Printf.sprintf "The term %s is not well typed: %s" (term2str s1) msg)
        | _, _, TypeError msg, _ ->
            Invalid (Printf.sprintf "The term %s is not well typed: %s" (term2str s2) msg)
        | _ -> Invalid (Printf.sprintf "Invalid judgement: %s." (prop2str prop))
        )
  | Eq {t1; t2} ->
      let t1_type = calc_type f t1 in
      let t2_type = calc_type f t2 in
        (match t1_type, t2_type with
        | Type (Opt n), Type (Opt m) when n = m -> Valid
        | Type LOpt, Type LOpt -> Valid
        | Type (Opt _), Type (Opt _) -> 
            Invalid (Printf.sprintf "The terms %s and %s are not of the same operator type." (term2str t1) (term2str t2))
        | _ -> 
            Invalid (Printf.sprintf "The terms %s and %s should have operator or labeled operator types." (term2str t1) (term2str t2))
        )
  (* | _ -> raise (Failure "Not implemented yet") *)

(* Check whether the proposition is proved in the context by directly search through the proofs and hypotheses *)
and prop_proved (frame : frame) (prop: props) : bool =
  let rec find_item_in_list (ctx: context) prop =
    match ctx with
    | [] -> false
    | hd :: tl -> 
        match hd with
        | Proof {name = _; prop = p} when p = prop -> true
        | Hypothesis {name = _; prop = p} when p = prop -> true
        | _ -> 
            (* Check the rest of the environment *)
            find_item_in_list tl prop
  in find_item_in_list (get_ctx frame) prop
  

(** Calculate the type of the term. Raise the corresponding error when typing failes. *)
and calc_type (f : frame) (s : terms) : typing_result = 
  match s with
  | Var x -> 
      calc_type_var f x
  | QRegTerm qs -> 
      calc_type_qreg f qs
  | OptTerm o ->
      calc_type_opt f o
  | LOptTerm lo ->
      calc_type_lopt f lo
  | MeasOpt _ ->
      raise (Failure "Unimplemented")
  | Stmt ss -> 
      calc_type_program f ss

and calc_type_var (f : frame) (v : string) : typing_result = 
  match find_item f v with
  | Some (Assumption {t; _}) | Some (Definition {t; _}) -> Type t
  | Some (Proof {prop; _}) | Some (Hypothesis {prop; _}) -> Proof prop
  | None -> TypeError (Printf.sprintf "Variable %s is not defined." v)

and calc_type_qreg (f : frame) (qs : qreg) : typing_result = 
  if List.for_all (fun qv -> (calc_type_var f qv) = Type QVar) qs then
    (* Check whether there are repeated variable in the register *)
    let rec check_repeated lst = 
      match lst with
      | [] -> true
      | x :: xs -> 
          if List.exists (fun y -> x = y) xs then
            false
          else
            check_repeated xs
    in
    if check_repeated qs then
      Type (QReg (List.length qs))
    else
      TypeError (Printf.sprintf "The quantum register %s contains repeated variables." (qreg2str qs))
  else
    TypeError (Printf.sprintf "The quantum register %s is not well typed." (qreg2str qs))

and calc_type_opt (f : frame) (o : opt) : typing_result = 
  match o with
  | Add {o1; o2} -> 
      let t1 = calc_type f o1 in
      let t2 = calc_type f o2 in
        if t1 = t2 then
          t1
        else
          TypeError (Printf.sprintf "The operator %s is not well typed." (opt2str o))

and calc_type_lopt (f : frame) (lo : lopt) : typing_result = 
  match lo with
  | Pair {opt; qs} -> 
      let t = calc_type f opt in
      let qs_t = calc_type_qreg f qs in
      match t, qs_t with
      | Type (Opt n), Type (QReg m) -> 
          if n = m then
            Type LOpt
          else
            TypeError (Printf.sprintf "The operator %s is not well typed, because the system number mismatch." (term2str opt))
      | _ ->
          TypeError (Printf.sprintf "The operator %s is not well typed." (term2str opt))

and calc_type_program (f : frame) (s : stmt_seq) : typing_result = 
  match s with
  | SingleCmd cmd -> 
      calc_type_stmt f cmd
  | cmd1 :: cmd2 -> 
      let t1 = calc_type_stmt f cmd1 in
      let t2 = calc_type_program f cmd2 in
        if t1 = Type Program && t2 = Type Program then
          Type Program
        else
          TypeError (Printf.sprintf "The program %s is not well typed." (stmt_seq_2_str s))

and calc_type_stmt (f :frame) (s : stmt) : typing_result = 
  match s with
  | Skip -> 
      Type Program
  | _ -> 
      Type Program
      (* Not implemented *)



(* The empty frame. *)
let empty_frame : frame = 
  NormalFrame {env = []}

(* Check whether a variable is defined in the frame. *)
let is_defined (f: frame) (name: string) : bool =
  find_item f name <> None


(* The prover. Initially it has empty stack and the frame is described by empty_frame. *)
type prover = {
  mutable stack: frame list;  (* The new frames *)
}

(* Get the latest frame of the environment. *)
let get_frame (p: prover) : frame =
  match p.stack with
  | [] -> empty_frame
  | f :: _ -> f

(* Initialize the prover with an empty stack. *)

let init_prover () : prover = 
  {stack = []}


(* formatting *)
let envItem2str (item: envItem ): string = 
  match item with
  | Assumption {name; t} -> 
      Printf.sprintf "%s : %s" name (type2str t)
  | Definition {name; t; e} -> 
      Printf.sprintf "%s := %s : %s" name (term2str e) (type2str t)
  | Proof {name; prop} -> 
      Printf.sprintf "%s := <proof> : %s" name (prop2str prop)
  | Hypothesis {name; prop} -> 
      Printf.sprintf "%s : %s" name (prop2str prop)


let env2str (env: envItem list): string =
  let env_str = List.map envItem2str env in
    String.concat "\n" env_str
    |> Printf.sprintf "[\n%s\n]"


let goals2str (f: proof_frame): string =
  match f.goals with
  | [] -> "All Goals Clear.\n"
  | _ ->
    let total = List.length f.goals in
    let goals_str = List.mapi 
      (fun i p -> Printf.sprintf "(%d/%d) %s" (i + 1) total (prop2str p))
      f.goals
    in
    String.concat "\n" goals_str
    |> Printf.sprintf "Goals\n%s\n"

(* The whole information about the frame *)
let frame2str (f: frame): string =
  match f with
  | NormalFrame {env} -> 
      let env_str = env2str env in
        Printf.sprintf "Context: %s" env_str
  | ProofFrame f ->
    let env_str = env2str f.env in
    let proof_mode_str = Printf.sprintf "\n---------------------------------------------------------------\n[Proof Mode] %s : %s\n\n%s" f.proof_name (prop2str f.proof_prop) (goals2str f)
    in
      Printf.sprintf "Context: %s%s" env_str proof_mode_str

let prover2str (p: prover): string =
  let frame = get_frame p in
    (frame2str frame)
    |> Printf.sprintf "%s" 

type eval_result = 
  | Success
  | ProverError of string
  | Pause

type tactic_result =
  | Success of frame
  | TacticError of string

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
    | Assume {x = x; p = prop} ->
        eval_assume p x prop
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
  

and eval_def (p: prover) (name: string) (t: types) (e: terms) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ -> 
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      match find_item frame name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None -> 
        (* Type check here *)
        match calc_type frame e with
        | Type t' when t = t' -> 
            (* Add the new definition to the frame. *)
            p.stack <- (add_envItem normal_f (Definition {name; t; e})) :: p.stack;
            Success
        | Type t' -> 
            ProverError (Printf.sprintf "The variable %s is specified as type %s, but term %s has type %s." name (type2str t) (term2str e) (type2str t'))
        | Proof _ -> ProverError (Printf.sprintf "The term %s is related to a proof." (term2str e))
        | TypeError msg -> 
            ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_def_without_type (p: prover) (name: string) (e: terms) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ -> 
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      match find_item frame name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None -> 
        (* Type check here *)
        match calc_type frame e with
        | Type t ->   
            (* Add the new definition to the frame. *)
            p.stack <- (add_envItem normal_f (Definition {name; t; e})):: p.stack;
            Success
        | Proof _ -> ProverError (Printf.sprintf "The term %s is related to a proof." (term2str e))
        | TypeError msg ->
            ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_var (p: prover) (name: string) (t: types) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ ->
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      match find_item frame name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None ->
          (* Add the new variable to the frame. *)
          p.stack <- (add_envItem normal_f (Assumption {name; t})) :: p.stack;
          Success

and eval_check (p: prover) (e: terms) : eval_result =
  let frame = get_frame p in
    (* Type check here *)
    match calc_type frame e with
    | Type t -> 
      Printf.printf "Check %s: %s.\n" (term2str e) (type2str t);
      Success
    | Proof prop -> 
      Printf.printf "Check %s: %s.\n" (term2str e) (prop2str prop);
      Success
    | TypeError msg -> 
      ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_show (p: prover) (x: string) : eval_result =
  let frame = get_frame p in
    let item = find_item frame x in
      match item with
      | Some (Assumption {name; t}) -> 
          Printf.printf "Show %s : %s.\n" name (type2str t);
          Success
      | Some (Definition {name; t; e}) -> 
          Printf.printf "Show %s := %s : %s.\n" name (term2str e) (type2str t);
          Success
      | Some (Proof {name; prop}) -> 
          Printf.printf "Show %s := <proof> %s.\n" name (prop2str prop);
          Success
      | Some (Hypothesis {name; prop}) ->
          Printf.printf "Show %s : %s.\n" name (prop2str prop);
          Success
      (* | Some _ -> ProverError (Printf.sprintf "Name %s is not defined." x) *)
      | None -> 
          ProverError (Printf.sprintf "Name %s is not defined." x)

and eval_showall (p: prover) : eval_result =
  let frame = get_frame p in
  Printf.printf "ShowAll:\n%s\n" (env2str (get_ctx frame));
  Success
    

and eval_undo (p: prover) : eval_result =
  match p.stack with
  | [] -> ProverError "No frame to undo."
  | _ :: rest -> p.stack <- rest; Success

and eval_assume (p: prover) (x : string) (prop: props) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    match frame with
    | ProofFrame _ -> 
      ProverError "The prover is in proof mode."
    | NormalFrame normal_f ->
      (* check whether the name is already defined *)
      match find_item frame x with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." x)
      | None ->
          (* Type check here *)
          match valid_prop frame prop with
          | Valid -> 
              (* Add the new assumption to the frame. *)
              p.stack <- (add_envItem normal_f (Hypothesis {name = x; prop})) :: p.stack;
              Success
          | Invalid msg -> 
              ProverError (Printf.sprintf "The proposition %s is not valid: %s" (prop2str prop) msg)

and eval_prove (p: prover) (x : string) (prop: props) : eval_result =
  let frame = get_frame p in
  (* check whether it is in proof mode *)
  match frame with
  | ProofFrame _ -> 
    ProverError "The prover is in proof mode."
  | NormalFrame normal_f ->
    (* check whether the name is already defined *)
    match find_item frame x with
    | Some _ -> 
      ProverError (Printf.sprintf "Name %s is already declared." x)
    | None ->
        (* Type check here *)
        match valid_prop frame prop with
        | Valid -> 
            (* Open the proof mode *)
            p.stack <- (open_proof normal_f x prop) :: p.stack;
            Success
        | Invalid msg -> 
            ProverError (Printf.sprintf "The proposition %s is not valid: %s" (prop2str prop) msg)

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
          | R_SKIP -> eval_tac_R_SKIP proof_f
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
      Success new_frame

and eval_tac_R_SKIP (f: proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | hd :: _ ->
      (* Check the application condition *)
      match hd with
      | Judgement {pre; s1; s2; post} when 
        (
          pre = post 
        && s1 = Stmt (SingleCmd Skip)
        && s2 = Stmt (SingleCmd Skip)
          ) ->       
        let new_frame = discharge_first_goal f in
        (* Add the proof to the frame. *)
        Success new_frame
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")
              

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