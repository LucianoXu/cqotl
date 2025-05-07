open Ast
open Pretty_printer

type envItem =
  | Assumption of {name: string; t: terms}
  | Definition of {name: string; t: terms; e: terms}

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
  NormalFrame {env = (Definition {name = f.proof_name; t=PropTerm f.proof_prop; e=ProofTerm}) :: f.env}

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
    ) 
  (get_ctx f)

type typing_result =
  | Type of terms
  | TypeError of string



(** Calculate the type of the term. Raise the corresponding error when typing failes. *)
let rec calc_type (f : frame) (s : terms) : typing_result = 
  match s with
  | Var x -> calc_type_var f x

  | Type -> TypeError "Type cannot be typed."

  | Prop -> Type Type

  | QVList -> Type Type

  | OptPair t -> calc_type_OptPair f t

  | CType -> Type Type

  | CVar t -> calc_type_CVar f t

  | QReg t -> calc_type_QReg f t
  
  | Prog -> Type Type

  | CAssn -> Type Type

  | QAssn -> Type Type

  | CQAssn -> Type Type

  | Bit -> Type CType

  | CTerm t -> calc_type_CTerm f t

  | SType -> Type Type

  | OType (t1, t2) -> calc_type_OType f t1 t2

  | DType (t1, t2) -> calc_type_DType f t1 t2


  | Star (t1, t2) -> calc_type_Star f t1 t2

  | At1 t1 -> calc_type_At1 f t1

  | At2 t2 -> calc_type_At2 f t2


  | Pair (t1, t2) -> calc_type_pair f t1 t2

  | AnglePair (t1, t2) -> calc_type_angle_pair f t1 t2


  | QVListTerm ls -> calc_type_qvlist f ls

  | Subscript (e, t1, t2) -> calc_type_subscript f e t1 t2

  | BitTerm b -> calc_type_bitterm f b

  (* | CAssnTerm c -> calc_type_cassn f c *)

  | OptTerm o -> calc_type_opt f o

  | CQAssnTerm cq -> calc_type_cqassn f cq

  | ProgTerm ss ->  calc_type_program f ss
  
  | PropTerm prop -> calc_type_prop f prop

  | ProofTerm -> raise (Failure "<proof> should not be typed")

(* Check whether the term is CTerm[..] *)
and is_CTerm (f: frame) (e: terms) : typing_result =
  let t = calc_type f e in
  match t with
  | Type (CTerm _) -> t
  | Type (CVar a) -> Type (CTerm a)
  | _ ->
    TypeError (Printf.sprintf "The term %s cannot be typed as CTerm[...]." (term2str e))

and is_CAssn (f: frame) (e: terms) : typing_result = 
  let t = calc_type f e in
  match t with
  | Type CAssn -> Type CAssn
  | Type (CTerm Bit) -> Type CAssn
  | _ ->
    TypeError (Printf.sprintf "The term %s cannot be typed as CAssn." (term2str e))
    
and calc_type_var (f : frame) (v : string) : typing_result = 
  match find_item f v with
  | Some (Assumption {t; _}) | Some (Definition {t; _}) -> Type t
  | None -> TypeError (Printf.sprintf "Variable %s is not defined." v)

and calc_type_OptPair f t =
  let type_of_t = calc_type f t in
  match type_of_t with
  | Type CType -> Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_CVar (f : frame) (t : terms) =
  let type_of_t = calc_type f t in
  match type_of_t with
  | Type CType -> 
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_QReg (f : frame) (t : terms) =
  let type_of_t = calc_type f t in
  match type_of_t with
  | Type CType -> 
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_CTerm (f : frame) (t : terms) =
  let type_of_t = calc_type f t in
    match type_of_t with
    | Type CType -> 
      Type Type
    | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_OType (f : frame) t1 t2 =
  let type_of_t1 = calc_type f t1 in
  let type_of_t2 = calc_type f t2 in
  match type_of_t1, type_of_t2 with
  | Type CType, Type CType ->
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (OType (t1, t2))))

and calc_type_DType (f : frame) t1 t2 =
  let type_of_t1 = calc_type f t1 in
  let type_of_t2 = calc_type f t2 in
  match type_of_t1, type_of_t2 with
  | Type QVList, Type QVList ->
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (DType (t1, t2))))

and calc_type_Star (f : frame) t1 t2 =
  let type_of_t1 = calc_type f t1 in
  let type_of_t2 = calc_type f t2 in
  match type_of_t1, type_of_t2 with
  | Type CType, Type CType
    -> Type CType
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Star (t1, t2))))

and calc_type_At1 (f : frame) t =
  let type_of_t = calc_type f (Var t) in
  match type_of_t with
  | Type (QReg _) -> type_of_t
  | Type (CVar _) -> type_of_t
  | _ -> TypeError (Printf.sprintf "Only quantum registers can be annotated by @1")

and calc_type_At2 (f : frame) t =
  let type_of_t = calc_type f (Var t) in
  match type_of_t with
  | Type (QReg _) -> type_of_t
  | Type (CVar _) -> type_of_t
  | _ -> TypeError (Printf.sprintf "Only quantum registers can be annotated by @1")

and calc_type_pair (f : frame) (t1 : terms) (t2 : terms): typing_result = 
  let type_of_t1 = calc_type f t1 in
  let type_of_t2 = calc_type f t2 in
  match type_of_t1, type_of_t2 with
  (* a pair of basis *)
  | Type (CTerm ctype1), Type (CTerm ctype2) ->
    Type (CTerm (Star (ctype1, ctype2)))

  (* a pair of operators *)
  | Type (OType (d1, d2)), Type (OType (d1', d2')) when (d1 = d2 && d2 = d1' && d1' = d2') ->
    Type (OptPair d1)

  (* a pair of qreg *)
  | Type (QReg qregt1), Type (QReg qregt2) ->
    Type (QReg (Star (qregt1, qregt2)))

  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Pair (t1, t2))))

and calc_type_angle_pair (f : frame) (t1 : terms) (t2 : terms): typing_result =
  let type_of_t1 = calc_type f t1 in
  let type_of_t2 = calc_type f t2 in
  match type_of_t1, type_of_t2 with
  (* a pair of operators *)
  | Type (DType _), Type (DType _) ->
    (* check the proofs *)
    if not (prop_proved f (Proj t1)) then
      TypeError (Printf.sprintf "The term %s is not proved to be a projection." (term2str t1))
    else if not (prop_proved f (Pos t2)) then
      TypeError (Printf.sprintf "The term %s is not proved to be a positive operator." (term2str t2))
    else  
      Type QAssn

  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Star (t1, t2))))

and calc_type_qvlist (f : frame) ls =
  (* check whether all elements is typed as QReg *)
  match ls with
  | [] -> Type QVList
  | hd :: tl ->
    (* check whether hd appears in the tl*)
    if List.mem hd tl then
      TypeError (Printf.sprintf "The variable %s appears more than once in the QVList." (term2str hd))
    else
      let type_hd = calc_type f hd in
      match type_hd with
      | Type (QReg _) -> calc_type_qvlist f tl
      | _ -> TypeError (Printf.sprintf "The element %s is not typed as QReg." (term2str hd))

and calc_type_subscript f e t1 t2 =
  let type_of_e = calc_type f e in
  let type_of_t1 = calc_type f t1 in
  let type_of_t2 = calc_type f t2 in
  match type_of_e, type_of_t1, type_of_t2 with
  | Type (OType (ot1, ot2)), Type (QReg rt1), Type (QReg rt2) when
    ot1 = rt1 && ot2 = rt2 ->
      Type (DType (QVListTerm (get_qvlist t1), QVListTerm (get_qvlist t2)))
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Subscript (e, t1, t2))))

and calc_type_bitterm f e =
  match e with
  | True -> Type (CTerm Bit)
  | False -> Type (CTerm Bit)
  | Eq {t1; t2} ->
    let type_of_t1 = is_CTerm f t1 in
    let type_of_t2 = is_CTerm f t2 in
      (match type_of_t1, type_of_t2 with
      | Type (CTerm a), Type (CTerm b) when a = b ->
        Type (CTerm Bit)
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed, because the two sides are not terms of the same classical type." (bitterm2str e))
      )
(* 
and calc_type_cassn f c =
  match c with
  | True -> Type CAssn
  | False -> Type CAssn *)

and calc_type_opt (f : frame) (o : opt) : typing_result = 
  match o with
  | OneO t ->
      let type_of_t = calc_type f t in
      (match type_of_t with
      | Type CType -> Type (OType (t, t))
      | _ -> TypeError (Printf.sprintf "%s should be typed as CType in %s." (term2str t) (opt2str o))
      )
  | ZeroO {t1; t2} ->
      let type_of_t1 = calc_type f t1 in
      let type_of_t2 = calc_type f t2 in
      (match type_of_t1, type_of_t2 with
      | Type CType, Type CType -> Type (OType (t1, t2))
      | _ -> TypeError (Printf.sprintf "%s and %s should be typed as CType in %s." (term2str t1) (term2str t2) (opt2str o))
      )
  | Add {o1; o2} -> 
      let t1 = calc_type f o1 in
      let t2 = calc_type f o2 in
      match t1, t2 with
      | Type (OType (index11, index12)), Type (OType (index21, index22)) when index11 = index21 && index21 = index22 ->
        Type (OType (index11, index12))
      | Type (OType _), Type (OType _) ->
        TypeError (Printf.sprintf "The operator %s and %s do not have the same operator type." (term2str o1) (term2str o2))
      | _ ->
          TypeError (Printf.sprintf "The operator %s is not well typed." (opt2str o))

and calc_type_cqassn f cq =
  match cq with
  | Fiber {psi; p} -> 
    let type_psi = is_CAssn f psi in
    let type_p = calc_type f p in
    (match type_psi, type_p with
    | Type CAssn, Type QAssn -> Type CQAssn
    | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (cqassn2str cq))
    )
  | Add {cq1; cq2} -> 
    let type_cq1 = calc_type f cq1 in 
    let type_cq2 = calc_type f cq2 in
    (match type_cq1, type_cq2 with
    | Type CQAssn, Type CQAssn -> Type CQAssn
    | _ -> TypeError (Printf.sprintf "The two terms %s and %s for +cq should have type CQAssn." (term2str cq1) (term2str cq2))
    )

  
and calc_type_program (f : frame) (s : stmt_seq) : typing_result = 
  match s with
  | SingleCmd cmd -> 
      calc_type_stmt f cmd
  | cmd1 :: cmd2 -> 
      let t1 = calc_type_stmt f cmd1 in
      let t2 = calc_type_program f cmd2 in
        if t1 = Type Prog && t2 = Type Prog then
          Type Prog
        else
          TypeError (Printf.sprintf "The program %s is not well typed." (stmt_seq_2_str s))

and calc_type_stmt (f :frame) (s : stmt) : typing_result = 
  match s with
  | Skip -> 
      Type Prog
  | Assign {x; t} ->
      let type_of_x = calc_type f (Var x) in
        (match type_of_x with
        | Type (CVar a) ->
          (match is_CTerm f t with
          | Type (CTerm b) when a = b -> 
            Type Prog
          | _ -> 
            TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
          )
        | _ -> 
            TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
        )
  | PAssign {x; t} -> 
      let type_of_x = calc_type f (Var x) in
        (match type_of_x with
        | Type (CVar t') when t' = t ->
          Type Prog
        | _ ->
          TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
        )
  | InitQubit t ->
      let type_of_t = calc_type f t in
        (match type_of_t with
        | Type (QReg _) -> Type Prog
        | _ -> 
            TypeError (Printf.sprintf "The term %s does not have quantum register type." (term2str t))
        )
  | Unitary {u_opt; qs} ->
      let type_of_u_opt = calc_type f u_opt in
      let type_of_qs = calc_type f qs in
        (match type_of_u_opt, type_of_qs with
        | Type (OType (t1, t2)), Type (QReg t3) -> 
          (* Check unitary proof *)
          if prop_proved f (Unitary u_opt) then
            if t1 <> t2 then
              TypeError (Printf.sprintf "The operator %s is not an endomorphism" (term2str u_opt))
            else
              if t1 <> t3 then
                TypeError (Printf.sprintf "The operator %s and quantum register %s are not compatible." (term2str u_opt) (term2str qs))
              else
                Type Prog
          else
            TypeError (Printf.sprintf "The operator %s is not proved to be unitary." (term2str u_opt))
        | _ -> 
            TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
        )
  | Meas {x; m_opt; qs} ->
    let type_of_x = calc_type f (Var x) in
    let type_of_m_opt = calc_type f m_opt in
    let type_of_qs = calc_type f qs in
      (match type_of_x, type_of_m_opt, type_of_qs with
      | Type (CVar Bit), Type (OptPair d1), Type (QReg d2) when d1 = d2 -> 
        (* Check measurement proof *)
        if prop_proved f (Meas m_opt) then
          Type Prog
        else
          TypeError (Printf.sprintf "The operator %s is not proved to be a measurement." (term2str m_opt))
      | _ -> 
          TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
      )
  | IfMeas {b; s1; s2} ->
      (match is_CTerm f b with
      | Type (CTerm Bit) ->
        let type_of_s1 = calc_type f s1 in
        let type_of_s2 = calc_type f s2 in
          (match type_of_s1, type_of_s2 with
          | Type Prog, Type Prog -> 
                Type Prog
          | _ -> 
              TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
          )
      | _ -> 
          TypeError (Printf.sprintf "The term %s is not well typed, because %s is not of CTerm[Bit] type." (stmt2str s) (term2str b))
      )

  | WhileMeas {b=b; s=s1} ->
      (match is_CTerm f b with
      | Type (CTerm Bit) -> 
      let type_of_s = calc_type f s1 in
        (match type_of_s with
        | Type Prog -> 
            Type Prog
        | _ -> 
            TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
        )
      | _ -> 
          TypeError (Printf.sprintf "The term %s is not well typed, because %s is not of CTerm[Bit] type." (stmt2str s) (term2str b))
      )
  (* | _ -> raise (Failure "Not implemented yet") *)


(* decide whether the proposition is valid in the context *)
and calc_type_prop (f : frame) (prop: props) : typing_result =
  match prop with
  | Unitary e -> 
      let t = calc_type f e in
      (match t with
      | Type (OType _) -> Type Prop
      | Type _ -> 
          TypeError (Printf.sprintf "The term %s is not of operator type." (term2str e))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str e))
      )
  | Pos lo ->
      let t = calc_type f lo in
      (match t with
      | Type (DType _) -> Type Prop
      | Type _ -> 
          TypeError (Printf.sprintf "The term %s is not of labeled operator type." (term2str lo))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str lo))
      )
  | Proj lo ->
      let t = calc_type f lo in
      (match t with
      | Type (DType _) -> Type Prop
      | Type _ -> 
          TypeError (Printf.sprintf "The term %s is not of labeled operator type." (term2str lo))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str lo))
      )
  | Meas m -> 
      let t = calc_type f m in
      (match t with
      | Type (OptPair _) -> Type Prop
      | Type _ ->
          TypeError (Printf.sprintf "The term %s is not of operator pair type." (term2str m))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str m))
      )
      
  | Judgement {pre; s1; s2; post} -> 
      let t2 = calc_type f s1 in
      let t3 = calc_type f s2 in
      let t_pre = calc_type f pre in
      let t_post = calc_type f post in
        (match t_pre, t2, t3, t_post with
        | Type CQAssn, Type Prog, Type Prog, Type CQAssn -> Type Prop
        | _, TypeError msg, _, _ -> 
          TypeError (Printf.sprintf "The term %s is not well typed: %s" (term2str s1) msg)
        | _, _, TypeError msg, _ ->
          TypeError (Printf.sprintf "The term %s is not well typed: %s" (term2str s2) msg)
        | _ -> TypeError (Printf.sprintf "Invalid judgement: %s." (prop2str prop))
        )

  | Eq {t1; t2} ->
      let t1_type = calc_type f t1 in
      let t2_type = calc_type f t2 in
        (match t1_type, t2_type with
        | Type (OType (t1, t2)), Type (OType (t1', t2')) when t1 = t1' && t2 = t2' -> Type Prop
        | Type (OType _), Type (OType _) -> 
            TypeError (Printf.sprintf "The terms %s and %s are not of the same operator type." (term2str t1) (term2str t2))
        | _ -> 
            TypeError (Printf.sprintf "The terms %s and %s should have operator." (term2str t1) (term2str t2))
        )
  (* | _ -> raise (Failure "Not implemented yet") *)


(* Check whether the proposition is proved in the context by directly search through the proofs and hypotheses *)
and prop_proved (frame : frame) (prop: props) : bool =
  let rec find_item_in_list (ctx: context) prop =
    match ctx with
    | [] -> false
    | hd :: tl -> 
        match hd with
        | Assumption {name = _; t = p} when p = prop -> true
        | Definition {name = _; t = p; e = _} when p = prop -> true
        | _ -> 
            (* Check the rest of the environment *)
            find_item_in_list tl prop
  in find_item_in_list (get_ctx frame) (PropTerm prop)
  

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
      Printf.sprintf "%s : %s" name (term2str t)
  | Definition {name; t; e} -> 
      Printf.sprintf "%s := %s : %s" name (term2str e) (term2str t)


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
            ProverError (Printf.sprintf "The variable %s is specified as type %s, but term %s has type %s." name (term2str t) (term2str e) (term2str t'))
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
      match find_item frame name with
      | Some _ -> 
        ProverError (Printf.sprintf "Name %s is already declared." name)
      | None ->
          (* Type check needed here *)
          (* Add the new variable to the frame. *)
          let type_of_t = calc_type frame t in
          match type_of_t with
          | Type Type | Type Prop -> 
            p.stack <- (add_envItem normal_f (Assumption {name; t})) :: p.stack;
            Success
          | _ -> ProverError (Printf.sprintf "The type %s is not typed as Type, Prop or CType." (term2str t))

and eval_check (p: prover) (e: terms) : eval_result =
  let frame = get_frame p in
    (* check whether it is in proof mode *)
    (* Type check here *)
    match calc_type frame e with
    | Type t -> 
      Printf.printf "Check %s: %s.\n" (term2str e) (term2str t);
      Success
    | TypeError msg -> 
      ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_show (p: prover) (x: string) : eval_result =
  let frame = get_frame p in
    let item = find_item frame x in
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
  Printf.printf "ShowAll:\n%s\n" (env2str (get_ctx frame));
  Success
    

and eval_undo (p: prover) : eval_result =
  match p.stack with
  | [] -> ProverError "No frame to undo."
  | _ :: rest -> p.stack <- rest; Success

and eval_prove (p: prover) (x : string) (prop: terms) : eval_result =
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
      (* check whether prop is proposition *)
      match prop with
      | PropTerm prop ->
        (* Type check here *)
        (match calc_type_prop frame prop with
        | Type Prop -> 
            (* Open the proof mode *)
            p.stack <- (open_proof normal_f x prop) :: p.stack;
            Success
        | Type _ ->
            ProverError (Printf.sprintf "The term %s is not typed as a proposition." (prop2str prop))
        | TypeError msg -> 
            ProverError (Printf.sprintf "The proposition %s is not valid: %s" (prop2str prop) msg)
        )
      | _ -> ProverError (Printf.sprintf "Only propositions can be proved.")

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
        && s1 = ProgTerm (SingleCmd Skip)
        && s2 = ProgTerm (SingleCmd Skip)
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