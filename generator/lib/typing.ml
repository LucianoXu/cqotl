(* open Ast
open Pretty_printer
open Utils

type envItem =
  | Assumption of {name: string; t: terms}
  | Definition of {name: string; t: terms; e: terms}

(* The well-formed environment and context *)
type wf_ctx = {
  env: envItem list; 
  ctx: envItem list
}

(** Create a well-formed context with empty context. *)
let env2wfctx env = {env=env; ctx=[]}


(** Find the item in the well-formed context. *)
let find_item (wfctx: wf_ctx) (name: string) : envItem option =
  let find_item_single (env: envItem list) (name: string) : envItem option =
    List.find_opt (
      function
        | Assumption {name = n; _} -> n = name
        | Definition {name = n; _} -> n = name
      ) 
    (env) 
  in
  let ctx_res = find_item_single wfctx.ctx name in
  match ctx_res with
  | Some _ -> ctx_res
  | None ->
    let env_res = find_item_single wfctx.env name in
    match env_res with
    | Some _ -> env_res
    | None -> None



type normal_frame = {
  env: envItem list;
}

type proof_frame = {
  env: envItem list;
  proof_name: string;
  proof_prop: props;
  goals: props list;
}

(* The frame of the prover. *)
type frame = 
  | NormalFrame of normal_frame
  | ProofFrame of proof_frame

(** Get the environment from the frame. *)
let get_frame_env (f: frame) : envItem list =
  match f with
  | NormalFrame {env} -> env
  | ProofFrame {env; _} -> env

let add_envItem (f: normal_frame) (item: envItem) : frame =
  NormalFrame {env = item::f.env}



(* QVList Calculation *)
type termls_result =
  | TermList of terms list
  | TermError of string

(** the function to calculate the qvlist from the qreg term *)
let rec get_qvlist (qreg : terms) : termls_result =
  match qreg with
  | Var _ | At1 _ | At2 _ -> TermList [qreg]
  | Pair (t1, t2) -> 
    let t1_list = get_qvlist t1 in
    let t2_list = get_qvlist t2 in
    (
      match t1_list, t2_list with
      | TermList l1, TermList l2 -> TermList (l1 @ l2)
      | TermError msg, _ -> TermError msg
      | _, TermError msg -> TermError msg
    )
  | _ -> TermError "Cannot calculate the quantum variable list for the given term."



type typing_result =
  | Type of terms
  | TypeError of string

(** Calculate the type of the term. Raise the corresponding error when typing failes. *)
let rec calc_type (wfctx : wf_ctx) (s : terms) : typing_result = 
  match s with
  | Var x -> calc_type_var wfctx x

  | Forall {x; t; t'} -> calc_type_forall wfctx x t t'

  | Fun {x; t; e} -> calc_type_fun wfctx x t e

  | Apply (f, t) -> calc_type_apply wfctx f t

  | Type -> TypeError "Type cannot be typed."

  | Prop -> Type Type

  | QVList -> Type Type

  | OptPair t -> calc_type_OptPair wfctx t

  | CType -> Type Type

  | CVar t -> calc_type_CVar wfctx t

  | QReg t -> calc_type_QReg wfctx t
  
  | Prog -> Type Type

  | CAssn -> Type Type

  | QAssn -> Type Type

  | CQAssn -> Type Type

  | Bit -> Type CType

  | CTerm t -> calc_type_CTerm wfctx t

  | SType -> Type Type

  | OType (t1, t2) -> calc_type_OType wfctx t1 t2

  | DType (t1, t2) -> calc_type_DType wfctx t1 t2


  | Star (t1, t2) -> calc_type_Star wfctx t1 t2

  | At1 t1 -> calc_type_At1 wfctx t1

  | At2 t2 -> calc_type_At2 wfctx t2


  | Pair (t1, t2) -> calc_type_pair wfctx t1 t2

  | AnglePair (t1, t2) -> calc_type_angle_pair wfctx t1 t2


  | QVListTerm ls -> calc_type_qvlist wfctx ls

  | Subscript (e, t1, t2) -> calc_type_subscript wfctx e t1 t2

  | BitTerm b -> calc_type_bitterm wfctx b

  (* | CAssnTerm c -> calc_type_cassn f c *)

  | OptTerm o -> calc_type_opt wfctx o

  | CQAssnTerm cq -> calc_type_cqassn wfctx cq

  | ProgTerm ss ->  calc_type_program wfctx ss
  
  | PropTerm prop -> calc_type_prop wfctx prop

  | ProofTerm -> raise (Failure "<proof> should not be typed")


(** annotate the variables in the term and return the result *)
and annotate_var (wfctx: wf_ctx) (t: terms) (g: string -> terms) : terms option =
  match t with
  | Var x ->
    let type_of_t = calc_type wfctx (Var x) in
    begin
      match type_of_t with
      | Type (CVar _) | Type (QReg _) -> Some (g x)
      | _ -> None
    end
  | Pair (t1, t2) -> 
    let t1' = annotate_var wfctx t1 g in
    let t2' = annotate_var wfctx t2 g in
    begin
      match t1', t2' with
      | Some t1'', Some t2'' -> Some (Pair (t1'', t2''))
      | _ -> None
    end
  | _ -> None

(* Check whether the term is CTerm[..] *)
and is_CTerm (wfctx: wf_ctx) (e: terms) : typing_result =
  let t = calc_type wfctx e in
  match t with
  | Type (CTerm _) -> t
  | Type (CVar a) -> Type (CTerm a)
  | _ ->
    TypeError (Printf.sprintf "The term %s cannot be typed as CTerm[...]." (term2str e))

and is_CAssn (wfctx: wf_ctx) (e: terms) : typing_result = 
  let t = calc_type wfctx e in
  match t with
  | Type CAssn -> Type CAssn
  | Type (CTerm Bit) -> Type CAssn
  | _ ->
    TypeError (Printf.sprintf "The term %s cannot be typed as CAssn." (term2str e))
    
and calc_type_var (wfctx : wf_ctx) (v : string) : typing_result = 
  match find_item wfctx v with
  | Some (Assumption {t; _}) | Some (Definition {t; _}) -> Type t
  | None -> TypeError (Printf.sprintf "Variable %s is not defined." v)

and calc_type_forall (wfctx : wf_ctx) (x : string) (t : terms) (t' : terms) =
  let type_of_t = calc_type wfctx t in
  match type_of_t with
  | Type Type -> 
    begin
      let new_envs : wf_ctx = {
        env=wfctx.env; 
        ctx=Assumption {name = x; t = t} :: wfctx.ctx
      } in
      let type_of_t' = calc_type new_envs t' in
      match type_of_t' with
      | Type Type -> Type Type
      | _ -> TypeError (Printf.sprintf "The term %s is typed as Type." (term2str t'))
    end
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as Type." (term2str t))

and calc_type_fun (wfctx : wf_ctx) (x : string) (t : terms) (e : terms) =
  let type_of_t = calc_type wfctx t in
  match type_of_t with
  | Type Type -> 
    begin
      let new_envs : wf_ctx = {
        env=wfctx.env; 
        ctx=Assumption {name = x; t = t} :: wfctx.ctx
      } in
      let type_of_e = calc_type new_envs e in
      match type_of_e with
      | Type t_e -> Type (Forall ({x; t; t' = t_e}))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str e))
    end
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str t))

and calc_type_apply wfctx f t =
  let type_of_f = calc_type wfctx f in
  match type_of_f with
  | Type (Forall {x; t=t_forall; t'=t_forall'}) ->
    begin
      match calc_type wfctx t with
      | Type type_of_t when type_of_t = t_forall ->
        Type t_forall'
      | _ -> TypeError (Printf.sprintf "The function argument %s is not typed as %s." (term2str t) (term2str t_forall))
    end
      
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as forall." (term2str t))


and calc_type_OptPair wfctx t =
  let type_of_t = calc_type wfctx t in
  match type_of_t with
  | Type CType -> Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_CVar (wfctx : wf_ctx) (t : terms) =
  let type_of_t = calc_type wfctx t in
  match type_of_t with
  | Type CType -> 
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_QReg (wfctx : wf_ctx) (t : terms) =
  let type_of_t = calc_type wfctx t in
  match type_of_t with
  | Type CType -> 
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_CTerm (wfctx : wf_ctx) (t : terms) =
  let type_of_t = calc_type wfctx t in
    match type_of_t with
    | Type CType -> 
      Type Type
    | _ -> TypeError (Printf.sprintf "The term %s is not typed as CType." (term2str t))

and calc_type_OType (wfctx : wf_ctx) t1 t2 =
  let type_of_t1 = calc_type wfctx t1 in
  let type_of_t2 = calc_type wfctx t2 in
  match type_of_t1, type_of_t2 with
  | Type CType, Type CType ->
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (OType (t1, t2))))

and calc_type_DType (wfctx : wf_ctx) t1 t2 =
  let type_of_t1 = calc_type wfctx t1 in
  let type_of_t2 = calc_type wfctx t2 in
  match type_of_t1, type_of_t2 with
  | Type QVList, Type QVList ->
    Type Type
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (DType (t1, t2))))

and calc_type_Star (wfctx : wf_ctx) t1 t2 =
  let type_of_t1 = calc_type wfctx t1 in
  let type_of_t2 = calc_type wfctx t2 in
  match type_of_t1, type_of_t2 with
  | Type CType, Type CType
    -> Type CType
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Star (t1, t2))))

and calc_type_At1 (wfctx : wf_ctx) t =
  let type_of_t = calc_type wfctx (Var t) in
  match type_of_t with
  | Type (QReg _) -> type_of_t
  | Type (CVar _) -> type_of_t
  | _ -> TypeError (Printf.sprintf "Only quantum registers can be annotated by @1")

and calc_type_At2 (wfctx : wf_ctx) t =
  let type_of_t = calc_type wfctx (Var t) in
  match type_of_t with
  | Type (QReg _) -> type_of_t
  | Type (CVar _) -> type_of_t
  | _ -> TypeError (Printf.sprintf "Only quantum registers can be annotated by @1")

and calc_type_pair (wfctx : wf_ctx) (t1 : terms) (t2 : terms): typing_result = 
  let type_of_t1 = calc_type wfctx t1 in
  let type_of_t2 = calc_type wfctx t2 in
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

and calc_type_angle_pair (wfctx : wf_ctx) (t1 : terms) (t2 : terms): typing_result =
  let type_of_t1 = calc_type wfctx t1 in
  let type_of_t2 = calc_type wfctx t2 in
  match type_of_t1, type_of_t2 with
  (* a pair of operators *)
  | Type (DType _), Type (DType _) ->
    (* check the proofs *)
    if not (prop_proved wfctx (Proj t1)) then
      TypeError (Printf.sprintf "The term %s is not proved to be a projection." (term2str t1))
    else if not (prop_proved wfctx (Pos t2)) then
      TypeError (Printf.sprintf "The term %s is not proved to be a positive operator." (term2str t2))
    else  
      Type QAssn

  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Star (t1, t2))))

and calc_type_qvlist (wfctx : wf_ctx) ls =
  (* check whether all elements is typed as QReg *)
  match ls with
  | [] -> Type QVList
  | hd :: tl ->
    (* check whether hd appears in the tl*)
    if List.mem hd tl then
      TypeError (Printf.sprintf "The variable %s appears more than once in the QVList." (term2str hd))
    else
      let type_hd = calc_type wfctx hd in
      match type_hd with
      | Type (QReg _) -> calc_type_qvlist wfctx tl
      | _ -> TypeError (Printf.sprintf "The element %s is not typed as QReg." (term2str hd))

and calc_type_subscript wfctx e t1 t2 =
  let type_of_e = calc_type wfctx e in
  let type_of_t1 = calc_type wfctx t1 in
  let type_of_t2 = calc_type wfctx t2 in
  match type_of_e, type_of_t1, type_of_t2 with
  | Type (OType (ot1, ot2)), Type (QReg rt1), Type (QReg rt2) when
    ot1 = rt1 && ot2 = rt2 ->
      let qvlist1 = get_qvlist t1 in
      let qvlist2 = get_qvlist t2 in
      (match qvlist1, qvlist2 with
      | TermList ls1, TermList ls2 -> 
        Type (DType (QVListTerm ls1, QVListTerm ls2))
      | _ -> 
        TypeError (Printf.sprintf "Calculation of quantum variable list failed.")
      )
  | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str (Subscript (e, t1, t2))))

and calc_type_bitterm wfctx e =
  match e with
  | True -> Type (CTerm Bit)
  | False -> Type (CTerm Bit)
  | Eq {t1; t2} ->
    let type_of_t1 = is_CTerm wfctx t1 in
    let type_of_t2 = is_CTerm wfctx t2 in
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

and calc_type_opt (wfctx : wf_ctx) (o : opt) : typing_result = 
  match o with
  | OneO t ->
      let type_of_t = calc_type wfctx t in
      (match type_of_t with
      | Type CType -> Type (OType (t, t))
      | _ -> TypeError (Printf.sprintf "%s should be typed as CType in %s." (term2str t) (opt2str o))
      )
  | ZeroO {t1; t2} ->
      let type_of_t1 = calc_type wfctx t1 in
      let type_of_t2 = calc_type wfctx t2 in
      (match type_of_t1, type_of_t2 with
      | Type CType, Type CType -> Type (OType (t1, t2))
      | _ -> TypeError (Printf.sprintf "%s and %s should be typed as CType in %s." (term2str t1) (term2str t2) (opt2str o))
      )
  | Add {o1; o2} -> 
      let t1 = calc_type wfctx o1 in
      let t2 = calc_type wfctx o2 in
      match t1, t2 with
      | Type (OType (index11, index12)), Type (OType (index21, index22)) when index11 = index21 && index21 = index22 ->
        Type (OType (index11, index12))
      | Type (OType _), Type (OType _) ->
        TypeError (Printf.sprintf "The operator %s and %s do not have the same operator type." (term2str o1) (term2str o2))
      | _ ->
          TypeError (Printf.sprintf "The operator %s is not well typed." (opt2str o))

and calc_type_cqassn wfctx cq =
  match cq with
  | Fiber {psi; p} -> 
    let type_psi = is_CAssn wfctx psi in
    let type_p = calc_type wfctx p in
    (match type_psi, type_p with
    | Type CAssn, Type QAssn -> Type CQAssn
    | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (cqassn2str cq))
    )
  | Add {cq1; cq2} -> 
    let type_cq1 = calc_type wfctx cq1 in 
    let type_cq2 = calc_type wfctx cq2 in
    (match type_cq1, type_cq2 with
    | Type CQAssn, Type CQAssn -> Type CQAssn
    | _ -> TypeError (Printf.sprintf "The two terms %s and %s for +cq should have type CQAssn." (term2str cq1) (term2str cq2))
    )
  | UApply {u; cq=cq'} ->
    let type_u = calc_type wfctx u in
    let type_cq' = calc_type wfctx cq' in
    (match type_u, type_cq' with
    | Type (DType _), Type CQAssn -> 
      (* check the proof *)
      if prop_proved wfctx (Unitary u) then
        Type CQAssn
      else
        TypeError (Printf.sprintf "The term %s is not proved to be a unitary operator." (term2str u))
    | _ -> 
      TypeError (Printf.sprintf "The term %s is not well typed." (cqassn2str cq))
    )

  
and calc_type_program (wfctx : wf_ctx) (s : stmt_seq) : typing_result = 
  match s with
  | SingleCmd cmd -> 
      calc_type_stmt wfctx cmd
  | cmd1 :: cmd2 -> 
      let t1 = calc_type_stmt wfctx cmd1 in
      let t2 = calc_type_program wfctx cmd2 in
        if t1 = Type Prog && t2 = Type Prog then
          Type Prog
        else
          TypeError (Printf.sprintf "The program %s is not well typed." (stmt_seq_2_str s))

and calc_type_stmt (wfctx :wf_ctx) (s : stmt) : typing_result = 
  match s with
  | Skip -> 
      Type Prog
  | Assign {x; t} ->
      let type_of_x = calc_type wfctx (Var x) in
        (match type_of_x with
        | Type (CVar a) ->
          (match is_CTerm wfctx t with
          | Type (CTerm b) when a = b -> 
            Type Prog
          | _ -> 
            TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
          )
        | _ -> 
            TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
        )
  | PAssign {x; t} -> 
      let type_of_x = calc_type wfctx (Var x) in
        (match type_of_x with
        | Type (CVar t') when t' = t ->
          Type Prog
        | _ ->
          TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
        )
  | InitQubit t ->
      let type_of_t = calc_type wfctx t in
        (match type_of_t with
        | Type (QReg _) -> Type Prog
        | _ -> 
            TypeError (Printf.sprintf "The term %s does not have quantum register type." (term2str t))
        )
  | Unitary {u_opt; qs} ->
      let type_of_u_opt = calc_type wfctx u_opt in
      let type_of_qs = calc_type wfctx qs in
        (match type_of_u_opt, type_of_qs with
        | Type (OType (t1, t2)), Type (QReg t3) -> 
          (* Check unitary proof *)
          if prop_proved wfctx (Unitary u_opt) then
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
    let type_of_x = calc_type wfctx (Var x) in
    let type_of_m_opt = calc_type wfctx m_opt in
    let type_of_qs = calc_type wfctx qs in
      (match type_of_x, type_of_m_opt, type_of_qs with
      | Type (CVar Bit), Type (OptPair d1), Type (QReg d2) when d1 = d2 -> 
        (* Check measurement proof *)
        if prop_proved wfctx (Meas m_opt) then
          Type Prog
        else
          TypeError (Printf.sprintf "The operator %s is not proved to be a measurement." (term2str m_opt))
      | _ -> 
          TypeError (Printf.sprintf "The term %s is not well typed." (stmt2str s))
      )
  | IfMeas {b; s1; s2} ->
      (match is_CTerm wfctx b with
      | Type (CTerm Bit) ->
        let type_of_s1 = calc_type wfctx s1 in
        let type_of_s2 = calc_type wfctx s2 in
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
      (match is_CTerm wfctx b with
      | Type (CTerm Bit) -> 
      let type_of_s = calc_type wfctx s1 in
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
and calc_type_prop (wfctx : wf_ctx) (prop: props) : typing_result =
  match prop with
  | Unitary e -> 
      let t = calc_type wfctx e in
      (match t with
      | Type (OType _) -> Type Prop
      | Type (DType _) -> Type Prop
      | Type _ -> 
          TypeError (Printf.sprintf "The term %s is not of operator type." (term2str e))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str e))
      )
  | Pos lo ->
      let t = calc_type wfctx lo in
      (match t with
      | Type (DType _) -> Type Prop
      | Type _ -> 
          TypeError (Printf.sprintf "The term %s is not of labeled operator type." (term2str lo))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str lo))
      )
  | Proj lo ->
      let t = calc_type wfctx lo in
      (match t with
      | Type (DType _) -> Type Prop
      | Type _ -> 
          TypeError (Printf.sprintf "The term %s is not of labeled operator type." (term2str lo))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str lo))
      )
  | Meas m -> 
      let t = calc_type wfctx m in
      (match t with
      | Type (OptPair _) -> Type Prop
      | Type _ ->
          TypeError (Printf.sprintf "The term %s is not of operator pair type." (term2str m))
      | _ -> TypeError (Printf.sprintf "The term %s is not well typed." (term2str m))
      )
      
  | Judgement {pre; s1; s2; post} -> 
      let t2 = calc_type wfctx s1 in
      let t3 = calc_type wfctx s2 in
      let t_pre = calc_type wfctx pre in
      let t_post = calc_type wfctx post in
        (match t_pre, t2, t3, t_post with
        | Type CQAssn, Type Prog, Type Prog, Type CQAssn -> Type Prop
        | _, TypeError msg, _, _ -> 
          TypeError (Printf.sprintf "The term %s is not well typed: %s" (term2str s1) msg)
        | _, _, TypeError msg, _ ->
          TypeError (Printf.sprintf "The term %s is not well typed: %s" (term2str s2) msg)
        | _ -> TypeError (Printf.sprintf "Invalid judgement: %s." (prop2str prop))
        )

  | Eq {t1; t2} ->
      let t1_type = calc_type wfctx t1 in
      let t2_type = calc_type wfctx t2 in
        (match t1_type, t2_type with
        | Type (OType (t1, t2)), Type (OType (t1', t2')) when t1 = t1' && t2 = t2' -> Type Prop
        | Type (OType _), Type (OType _) -> 
            TypeError (Printf.sprintf "The terms %s and %s are not of the same operator type." (term2str t1) (term2str t2))
        | _ -> 
            TypeError (Printf.sprintf "The terms %s and %s should have operator." (term2str t1) (term2str t2))
        )
  | Leq {t1; t2} ->
      let t1_type = calc_type wfctx t1 in
      let t2_type = calc_type wfctx t2 in
        (match t1_type, t2_type with
        | Type CQAssn, Type CQAssn -> Type Prop
        | _ -> 
            TypeError (Printf.sprintf "The terms %s and %s should have CQAssn type." (term2str t1) (term2str t2))
        )
  (* | _ -> raise (Failure "Not implemented yet") *)


(* Check whether the proposition is proved in the context by directly search through the proofs and hypotheses *)
and prop_proved (wfctx : wf_ctx) (prop: props) : bool =
  let rec find_item_in_list (ctx: envItem list) prop =
    match ctx with
    | [] -> false
    | hd :: tl -> 
        match hd with
        | Assumption {name = _; t = p} when p = prop -> true
        | Definition {name = _; t = p; e = _} when p = prop -> true
        | _ -> 
            (* Check the rest of the environment *)
            find_item_in_list tl prop
  in 
  let ctx_res = find_item_in_list wfctx.ctx (PropTerm prop) in
  match ctx_res with
  | true -> true
  | false -> 
    (* Check the rest of the environment *)
    let env_res = find_item_in_list wfctx.env (PropTerm prop) in
      match env_res with
      | true -> true
      | false -> false
  

(* The empty frame. *)
let empty_frame : frame = 
  NormalFrame {env = []}

(* Check whether a variable is defined in the frame. *)
let is_defined (wfctx: wf_ctx) (name: string) : bool =
  find_item wfctx name <> None


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




let prover2str (p: prover): string =
  let frame = get_frame p in
    (frame2str frame)
    |> Printf.sprintf "%s" 


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
        Success (ProofFrame new_frame)
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")
              
and eval_tac_SEQ_FRONT (f: proof_frame) (t: terms): tactic_result =
  (* Check the application condition *)
  let wfctx : wf_ctx = {env=f.env; ctx=[]} in
  let type_of_t = calc_type wfctx t in
  if type_of_t <> Type CQAssn then
    TacticError (Printf.sprintf "The term %s is not typed as CQAssn." (term2str t))

  else match f.goals with
  | [] -> TacticError "Nothing to prove."
  | hd :: _ ->
      (* Check the application condition *)
      match hd with
      | Judgement {pre=pre; s1 = ProgTerm s1; s2 = ProgTerm s2; post=post} ->
        let s1_front, s1_remain = get_front_stmt s1 in
        let s2_front, s2_reamin = get_front_stmt s2 in
        let removed_frame = discharge_first_goal f in
        let new_goal_1 = 
          Judgement {pre; s1 = ProgTerm (SingleCmd s1_front); s2 = ProgTerm (SingleCmd s2_front); post = t} in
        let new_goal_2 = 
          Judgement {pre = t; s1 = ProgTerm s1_remain; s2 = ProgTerm s2_reamin; post} in
        let new_frame =  add_goal (add_goal removed_frame new_goal_2) new_goal_1 in
        Success (ProofFrame new_frame)

      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")


and eval_tac_SEQ_BACK (f: proof_frame) (t: terms): tactic_result =
  (* Check the application condition *)
  let wfctx : wf_ctx = {env=f.env; ctx=[]} in
  let type_of_t = calc_type wfctx t in
  if type_of_t <> Type CQAssn then
    TacticError (Printf.sprintf "The term %s is not typed as CQAssn." (term2str t))

  else match f.goals with
  | [] -> TacticError "Nothing to prove."
  | hd :: _ ->
      (* Check the application condition *)
      match hd with
      | Judgement {pre=pre; s1 = ProgTerm s1; s2 = ProgTerm s2; post=post} ->
        let s1_back, s1_remain = get_back_stmt s1 in
        let s2_back, s2_reamin = get_back_stmt s2 in
        let removed_frame = discharge_first_goal f in
        let new_goal_1 = 
          Judgement {pre = t; s1 = ProgTerm (SingleCmd s1_back); s2 = ProgTerm (SingleCmd s2_back); post} in
        let new_goal_2 = 
          Judgement {pre; s1 = ProgTerm s1_remain; s2 = ProgTerm s2_reamin; post=t} in
        let new_frame =  add_goal (add_goal removed_frame new_goal_2) new_goal_1 in
        Success (ProofFrame new_frame)

      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")

and eval_tac_R_UNITARY1 (f : proof_frame) : tactic_result =
  match f.goals with
  | [] -> TacticError "Nothing to prove."
  | hd :: _ ->
      (* Check the application condition *)
      let wfctx : wf_ctx = {env=f.env; ctx=[]} in
      (match hd with
      | Judgement {pre=pre; s1 = ProgTerm s1; s2 = ProgTerm s2; post=post} ->
        let s1_front, s1_remain = get_front_stmt s1 in
        (match s1_front with
        | Unitary {u_opt; qs} ->
          let annotated_qs = annotate_var wfctx qs (fun v -> At1 v) in
          begin
            match annotated_qs with
            | Some qs' ->
            let new_goal = Judgement{
              pre=pre; 
              s1=ProgTerm s1_remain; 
              s2=ProgTerm s2; 
              post=CQAssnTerm (UApply {u = Subscript (u_opt, qs', qs'); cq = post})} in
            let removed_frame = discharge_first_goal f in
            let new_frame = add_goal removed_frame new_goal in
            Success (ProofFrame new_frame)
            | None -> 
              TacticError (Printf.sprintf "Cannot annotate the variable %s." (term2str qs))
          end
          | _ -> TacticError (Printf.sprintf "The first statment for  program 1 should be unitary transformation, but is %s." (stmt2str s1_front))
        )
      | _ -> TacticError (Printf.sprintf "The tactic is not applicable to the current goal")
  )



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
      | Pause -> Pause *)



open Ast
open Pretty_printer
(* open Utils *)

type envItem =
  | Assumption of {name: string; t: terms}
  | Definition of {name: string; t: terms; e: terms}

(* The well-formed environment and context *)
type wf_ctx = {
  env: envItem list; 
  ctx: envItem list
}

(** Create a well-formed context from an environment with empty context. *)
let env2wfctx env = {env=env; ctx=[]}


(** Find the item in the well-formed context. *)
let find_item (wfctx: wf_ctx) (name: string) : envItem option =
  let find_item_single (env: envItem list) (name: string) : envItem option =
    List.find_opt (
      function
        | Assumption {name = n; _} -> n = name
        | Definition {name = n; _} -> n = name
      ) 
    (env) 
  in
  let ctx_res = find_item_single wfctx.ctx name in
  match ctx_res with
  | Some _ -> ctx_res
  | None ->
    let env_res = find_item_single wfctx.env name in
    match env_res with
    | Some _ -> env_res
    | None -> None


type typing_result =
  | Type of terms
  | TypeError of string

(** Calculate the type of the term. Raise the corresponding error when typing failes. *)
let rec calc_type (wfctx : wf_ctx) (s : terms) : typing_result = 
  match s with

  (* Type *)
  | Symbol sym when sym = _type -> 
    Type (Symbol _type)

  (* forall *)
  | Fun {head; args=[Symbol x; t; t']} when head = _forall ->
    begin
      match type_check wfctx t (Symbol _type) with
      | Type _ -> 
        begin
          let new_wfctx = {wfctx with ctx = Assumption {name = x; t = t} :: wfctx.ctx} in
          match type_check new_wfctx t' (Symbol _type) with
          | Type _ -> Type (Symbol _type)
          | TypeError _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t'))
        end
      | TypeError _ ->
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t))
    end
  
  (* function *)
  | Fun {head; args=[Symbol x; t; e]} when head = _fun ->
    begin
      match type_check wfctx t (Symbol _type) with
      | Type _ ->
        begin
          let new_wfctx = {wfctx with ctx = Assumption {name = x; t = t} :: wfctx.ctx} in
          match calc_type new_wfctx e with
          | Type type_e -> 
            let sym = fresh_name type_e x in
            Type (Fun {head=_forall; args=[Symbol sym; t; subst type_e x (Symbol sym)]})
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str e) msg)
        end
      | TypeError _ ->
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t))
    end
    
  (* apply *)
  | Fun {head; args=[f; t]} when head = _apply ->
    begin
      match calc_type wfctx f with
      | Type (Fun {head; args=[Symbol x; forall_t; forall_t']}) when head = _forall ->
        begin
          match type_check wfctx t forall_t with
          | Type _ ->
            Type (subst forall_t' x t)
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as a valid argument. %s" (term2str s) (term2str t) msg)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as forall." (term2str s) (term2str f))
    end

  (* CType *)
  | Symbol sym when sym = _ctype ->
    Type (Symbol _type)

  (* CVar *)
  | Fun {head; args=[t]} when head = _cvar ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* CTerm *)
  | Fun {head; args=[t]} when head = _cterm ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* QVList *)
  | Symbol sym when sym = _qvlist ->
    Type (Symbol _type)

  (* OptPair *)
  | Fun {head; args=[t]} when head = _optpair ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* QReg *)
  | Fun {head; args=[t]} when head = _qreg ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* SType *)
  | Symbol sym when sym = _stype ->
    Type (Symbol _type)

  (* OType *)
  | Fun {head; args=[t1; t2]} when head = _otype ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 when 
        type_t1 = Symbol _ctype && type_t2 = Symbol _ctype -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as CType." (term2str s) (term2str t1) (term2str t2))
    end

  (* DType *)
  | Fun {head; args=[r1; r2]} when head = _dtype ->
    begin
      match calc_type wfctx r1, calc_type wfctx r2 with
      | Type type_r1, Type type_r2 when 
        type_r1 = Symbol _qvlist && type_r2 = Symbol _qvlist -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as QVList." (term2str s) (term2str r1) (term2str r2))
    end

  (* Prog *)
  | Symbol sym when sym = _prog -> Type (Symbol _type)


  (* Assn *)
  | Symbol sym when sym = _assn -> Type (Symbol _type)


  (*** typing for program statements ***)
  (* Skip *)
  | Symbol sym when sym = _skip -> Type (Symbol _prog)

  (* Assign *)
  | Fun {head; args=[Symbol x; t]} when head = _assign ->
    begin
      match calc_type wfctx (Symbol x) with
      | Type (Fun {head=_cvar; args=[a]}) ->
        begin
          match type_check wfctx t (Fun {head=_cterm; args=[a]}) with
          | Type _ -> Type (Symbol _prog)
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type. %s" (term2str s) x (term2str t) msg)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CVar." (term2str s) x)
    end

  (* PAssign *)
  | Fun {head; args=[Symbol x; t]} when head = _passign ->
    begin
      match type_check wfctx (Symbol x) (Fun {head=_cvar; args=[t]}) with
      | Type _ -> Type (Symbol _prog)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s cannot be typed as CVar[%s]. %s" (term2str s) x (term2str t) msg)
    end

  (* Init Qubit *)
  | Fun {head; args=[qs]} when head = _init_qubit ->
    begin
      match calc_type wfctx qs with
      | Type (Fun {head=_qreg; args=[_]}) -> Type (Symbol _prog)
      | Type tt -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s instead of QReg." (term2str s) (term2str qs) (term2str tt))
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as QReg. %s" (term2str s) (term2str qs) msg)
    end

  
  (* plus *)
  | Fun {head; args=[t1; t2]} when head = _plus ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          | Fun {head=head1; _}, _ when head1 = _otype && type_t1 = type_t2 ->
            Type type_t1
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as QVList." (term2str s) (term2str t1) (term2str t2))
    end


  (* Eq *)
  | Fun {head; args=[t1; t2]} when head = _eq ->
    begin
      match calc_type wfctx t1 with
      | Type type_t1 ->
        begin
          match type_check wfctx t2 type_t1 with
          | Type _ -> Type (Symbol _type)
          | TypeError _ -> TypeError (Printf.sprintf "%s typing failed. Two sides don't have the same type." (term2str s))
        end
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t1) msg)
    end
  
  (* Variable *)
  | Symbol x ->
    begin
      match find_item wfctx x with
      | Some (Assumption {name=_; t}) -> Type t
      | Some (Definition {name=_; t; e=_}) -> Type t
      | None -> TypeError (Printf.sprintf "The term %s is not defined or assumed." x)
    end

  (* default *)
  | _ -> TypeError (Printf.sprintf "Cannot calculate type of %s." (term2str s))

    


and type_check (wfctx : wf_ctx) (s : terms) (t : terms) : typing_result = 
  let calc_type_res = calc_type wfctx s in
  match calc_type_res with
  | Type t' when t = t' -> Type t
  | Type t' -> 
      TypeError (Printf.sprintf "The term %s is not typed as %s, but %s." (term2str s) (term2str t) (term2str t'))
  | TypeError msg -> TypeError msg
  
