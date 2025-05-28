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
open Utils



(* QVList Calculation *)
type termls_result =
  | TermList of terms list
  | TermError of string

(** the function to calculate the qvlist from the qreg term *)
let rec get_qvlist (qreg : terms) : termls_result =
  match qreg with
  | Symbol _ -> TermList [qreg]
  | Fun {head; args=[t1; t2]} when head=_pair ->
    let t1_list = get_qvlist t1 in
    let t2_list = get_qvlist t2 in
    (
      match t1_list, t2_list with
      | TermList l1, TermList l2 -> TermList (l1 @ l2)
      | TermError msg, _ -> TermError msg
      | _, TermError msg -> TermError msg
    )
  | _ -> TermError "Cannot calculate the quantum variable list for the given term."



type envItem =
  | Assumption of {name: string; t: terms}
  | Definition of {name: string; t: terms; e: terms}

(* The well-formed environment and context *)
type wf_ctx = {
  env: envItem list; 
  ctx: envItem list
}

(* return a fresh name for the context *)
let fresh_name_for_ctx (ctx: wf_ctx) (prefix : string): string =
  (* Helper function to get all symbols in an environment list *)
  let get_symbols_from_env (env: envItem list) : string list =
    List.map (function
      | Assumption {name; _} -> name
      | Definition {name; _} -> name
    ) env
  in
  
  (* Get all symbols from both ctx and env *)
  let all_symbols = get_symbols_from_env ctx.ctx @ get_symbols_from_env ctx.env in
  fresh_name all_symbols prefix

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
            let sym = fresh_name_for_term type_e x in
            Type (Fun {head=_forall; args=[Symbol sym; t; substitute type_e x (Symbol sym)]})
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str e) msg)
        end
      | TypeError _ ->
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t))
    end
    
  (* apply *)
  | Fun {head; args=[t1; t2]} when head = _apply ->
    begin
      match calc_type wfctx t1 with
      (* function application *)
      | Type (Fun {head; args=[Symbol x; forall_t; forall_t']}) when head = _forall ->
        begin
          match type_check wfctx t2 forall_t with
          | Type _ ->
            Type (substitute forall_t' x t2)
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as a valid argument. %s" (term2str s) (term2str t2) msg)
        end
      (* scalar multiplication *)
      | Type (Symbol sym) when sym = _stype ->
        begin
          match calc_type wfctx t2 with
          | Type (Symbol sym) when sym = _stype -> Type (Symbol _stype)
          | Type (Fun {head; args=[t]}) when head = _ktype ->
            Type (Fun {head=_ktype; args=[t]})
          | Type (Fun {head; args=[t]}) when head = _btype ->
            Type (Fun {head=_btype; args=[t]})
          | Type (Fun {head; args=[t1; t2]}) when head = _otype ->
            Type (Fun {head=_otype; args=[t1; t2]})
          | _ -> TypeError (Printf.sprintf "%s typing failed for scalar multiplication." (term2str s))
        end
      | Type (Fun {head; args=[t]}) when head = _btype ->
        begin
          match calc_type wfctx t2 with
          (* inner product *)
          | Type (Fun {head; args=[t']}) when head = _ktype ->
            if t = t' then
              Type (Symbol _stype)
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not bra and ket of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          (* bra-opt mult *)
          | Type (Fun {head; args=[t1'; t2']}) when head = _otype ->
            if t = t1' then
              Type (Fun {head=_btype; args=[t2']})
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not bra and operator of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | Type (Fun {head; args=[t]}) when head = _ktype ->
        begin
          match calc_type wfctx t2 with
          (* outer product *)
          | Type (Fun {head; args=[t']}) when head = _btype ->
            Type (Fun {head=_otype; args=[t; t']})
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | Type (Fun {head; args=[u; v]}) when head = _otype ->
        begin
          match calc_type wfctx t2 with
          (* opt-ket mult *)
          | Type (Fun {head; args=[v']}) when head = _ktype ->
            if v = v' then
              Type (Fun {head=_ktype; args=[u]})
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not operator and ket of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          | Type (Fun {head; args=[u'; v']}) when head = _otype ->
            if v = u' then
              Type (Fun {head=_otype; args=[u; v']})
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not operator and operator of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      (* labelled dirac notation multiplication *)
      | Type (Fun {head; args=[Fun{args=s1; _}; Fun{args=s1'; _}]}) when head = _dtype ->
        begin
          match calc_type wfctx t2 with
          | Type (Fun {head; args=[Fun{args=s2; _}; Fun{args=s2'; _}]}) when head = _dtype -> 
            let s2_sub_s1' = list_remove s2 s1' in
            let s1'_sub_s2 = list_remove s1' s2 in
            if list_disjoint s1 s2_sub_s1' && list_disjoint s2' s1'_sub_s2 then
              Type (Fun 
              {head=_dtype; 
              args=[
                Fun {head=_list; args=s1 @ s2_sub_s1'}; 
                Fun {head=_list; args=s2' @ s1'_sub_s2}
              ];
            })
            else
              TypeError (Printf.sprintf "%s typing failed. quantum vairbale lists are not disjoint." (term2str s))

          | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as DType." (term2str s) (term2str t2))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
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

  (* Set *)
  | Fun {head; args=[t]} when head = _set ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* bit *)
  | Symbol sym when sym = _bit ->
    Type (Symbol _ctype)
  

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

  (* KType *)
  | Fun {head; args=[t]} when head = _ktype ->
    begin
      match calc_type wfctx t with 
      | Type type_t when type_t = Symbol _ctype -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end

  (* BType *)
  | Fun {head; args=[t]} when head = _btype ->
    begin
      match calc_type wfctx t with 
      | Type type_t when type_t = Symbol _ctype -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end

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

  (* ProgStt *)
  | Symbol sym when sym = _progstt -> Type (Symbol _type)

  (* Prog *)
  | Symbol sym when sym = _prog -> Type (Symbol _type)

  (* CQProj *)
  | Symbol sym when sym = _cqproj -> Type (Symbol _type)


  (* Assn *)
  | Symbol sym when sym = _assn -> Type (Symbol _type)


  (*** typing for program statements ***)
  (* seq *)
  | Fun {head; args} when head = _seq ->
    (* Check whether all arguments are typed as prog *)
    let rec check_args args =
      match args with
      | [] -> TypeError "Empty program sequence is not allowed."
      | [prog] -> 
        begin
          match calc_type wfctx prog with
          | Type (Symbol sym) when sym = _progstt -> Type (Symbol _prog)
          | Type _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt." (term2str s) (term2str prog))
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt. %s" (term2str s) (term2str prog) msg)
        end
      | prog :: rest ->
        begin
          match calc_type wfctx prog with
          | Type (Symbol sym) when sym = _progstt -> check_args rest
          | Type _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt." (term2str s) (term2str prog))
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt. %s" (term2str s) (term2str prog) msg)
        end
      in
      check_args args

  (* Skip *)
  | Symbol sym when sym = _skip -> Type (Symbol _progstt)

  (* Assign *)
  | Fun {head; args=[Symbol x; t]} when head = _assign ->
    begin
      match calc_type wfctx (Symbol x) with
      | Type (Fun {head=_cvar; args=[a]}) ->
        begin
          match is_cterm wfctx t with
          | Type type_t when type_t = (Fun {head=_cterm; args=[a]}) -> Type (Symbol _progstt)
          | Type _ -> 
            TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type." (term2str s) x (term2str t))
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type. %s" (term2str s) x (term2str t) msg)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CVar." (term2str s) x)
    end

  (* PAssign *)
  | Fun {head; args=[Symbol x; t]} when head = _passign ->
    begin
      match type_check wfctx (Symbol x) (Fun {head=_cvar; args=[t]}) with
      | Type _ -> Type (Symbol _progstt)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s cannot be typed as CVar[%s]. %s" (term2str s) x (term2str t) msg)
    end

  (* Init Qubit *)
  | Fun {head; args=[qs]} when head = _init_qubit ->
    begin
      match calc_type wfctx qs with
      | Type (Fun {head=_qreg; args=[_]}) -> Type (Symbol _progstt)
      | Type tt -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s instead of QReg." (term2str s) (term2str qs) (term2str tt))
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as QReg. %s" (term2str s) (term2str qs) msg)
    end

  (* Unitary *)
  | Fun {head; args=[u; qs]} when head = _unitary ->
    begin
      match calc_type wfctx u, calc_type wfctx qs with
      | Type (Fun {head=head1; args=[t1; t1']}), Type (Fun {head=head2; args=[t2]}) when 
      (
        head1 = _otype &&
        head2 = _qreg &&
        t1 = t1' && t1 = t2
      ) ->
        Type (Symbol _progstt)
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* measure *)
  | Fun {head; args=[Symbol x; m_opt; qs]} when head = _meas ->
    begin
      match calc_type wfctx (Symbol x), calc_type wfctx m_opt, calc_type wfctx qs with
      | Type type1, Type type2, Type type3->
        begin
        match type1, type2, type3 with
        | Fun {head=head1; args=[t1]}, Fun {head=head2; args=[t2]}, Fun {head=head3; args=[t3]} when 
          (
            head1 = _cvar && t1 = Symbol _bit &&
            head2 = _optpair && 
            head3 = _qreg &&
            t2 = t3
          ) ->
          Type (Symbol _progstt)

        | Fun {head=head1; args}, _, _ when head1 = _cvar && args <> [Symbol _bit] ->
          TypeError (Printf.sprintf "%s typing failed. %s is typed as %s, instead of CVAR[BIT]." (term2str s) x (term2str (Fun {head=_cvar; args})))
        | _ -> 
          TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end 
      | _ ->
        TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* if *)
  | Fun {head; args=[b; s1; s2]} when head = _if ->
    begin
      match is_cterm wfctx b, calc_type wfctx s1, calc_type wfctx s2 with
      | Type type1, Type type2, Type type3 when type1 = Fun {head=_cterm; args=[Symbol _bit]} && type2 = Symbol _prog && type3 = Symbol _prog ->
        Type (Symbol _progstt)

      | Type (Fun {head; args}), _, _ when head = _cterm && args <> [Symbol _bit] -> 
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit]." (term2str s) (term2str b))

      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* while *)
  | Fun {head; args=[b; s']} when head = _while ->
    begin
      match is_cterm wfctx b, calc_type wfctx s' with
      | Type type1, Type type2 when type1 = Fun {head=_cterm; args=[Symbol _bit]} && type2 = Symbol _prog ->
        Type (Symbol _progstt)
      | Type (Fun {head; _}), _ when head = _cterm -> 
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit]." (term2str s) (term2str b))
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end


  (* pair *)
  | Fun {head; args=[t1; t2]} when head = _pair ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      (* operator pair *)
      | Type (Fun {head=head1; args=[tt1; tt2]}), Type (Fun {head=head2; args=[tt1'; tt2']}) when head1 = _otype && head2 = _otype && tt1 = tt2 && tt1' = tt2' && tt1 = tt1'->
        Type (Fun {head=_optpair; args=[tt1]})

      | Type (Fun {head=head1; _}), Type (Fun {head=head2; _}) when head1 = _otype && head2 = _otype ->
        TypeError (Printf.sprintf "%s typing failed. %s and %s are not square operators of the same type." (term2str s) (term2str t1) (term2str t2))

      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as OType." (term2str s) (term2str t1) (term2str t2))
    end

  (* list of qreg *)
  | Fun {head; args} when head = _pair ->
    let symbols = get_qvlist s in
    begin
      match symbols with 
      (* check whether calculate qvlist can work *)
      | TermError msg -> TypeError (Printf.sprintf "%s typing failed. %s" (term2str s) msg)
      | TermList symbols ->
        (* check whether all qreg are unique *)
        if not (all_unique symbols) then
          TypeError (Printf.sprintf "%s typing failed. It contains duplicate quantum variables." (term2str s))
        else
          let rec aux args =
            begin
            match args with
            | [] -> Type (Symbol _qvlist)
            | hd :: tl ->
              match calc_type wfctx hd with
              | Type (Fun {head; _}) when head = _qreg ->
                aux tl
              | _ -> TypeError (Printf.sprintf "%s cannot be typd as QReg." (term2str hd))
            end
          in aux args
    end


  (**************************************)
  (* Dirac Notation *)
  (* ket *)
  | Fun {head; args=[t]} when head = _ket ->
    begin
      match is_cterm wfctx t with
      | Type (Fun {head=head; args=[t]}) when head=_cterm ->
          Type (Fun {head=_ktype; args=[t]})
      | Type t' -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s, instead of CTerm[_]." (term2str s) (term2str t) (term2str t'))
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t) msg)
    end

  (* bra *)
  | Fun {head; args=[t]} when head = _bra ->
      begin
        match is_cterm wfctx t with
        | Type (Fun {head=head; args=[t]}) when head=_cterm ->
            Type (Fun {head=_btype; args=[t]})
        | Type t' -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s, instead of CTerm[_]." (term2str s) (term2str t) (term2str t'))
        | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t) msg)
      end

  (* adj *)
  | Fun {head; args=[t]} when head = _adj ->
    begin
      match calc_type wfctx t with
      | Type (Symbol sym) when sym = _stype ->
        Type (Symbol _stype)
      | Type (Fun {head=head; args=[t]}) when head=_ktype ->
        Type (Fun {head=_btype; args=[t]})
      | Type (Fun {head=head; args=[t]}) when head=_btype ->
        Type (Fun {head=_ktype; args=[t]})
      | Type (Fun {head=head; args=[t1; t2]}) when head=_otype ->
        Type (Fun {head=_otype; args=[t2; t1]})
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* zeroo *)
  | Fun {head; args=[t1; t2]} when head = _zeroo ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type (Symbol sym1), Type (Symbol sym2) when sym1 = _ctype && sym2 = _ctype ->
        Type (Fun {head=_otype; args=[t1; t2]})
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as CType." (term2str s) (term2str t1) (term2str t2))
    end

  (* oneo *)
  | Fun {head; args=[t]} when head = _oneo ->
    begin
      match calc_type wfctx t with
      | Type (Symbol sym1) when sym1 = _ctype ->
        Type (Fun {head=_otype; args=[t; t]})
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
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

  (* sum *)
  | Fun {head; args=[s'; f]} when head = _sum ->
    begin
      match calc_type wfctx f with
      | Type (Fun {head=head; args=[Symbol v; t; t']}) when head = _forall ->
        begin
          (* Check the set and input type*)
          match calc_type wfctx s', t with
          | Type (Fun {head=head1; args=[t1]}), Fun {head=head2; args=[t2]} when head1 = _set &&  head2 = _cterm && t1 = t2 ->
          begin
            (* check the type of the function *)
            match t' with
            | Symbol sym when sym = _stype -> 
                Type t'
            | Fun {head; _} when head = _ktype || head = _btype || head = _otype ->
                Type t'
            | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not a function to SType, KType, BType or OType." (term2str s) (term2str f))
          end
          | _ -> TypeError (Printf.sprintf "%s typing failed. set %s and index %s have inconsistent types." (term2str s) (term2str s') v)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s must be typed as a function." (term2str s) (term2str f))
    end

  (* uset *)
  | Fun {head; args=[t]} when head = _uset ->
    begin
      match calc_type wfctx t with
      | Type (Symbol sym) when sym = _ctype ->
        Type (Fun {head=_set; args=[t]})
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end

  
  (* subscript, opt pair*)
  | Fun {head; args=[t1; Fun {head=pair_head; args=[s1; s2]}]} when head = _subscript && pair_head = _pair->
    begin
      match calc_type wfctx t1, calc_type wfctx s1, calc_type wfctx s2 with
      | Type (Fun {head=head1; args=[tt1; tt2]}), 
        Type (Fun {head=head2; args=[tqreg1]}),
        Type (Fun {head=head3; args=[tqreg2]}) when
        (
          head1 = _otype &&
          head2 = _qreg &&
          head3 = _qreg &&
          tt1 = tqreg1 && tt2 = tqreg2
        ) ->
        begin
          match get_qvlist s1, get_qvlist s2 with
          | TermList qv1, TermList qv2 ->
            Type (Fun {head=_dtype; args=[
              Fun {head=_list; args=qv1};
              Fun {head=_list; args=qv2}
            ]})
          | _ -> TypeError (Printf.sprintf "%s typing failed. Cannot calculate quantum variable list of %s or %s." (term2str s) (term2str s1) (term2str s2))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end



  (* true *)
  | Symbol sym when sym = _true -> Type (Fun {head=_cterm; args=[Symbol _bit]})

  (* false *)
  | Symbol sym when sym = _false -> Type (Fun {head=_cterm; args=[Symbol _bit]})

  (* eqeq *)
  | Fun {head; args=[t1; t2]} when head = _eqeq ->
    begin
      match is_cterm wfctx t1 with
      | Type type_t1 ->
        begin
          match type_t1 with
          | Fun {head=head; args=[Symbol _]} when head = _cterm ->
            begin
              match is_cterm wfctx t2 with
              | Type type_t2 when type_t1 = type_t2 -> Type (Fun {head=_cterm; args=[Symbol _bit]})
              | Type _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type." (term2str s) (term2str t1) (term2str t2))
              | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type. %s" (term2str s) (term2str t1) (term2str t2) msg)
            end
          | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm." (term2str s) (term2str t1))
        end
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t1) msg)
    end

  (* wedge *)
  | Fun {head; args=[t1; t2]} when head = _wedge ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          (* type conjunction *)
          | _ when type_t1 = Symbol _type && type_t2 = Symbol _type ->
            Type (Symbol _type)
          (* boolean conjunction *)
          | _ when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 ->
              Type (Fun {head=_cterm; args=[Symbol _bit]})
          (* cq-projector conjunction *)
          | _ when type_t1 = Symbol _cqproj && type_t2 = Symbol _cqproj ->
              Type (Symbol _cqproj) 
          | _ ->
              TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end
      
  (* vee *)
  | Fun {head; args=[t1; t2]} when head = _vee ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          if type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 then
            Type (Fun {head=_cterm; args=[Symbol _bit]})
          else
            TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end

  (* not *)
  | Fun {head; args=[t]} when head = _not ->
    begin
      match calc_type wfctx t with
      | Type type_t ->
        begin
          if type_t = Fun {head=_cterm; args=[Symbol _bit]} then
            Type (Fun {head=_cterm; args=[Symbol _bit]})
          else
            TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit]." (term2str s) (term2str t))
        end
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t) msg)
    end
  
  (* imply *)
  | Fun {head; args=[t1; t2]} when head = _imply ->
      begin
        match calc_type wfctx t1, calc_type wfctx t2 with
        | Type type_t1, Type type_t2 ->
          begin
            match type_t1, type_t2 with
            (* boolean implication *)
            | _ when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 ->
                Type (Fun {head=_cterm; args=[Symbol _bit]})
            (* Sasaki implication *)
            | Fun {head=head1; args=[tt1; tt2]}, Fun {head=head2; args=[tt1'; tt2']} when head1 = _otype && head2 = _otype && tt1=tt2 && tt1'=tt2' && tt1=tt1' ->
                Type (Fun {head=_otype; args=[tt1; tt1]})
            (* cq-projector *)
            | _, Fun {head=head2; _} when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && head2=_dtype ->
                Type (Symbol _cqproj)
            | _ ->
                TypeError (Printf.sprintf "%s typing failed." (term2str s))
          end
        | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
      end

  (* guarded quantum operator *)
  | Fun {head; args=[t1; t2]} when head = _guarded ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          | _, Fun {head=head2; _} when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && head2 = _dtype ->
            Type type_t2
          | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit] or %s is not typed as DType." (term2str s) (term2str t1) (term2str t2))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end

  (* vbar (cq-assertion) *)
  | Fun {head; args=[t1; t2]} when head = _vbar ->
    (* (psi, A) pair of assn *)
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type Fun {head=head2; _} when 
        type_t1 = Symbol _cqproj && head2 = _dtype ->
          Type (Symbol _assn)
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
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

  (* Entailment *)
  | Fun {head; args=[t1; t2]} when head = _entailment -> 
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          (* cq-projector entailment *)
          | _ when type_t1 = Symbol _cqproj && type_t2 = Symbol _cqproj -> Type (Symbol _type)

          (* assertion entailment *)
          | _ when type_t1 = Symbol _assn && type_t2 = Symbol _assn ->
            Type (Symbol _type)

          (* operator entailment *)
          | Fun {head=head1; _}, Fun {head=head2; _} when head1=_dtype && head2=_dtype ->
            Type (Symbol _type)
          | _ -> 
            TypeError (Printf.sprintf "%s typing failed. Entailment should between two assertions." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* Judgement *)
  | Fun {head; args=[pre; s1; s2; post]} when head = _judgement ->
    begin
      match calc_type wfctx pre, calc_type wfctx s1, calc_type wfctx s2, calc_type wfctx post with
      | Type type_pre, Type type_s1, Type type_s2, Type type_post ->
        if type_pre = Symbol _assn && type_s1 = Symbol _prog && type_s2 = Symbol _prog && type_post = Symbol _assn then
          Type (Symbol _type)
        else
          TypeError (Printf.sprintf "%s typing failed." (term2str s))
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
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
  (* the same type *)
  | Type t' when t = t' -> Type t


  | Type t' -> 
      TypeError (Printf.sprintf "The term %s is not typed as %s, but %s." (term2str s) (term2str t) (term2str t'))
  | TypeError msg -> TypeError msg
  

and is_cterm (wfctx : wf_ctx) (s : terms) : typing_result =
  let calc_type_res = calc_type wfctx s in
  match calc_type_res with
  | Type (Fun {head; args=[t']}) when head = _cterm -> Type (Fun {head=_cterm; args=[t']})

  (* cvar is cterm *)
  | Type (Fun {head; args=[t']}) when head = _cvar -> Type (Fun {head=_cterm; args=[t']})

  | Type t' -> 
      TypeError (Printf.sprintf "The term %s is not typed as CTerm, but %s." (term2str s) (term2str t'))
  | TypeError msg -> TypeError msg
  
