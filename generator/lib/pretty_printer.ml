open Ast
(* 
let rec command_list_2_str (cs: command list) : string =
  let format_command (c: command) : string = 
    command2str c in
  let command_strs = List.map format_command cs in
  String.concat "\n" command_strs


  and term2str (e: terms) : string =
    match e with
    | Var x -> 
        Printf.sprintf "%s" x
    | Forall {x; t; t'} ->
        Printf.sprintf "forall (%s : %s), %s" x (term2str t) (term2str t')
    | Fun {x; t; e} ->
        Printf.sprintf "fun (%s : %s) => %s" x (term2str t) (term2str e)
    | Apply (f, t) ->
        Printf.sprintf "(%s %s)" (term2str f) (term2str t)
    | Type ->
        Printf.sprintf "Type"
    | Prop ->
        Printf.sprintf "Prop"
    | QVList ->
        Printf.sprintf "QVList"
    | OptPair t ->
        Printf.sprintf "OptPair[%s]" (term2str t)
    | ProofTerm ->
        Printf.sprintf "<proof>"
    | CType ->
        Printf.sprintf "CType"
    | CVar t ->
        Printf.sprintf "CVar[%s]" (term2str t)
    | QReg qs ->
        Printf.sprintf "QReg[%s]" (term2str qs)
    | Prog -> 
        Printf.sprintf "Prog"
    | CAssn ->
        Printf.sprintf "CAssn"
    | QAssn ->
        Printf.sprintf "QAssn"
    | CQAssn ->
        Printf.sprintf "CQAssn"

    | Bit ->
        Printf.sprintf "Bit"

    | CTerm t ->
        Printf.sprintf "CTerm[%s]" (term2str t)
    | SType ->
        Printf.sprintf "SType"
    | OType (t1, t2) ->
        Printf.sprintf "OType[%s, %s]" (term2str t1) (term2str t2)
    | DType (t1, t2) ->
        Printf.sprintf "DType[%s, %s]" (term2str t1) (term2str t2)

    | Star (t1, t2) ->
        Printf.sprintf "(%s * %s)" (term2str t1) (term2str t2)
    | At1 v ->
        Printf.sprintf "%s@1" v
    | At2 v ->
        Printf.sprintf "%s@2" v

    | Pair (t1, t2) ->
        Printf.sprintf "(%s, %s)" (term2str t1) (term2str t2)
    | AnglePair (t1, t2) ->
        Printf.sprintf "<%s, %s>" (term2str t1) (term2str t2)


    | QVListTerm tls ->
        qvlistterm2str tls

    | Subscript (t1, t2, t3) ->
        Printf.sprintf "%s_%s,%s" (term2str t1) (term2str t2) (term2str t3)

    | BitTerm b -> (bitterm2str b)

    (* | CAssnTerm c -> (cassn2str c) *)

    | OptTerm o -> (opt2str o)

    | CQAssnTerm cq -> (cqassn2str cq)

    | ProgTerm s -> (stmt_seq_2_str s)

    | PropTerm p -> (prop2str p)
    
    (* | _ -> 
        Printf.sprintf "<Term not implemented yet>" *)

and qvlistterm2str (tls : terms list) : string =
    List.map term2str tls |> String.concat ", " |> Printf.sprintf "[%s]"
    

and prop2str (p: props) : string =
  match p with
  | Unitary e -> 
      Printf.sprintf "Unitary %s" (term2str e)
  | Pos e ->
      Printf.sprintf "Pos %s" (term2str e)
  | Proj e ->
      Printf.sprintf "Proj %s" (term2str e)
  | Meas e ->
      Printf.sprintf "Meas %s" (term2str e)
  | Judgement {pre; s1; s2; post} -> 
    Printf.sprintf "\n{%s}\n%s\n ~ \n%s\n{%s}" 
      (term2str pre) (term2str s1) (term2str s2) (term2str post)
  | Eq {t1; t2} ->
      Printf.sprintf "%s = %s" (term2str t1) (term2str t2)
  | Leq {t1; t2} ->
      Printf.sprintf "%s <= %s" (term2str t1) (term2str t2)
  (* | _ -> "Unknown proposition" *)

and bitterm2str (b: bitterm) : string =
  match b with
  | True -> 
      Printf.sprintf "true"
  | False -> 
      Printf.sprintf "false"
  | Eq {t1; t2} -> 
      Printf.sprintf "%s == %s" (term2str t1) (term2str t2)
  (* | _ -> "Unknown bit term" *)
(* 
and cassn2str (c: cassn) : string =
  match c with
    | _ -> raise (Failure "Unknown assertion")
    | _ -> "Unknown assertion" *)

and opt2str (o: opt) : string =
  match o with
  | OneO t -> Printf.sprintf "1O[%s]" (term2str t)
  | ZeroO {t1; t2} -> Printf.sprintf "0O[%s, %s]" (term2str t1) (term2str t2)
  | Add {o1; o2} -> Printf.sprintf "(%s + %s)" (term2str o1) (term2str o2)
  (* | _ -> "Unknown operator" *)

and cqassn2str (c: cqassn) : string =
  match c with
  | Fiber {psi; p} -> 
      Printf.sprintf "(%s |-> %s)" (term2str psi) (term2str p)
  | Add {cq1; cq2} -> 
      Printf.sprintf "(%s +cq %s)" (term2str cq1) (term2str cq2)
  | UApply {u; cq} ->
      Printf.sprintf "(%s @ %s)" (term2str u) (term2str cq)
  (* | _ -> "Unknown assertion" *) 

   *)



let rec command_list_2_str (cs: command list) : string =
  let format_command (c: command) : string = 
    command2str c in
  let command_strs = List.map format_command cs in
  String.concat "\n" command_strs

and command2str (c: command) : string =
  match c with
  | Def {x; t; e} -> 
      Printf.sprintf "Def %s : %s := %s." x (term2str t) (term2str e)
  | DefWithoutType {x; e} -> 
      Printf.sprintf "Def %s := %s." x (term2str e)
  | Var {x; t}    -> 
      Printf.sprintf "Var %s : %s." x (term2str t) 
  | Check e      -> 
      Printf.sprintf "Check %s." (term2str e)
  | Show x       ->
      Printf.sprintf "Show %s." x
  | ShowAll      ->
      Printf.sprintf "ShowAll."
  | Undo         ->
      Printf.sprintf "Undo."
  | Pause       ->
      Printf.sprintf "Pause."
  | Prove {x; p}  ->
      Printf.sprintf "Prove %s : %s." x (term2str p)
  | Tactic t      ->
      (tactic2str t)
  | QED -> "QED."

and tactic2str (t: tactic) : string =
  match t with
  | Sorry -> "sorry."
  | Choose i -> Printf.sprintf "choose %d." i
  | ByLean -> "by_lean."

  (* | R_SKIP -> "r_skip."
  | SEQ_FRONT t -> Printf.sprintf "seq_front %s." (term2str t)
  | SEQ_BACK t -> Printf.sprintf "seq_back %s." (term2str t)
  | R_UNITARY1 -> "r_unitary1." *)
  (* | _ -> "Unknown tactic" *)

and term2str (e: terms) : string =
    match e with
    | Fun {head; args=[Symbol x; t; t']} when head = _forall->
        Printf.sprintf "(forall (%s : %s), %s)" x (term2str t) (term2str t')
    | Fun {head; args=[Symbol x; t; e]} when head = _fun->
        Printf.sprintf "(fun (%s : %s) => %s)" x (term2str t) (term2str e)
    | Fun {head; args=[f; t]} when head = _apply->
        Printf.sprintf "(%s @ %s)" (term2str f) (term2str t)


    (* dirac notation *)
    | Fun {head; args=[t1; t2]} when head = _plus ->
        Printf.sprintf "(%s + %s)" (term2str t1) (term2str t2)

    | Fun {head; args=[t1; t2]} when head = _eq ->
        Printf.sprintf "(%s = %s)" (term2str t1) (term2str t2)


    (* program statements *)
    | Symbol x when x = _skip ->
        "skip"
  
    | Fun {head; args=[Symbol x; t]} when head = _assign ->
        Printf.sprintf "%s := %s" x (term2str t)

    | Fun {head; args=[Symbol x; t]} when head = _passign ->
        Printf.sprintf "%s <-$ %s" x (term2str t)

    | Fun {head; args=[q]} when head = _init_qubit ->
        Printf.sprintf "init %s" (term2str q)
        
    | Fun {head; args=[u_opt; qs]} when head = _unitary ->
        Printf.sprintf "unitary %s %s" (term2str u_opt) (term2str qs)
    
    | Fun {head; args=[Symbol x; m_opt; qs]} when head = _meas ->
        Printf.sprintf "%s := meas %s %s" x (term2str m_opt) (term2str qs)

    | Fun {head; args=[b; s1; s2]} when head = _if ->
        Printf.sprintf "if %s then %s else %s end" 
          (term2str b) (term2str s1) (term2str s2)
  
    | Fun {head; args=[b; s]} when head = _while ->
        Printf.sprintf "while %s do %s end" 
          (term2str b) (term2str s)

    | Fun {head; args} when head = _seq ->
        let args_str = List.map term2str args |> String.concat ";\n" in
        Printf.sprintf "%s;\n" args_str


    | Symbol x -> 
        Printf.sprintf "%s" x

    | Fun {head; args} ->
        let args_str = List.map term2str args |> String.concat ", " in
        Printf.sprintf "%s[%s]" head args_str

    | Opaque ->
        Printf.sprintf "<opaque>"