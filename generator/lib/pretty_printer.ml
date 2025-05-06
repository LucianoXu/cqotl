open Ast

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
  (* | _ -> 
      Printf.sprintf "Command not implemented yet" *)

and tactic2str (t: tactic) : string =
  match t with
  | Sorry -> "sorry."
  | R_SKIP -> "r_skip."
  (* | _ -> "Unknown tactic" *)

  and term2str (e: terms) : string =
    match e with
    | Var x -> 
        Printf.sprintf "%s" x
    | Type ->
        Printf.sprintf "Type"
    | Prop ->
        Printf.sprintf "Prop"
    | QVList ->
        Printf.sprintf "QVList"
    | OptPair ->
        Printf.sprintf "OptPair"
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

    | Pair (t1, t2) ->
        Printf.sprintf "(%s, %s)" (term2str t1) (term2str t2)
    | AnglePair (t1, t2) ->
        Printf.sprintf "<%s, %s>" (term2str t1) (term2str t2)


    | QVListTerm tls ->
        qvlistterm2str tls

    | Subscript (t1, t2, t3) ->
        Printf.sprintf "%s_%s,%s" (term2str t1) (term2str t2) (term2str t3)

    | CAssnTerm c -> (cassn2str c)

    | OptTerm o -> (opt2str o)

    | CQAssnTerm cq -> (cqassn2str cq)

    | ProgTerm s -> (stmt_seq_2_str s)

    | PropTerm p -> (prop2str p)
    
    (* | _ -> 
        Printf.sprintf "<Term not implemented yet>" *)

and qvlistterm2str (tls : string list) : string =
    tls |> String.concat ", " |> Printf.sprintf "[%s]"
    

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
    Printf.sprintf "{%s} %s ~ %s {%s}" 
      (term2str pre) (term2str s1) (term2str s2) (term2str post)
  | Eq {t1; t2} ->
      Printf.sprintf "%s = %s" (term2str t1) (term2str t2)
  (* | _ -> "Unknown proposition" *)

and cassn2str (c: cassn) : string =
  match c with
    | True -> 
        Printf.sprintf "True"
    | False -> 
        Printf.sprintf "False"
    (* | _ -> "Unknown assertion" *)

and opt2str (o: opt) : string =
  match o with
  | Add {o1; o2} -> Printf.sprintf "(%s + %s)" (term2str o1) (term2str o2)
  (* | _ -> "Unknown operator" *)

and cqassn2str (c: cqassn) : string =
  match c with
  | Fiber {psi; p} -> 
      Printf.sprintf "(%s |-> %s)" (term2str psi) (term2str p)
  | Add {cq1; cq2} -> 
      Printf.sprintf "(%s +cq %s)" (term2str cq1) (term2str cq2)
  (* | _ -> "Unknown assertion" *) 

and stmt_seq_2_str (s: stmt_seq) : string =
    match s with
    | SingleCmd s1               -> stmt2str s1
    | (::) (s1, s2)              -> 
        stmt2str s1 ^ "\n" ^ stmt_seq_2_str s2

and stmt2str (s: stmt) : string =
  match s with
  | Skip                        -> 
      "skip"

  | Assign {x; t}               ->
    Printf.sprintf "%s := %s" x (term2str t)

  | PAssign {x; t}              ->
    Printf.sprintf "%s <-$ %s" x (term2str t)

  | InitQubit q                 -> 
      Printf.sprintf "init %s" (term2str q)

  | Unitary {u_opt; qs}       ->
      Printf.sprintf "unitary %s%s" (term2str u_opt) (term2str qs)

  | Meas {x; m_opt}             ->
      Printf.sprintf "%s := meas %s" x (term2str m_opt)

  | IfMeas {b; s1; s2}  ->
      Printf.sprintf "if %s then %s else %s end" 
        (term2str b) (term2str s1) (term2str s2)
        
  | WhileMeas {b; s}   ->
      Printf.sprintf "while %s do %s end" 
        (term2str b) (term2str s)
  (* | _ -> "Unknown labeled operator" *)