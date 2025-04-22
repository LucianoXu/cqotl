open Ast

let qreg2str (qs : qreg) : string =
  "[" ^ (String.concat ", " qs) ^ "]"


let rec command_list_2_str (cs: command list) : string =
  let format_command (c: command) : string = 
    command2str c in
  let command_strs = List.map format_command cs in
  String.concat "\n" command_strs

and command2str (c: command) : string =
  match c with
  | Def {x; t; e} -> 
      Printf.sprintf "Def %s : %s := %s." x (type2str t) (term2str e)
      
  | Var {x; t}    -> 
      Printf.sprintf "Var %s : %s." x (type2str t) 
  | Check e      -> 
      Printf.sprintf "Check %s." (term2str e)
  | Show x       ->
      Printf.sprintf "Show %s." x
  | ShowAll      ->
      Printf.sprintf "ShowAll."
  | Undo         ->
      Printf.sprintf "Undo."
  (* | _ -> 
      Printf.sprintf "Command not implemented yet" *)

and type2str (t: types) : string =
  match t with
  | QVar        -> "QVar"
  | QReg n      -> Printf.sprintf "QReg %d" n
  | Opt n       -> Printf.sprintf "Opt %d" n
  | LOpt        -> "LOpt"
  | Assertion   -> "Assertion"
  | Program     -> "Program"
  | Judgement {pre; s1; s2; post} -> 
      Printf.sprintf "{%s} %s ~ %s {%s}" 
        (term2str pre) (term2str s1) (term2str s2) (term2str post)
  (* | _ -> "Unknown type" *)
      

and term2str (e: terms) : string =
  match e with
  | Var v       -> v
  | QRegTerm qs -> qreg2str qs
  | OptTerm o  -> opt2str o
  | LOptTerm lo -> lopt2str lo
  | Assertion lo -> lopt2str lo
  | Stmt s      -> stmt_seq_2_str s
  | Proof       -> "<opaque proof>"
  (* | _ -> "Unknown term" *)

and opt2str (o: opt) : string =
  match o with
  | Add {o1; o2} -> Printf.sprintf "(%s + %s)" (term2str o1) (term2str o2)
  (* | _ -> "Unknown operator" *)

and lopt2str (lo: lopt) : string =
  match lo with
  | Pair {opt; qs} -> Printf.sprintf "%s%s" (term2str opt) (qreg2str qs)
  (* | _ -> "Unknown labeled operator" *)

and stmt_seq_2_str (s: stmt_seq) : string =
    match s with
    | SingleCmd s1               -> stmt2str s1
    | (::) (s1, s2)              -> 
        stmt2str s1 ^ "\n" ^ stmt_seq_2_str s2

and stmt2str (s: stmt) : string =
  match s with
  | Skip                        -> 
      "skip"

  | InitQubit q                 -> 
      Printf.sprintf "%s := |0>" q

  | Unitary {u_opt; qs}       ->
      Printf.sprintf "%s%s" (term2str u_opt) (qreg2str qs)

  | IfMeas {m_opt; s1; s2}  ->
      Printf.sprintf "if %s then %s else %s end" 
        (term2str m_opt) (term2str s1) (term2str s2)
        
  | WhileMeas {m_opt; s}   ->
      Printf.sprintf "while %s do %s end" 
        (term2str m_opt) (term2str s)
  (* | _ -> "Unknown labeled operator" *)