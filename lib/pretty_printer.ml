open Ast

let format_qreg (qs : qreg) : string =
  String.concat ", " qs

let rec pretty_print_stmt (s: stmt) : string =
  match s with
  | Skip                        -> "skip"
  | Seq (s1, s2)                -> 
      pretty_print_stmt s1 ^ ";\n" ^ pretty_print_stmt s2
  | InitQubit q                 -> 
      Printf.sprintf "%s := |0>" q
  | ApplyUnitary (op, qs)       ->
      Printf.sprintf "%s[%s]" op (format_qreg qs)
  | IfMeas (m_op, q, branches)  ->
      let format_branch (outcome, st)  =
        Printf.sprintf "%d -> %s" outcome (pretty_print_stmt st)  in
      let branch_strs   = List.map format_branch branches         in
      let branches_str  = String.concat " | " branch_strs         in
      Printf.sprintf "if %s[%s] = (%s) fi" m_op q branches_str
  | WhileMeas (m_op, q, body)   ->
      let body_str      = pretty_print_stmt body                                          in
      let indented_body = " " ^ String.concat "\n " (String.split_on_char '\n' body_str)  in
      Printf.sprintf "while %s[%s] = 1 do\n%s\nod" m_op q indented_body
