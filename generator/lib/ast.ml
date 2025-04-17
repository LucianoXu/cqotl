
type var                  = string
type qreg                 = var list
type unitary_op           = string  (* e.g. "H" for Hadamard *)
type measurement_outcome  = int     (* 0 or 1 *)
type measurement_op       = string  (* e.g., "M" *)

(* qWhile Grammar:
  Seq ::= S1 S2 ... Sn    (n >= 1)
  S ::= skip ;
    |   q := |0> ;
    |   U[q_reg] ;
    |   if ... ;
    |   while M[q_reg] = 1 do Seq end
*)

(* Single Statements *)
type stmt =
  | Skip
  | InitQubit of      var
  | ApplyUnitary of   unitary_op      * qreg
  | IfMeas of         measurement_op  * var * (measurement_outcome * stmt_seq) list
  | WhileMeas of      measurement_op  * var * stmt_seq

(* A Statement Sequence *)
and stmt_seq =
  | SingleCmd of stmt
  | (::) of stmt * stmt_seq
