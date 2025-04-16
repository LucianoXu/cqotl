
type var                  = string
type qreg                 = var list
type unitary_op           = string  (* e.g. "H" for Hadamard *)
type measurement_outcome  = int     (* 0 or 1 *)
type measurement_op       = string  (* e.g., "M" *)

(* qWhile Grammar:
  S ::= skip
    |   S1 ; S2
    |   q := |0>
    |   q_reg := U[q_reg]
    |   if ...
    |   while M[q_reg] = 1 do S od
*)
type stmt =
  | Skip                                                                  
  | Seq of            stmt * stmt
  | InitQubit of      var
  | ApplyUnitary of   unitary_op      * qreg
  | IfMeas of         measurement_op  * var * (measurement_outcome * stmt) list
  | WhileMeas of      measurement_op  * var * stmt
