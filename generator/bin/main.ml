open Cqotl_vgc.Ast
open Cqotl_vgc.Pretty_printer

let example = Seq(InitQubit "q1", ApplyUnitary ("H", ["q1"]))

let () = print_endline (pretty_print_stmt example)