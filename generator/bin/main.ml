open Cqotl_vgc.Ast
open Cqotl_vgc.Pretty_printer
open Cqotl_vgc.Parser_utils

let example = Seq(InitQubit "q1", ApplyUnitary ("H", ["q1"]))

let () = print_endline (pretty_print_stmt example)

let () = print_endline (pretty_print_stmt (parse_program ("q1 := |0>; H[q1]")))