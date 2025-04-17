open Cqotl_vgc.Ast
open Cqotl_vgc.Pretty_printer
open Cqotl_vgc.Parser_utils

let example = InitQubit "q1" :: SingleCmd (ApplyUnitary ("H", ["q1"]))
let () = print_endline "\n--qWhile programming language--\n"
let () = print_endline "AST -> Pretty print"
let () = print_endline (pretty_print_stmt_seq example)
let () = print_endline "------------------------------\n"
let () = print_endline "Parsing -> AST -> Pretty print"
let () = print_endline (pretty_print_stmt_seq (parse_program ("q1 := |0>; H[q1]; ")))
let () = print_endline "\n"