open Cqotl_vgc.Ast
open Pretty_printer
open Parser_utils

let parse_and_print_file file_path =
  try (* Read the entire file *)
      let channel = open_in file_path                                       in
      let content = really_input_string channel (in_channel_length channel) in
      close_in channel;
    
    (* Parse and print *)
    print_endline "\n-- Parsing file --\n";
    print_endline ("File: " ^ file_path);
    print_endline "Contents:";
    print_endline "\nParsed AST";
    let parsed = parse_program content in
    print_endline (pretty_print_stmt parsed);
    print_endline "\n"
  with
  | Sys_error msg -> print_endline ("File error: " ^ msg)
  | Parsing.Parse_error -> print_endline "Parse error: Invalid program syntax"
  | e -> print_endline ("Error: " ^ Printexc.to_string e)
