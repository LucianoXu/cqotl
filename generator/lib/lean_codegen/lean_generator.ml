(*********************************************************************************)
(* File handling utilities for the LEAN4 generation mechanism                    *)
(* Make sure to create `cqotl_path.config` file and specify path of this project *)
(*********************************************************************************)

open Lean_ast
open Printf
open Lean_printer
open Lean_examples
let config_file = "cqotl_path.config"

(* Define the relative path from the base CQOTL directory to the Lean Examples directory *)
let relative_lean_examples_dir = "lean-veri/LeanVeri/Examples"

(* Function to read the base path from the config file *)
let read_cqotl_base_path config_path =
  try
    let ic = open_in config_path in
    let base_path = input_line ic in
    close_in ic;
    Some base_path
  with
  | Sys_error msg ->
      eprintf "Error: Could not open or read config file '%s' - %s\n" config_path msg;
      None
  | End_of_file ->
      eprintf "Error: Config file '%s' is empty. Please provide the base CQOTL path.\n" config_path;
      None

(* Function to write content to a file *)
let write_content_to_file filepath content =
  try
    let oc = open_out filepath in
    fprintf oc "%s" content; (* Use %s not %s\n because lean_ast_to_lean_file already adds a newline *)
    close_out oc;
    printf "  -> Successfully wrote Lean code to '%s'\n" filepath;
    true
  with
  | Sys_error msg ->
      eprintf "Error: Could not write to file '%s' - %s\n" filepath msg;
      false

(* --- New function to process a single example --- *)
let process_example (file_ast, filename) =
  printf "Processing example: %s\n" filename;

  (* Generate the Lean code string from the AST *)
  let lean_code_string = lean_ast_to_lean_file file_ast in

  (* Get the base path from the config *)
  match read_cqotl_base_path config_file with
  | Some base_path ->
      (* Construct the full path to the target Lean file *)
      let dir_components = String.split_on_char '/' relative_lean_examples_dir in
      let full_examples_dir = List.fold_left Filename.concat base_path dir_components in
      (* Then, add the specific filename *)
      let full_lean_path = Filename.concat full_examples_dir filename in

      (* Write the generated code to the file *)
      let success = write_content_to_file full_lean_path lean_code_string in
      if not success then
        eprintf "Failed to process example '%s' due to file writing error.\n" filename;
      ()
  | None ->
      eprintf "Skipping example '%s' due to config file error.\n" filename;
      ()

(* --- Main execution block --- *)
let () =
  printf "Starting Lean file generation from CQOTL Prover...\n";
  (* Check if the config file exists before starting *)
  if not (Sys.file_exists config_file) then (
    eprintf "Error: Config file '%s' not found. Please create it with the base path of your CQOTL project.\n" config_file;
    exit 1
  );
  (* Iterate through the list of examples and process each one *)
  List.iter process_example examples;

  printf "Finished Lean4 obligation generation.\n";
