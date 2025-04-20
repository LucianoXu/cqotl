(* open Cqotl_vgc.Ast *)
(* open Cqotl_vgc.Pretty_printer *)
open Cqotl_vgc.Parser_utils
open Cqotl_vgc.Kernel

let repeat (f : prover -> unit) = 
  let p = {stack = []} in
    let rec aux () =
        f p;
        aux ()
    in
    aux ()

let step (p: prover) = 
    print_string "> ";
    flush stdout;
    try
      let input_line = read_line () in
      let line = String.trim input_line in

      (* skip empty input *)
      if line = "" then ()

      (* parse the input and interact with kernel *)
      else (
        let cmds = parse_top line in
          eval_list p cmds;
        print_endline (prover_to_string p);
      )

    with
    | End_of_file ->
        (* capture Ctrl+D, exit normally *)
        print_endline "Exit with Ctrl+D.";
        exit 0

    | Failure msg ->
        (* handle parsing errors *)
        print_endline ("Error: " ^ msg)


(* ENTRY POINT *)
let () = 
  print_endline " ---------- CQOTL Prover ----------";
  repeat step