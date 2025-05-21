open Unix
(* open Cqotl_vgc.Ast *)
(* open Cqotl_vgc.Pretty_printer *)
open Cqotl_vgc.Parser_utils
open Cqotl_vgc.Kernel


(** read the whole file as string *)
let read_file (path: string) : string =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      let len = in_channel_length ic in
      really_input_string ic len)

(** atomic file writing *)
let write_file ~(dst: string) ~(content: string) : unit =
  let oc = open_out dst in
  Fun.protect
    ~finally:(fun () -> close_out oc)
    (fun () -> output_string oc content)

(* Get the modification time *)
let mtime path =
  try (Unix.stat path).st_mtime with
  | Unix_error (ENOENT, _, _) -> 0.0

let watcher_print msg =
  let timestamp = Unix.time () |> Unix.gmtime in
    Printf.printf "[%02d:%02d:%02d] %s\n%!"
      timestamp.tm_hour timestamp.tm_min timestamp.tm_sec msg
  

let check_source_status source status =
  (* check if the source file exists. create them if not. *)
    if not (Sys.file_exists source) then (
      let oc = open_out source in
      Fun.protect
        ~finally:(fun () -> close_out oc)
        (fun () -> output_string oc "");
        watcher_print (Printf.sprintf "File %s created.\n%!" source);
      );
    if not (Sys.file_exists status) then (
      let oc = open_out status in
      Fun.protect
        ~finally:(fun () -> close_out oc)
        (fun () -> output_string oc "");
        watcher_print (Printf.sprintf "File %s created.\n%!" status);
      )
      
let () =
  (* process the command lind argument *)
  if Array.length Sys.argv <> 3 then (
    Printf.eprintf "Usage: %s <source> <status>\n" Sys.argv.(0);
    exit 1);
  let source  = Sys.argv.(1)
  and status  = Sys.argv.(2) in

  (* monitor loop 
      last_mtime is the last modification time of the source file.
  *)
  let rec loop last_mtime =
    let now = mtime source in
    check_source_status source status;
    if now > last_mtime then (
      (* file changed *)
      let p = init_prover () in
      let status_content : string = 
          let content   = read_file source in
          let parse_res = parse_top_inc content in
          match parse_res with
          (* Complete Parsing *)
          | Complete cmds ->    
            let eval_res = eval_list p cmds in
              get_status p eval_res

          (* Partial Parsing, execute the best command list and report the syntax error. *)
          | Partial (cmds, msg) ->
            let eval_res = eval_list p cmds in
              Printf.sprintf "%s\n\nSyntax error: %s" (get_status p eval_res) msg
      in
        write_file ~dst:status ~content:status_content;
        watcher_print (Printf.sprintf "%s updated -> %s\n%!" source status);
        loop now  (* update the modification time *)

    ) else (
      (* file not changed, sleep for a while *)
      Unix.sleepf 0.1;
      loop last_mtime)
  in
  loop 0.0