open Ast
open Pretty_printer

type envItem =
  | Assumption of {name: id; t: types}
  | Definition of {name: id; t: types; e: terms}

type frame = {
  env: envItem list;
}

(* let calc_type (f : frame) (s : terms) : types = 
  match s with
  | Var _ -> QVar
  | QRegTerm _ -> QReg 0
  | OptTerm _ -> Opt 0
  | LOptTerm _ -> LOpt
  | Assertion _ -> Assertion
  | Stmt _ -> Program
  | Proof -> Program *)

let find_item (f: frame) (name: id) : envItem option =
  List.find_opt (
    function
      | Assumption {name = n; _} -> n = name
      | Definition {name = n; _} -> n = name
    ) 
  f.env

(* The empty frame. *)
let empty_frame : frame = 
  {env = []}

(* Check whether a variable is defined in the frame. *)
let is_defined (f: frame) (name: id) : bool =
  List.exists (function
    | Assumption {name = n; _} -> n = name
    | Definition {name = n; _} -> n = name) f.env


(* The prover. Initially it has empty stack and the frame is described by empty_frame. *)
type prover = {
  mutable stack: frame list;  (* The new frames *)
}

(* Get the latest frame of the environment. *)
let get_frame (p: prover) : frame =
  match p.stack with
  | [] -> empty_frame
  | f :: _ -> f

(* Initialize the prover with an empty stack. *)

let init_prover () : prover = 
  {stack = []}

(* The main function that evaluates the command and updates the state. *)
let rec eval (p: prover) (cmd: command) : unit =
  match cmd with
  | Def {x; t; e} -> 
      eval_def p x t e
  | Var {x; t} -> 
      eval_var p x t
  | Check e ->
      eval_check p e
  | Show x ->
      eval_show p x
  | ShowAll -> 
      eval_showall p
  | Undo -> 
      eval_undo p
  (* | _ -> raise (Failure "Not implemented yet") *)

and eval_def (p: prover) (name: id) (t: types) (e: terms) : unit =
  let frame = get_frame p in
    match find_item frame name with
    | Some _ -> 
      raise (ProverError (Printf.sprintf "Name %s is already declared." name))
    | None -> 
      (* Type check here *)
      p.stack <- {env = Definition {name; t; e}::frame.env} :: p.stack

and eval_var (p: prover) (name: id) (t: types) : unit =
  let frame = get_frame p in
    match find_item frame name with
    | Some _ -> 
      raise (ProverError (Printf.sprintf "Name %s is already declared." name))
    | None ->
      ( (* Check the validity *)
        match t with
        | QVar | Opt _ | Assertion -> ()
        | _ -> 
          raise (ProverError (Printf.sprintf "Type %s is not allowed for variable %s." (type2str t) name))
      );
      (* Add the new variable to the frame. *)
      p.stack <- {env = Assumption {name; t}::frame.env} :: p.stack

and eval_check (p: prover) (e: terms) : unit =
  raise (Failure "Not implemented yet")

and eval_show (p: prover) (x: id) : unit =
  raise (Failure "Not implemented yet")

and eval_showall (p: prover) : unit =
  raise (Failure "Not implemented yet")

and eval_undo (p: prover) : unit =
  match p.stack with
  | [] -> raise (ProverError "No frame to undo.")
  | _ :: rest -> p.stack <- rest

(* the function to evaluate a command list *)
let eval_list (p: prover) (cmds: command list) : unit
  = 
  List.iter (fun cmd -> eval p cmd) cmds

(* formatting *)
let envItem2str (item: envItem ): string = 
  match item with
  | Assumption {name; t} -> 
      Printf.sprintf "%s : %s" name (type2str t)
  | Definition {name; t; e} -> 
    Printf.sprintf "%s := %s : %s" name (term2str e) (type2str t)


(* The whole information about the frame *)
let frame_to_string (f: frame): string =
  let env_str = List.map envItem2str f.env in
    String.concat "\n" env_str 
    |> Printf.sprintf "Context: [\n%s\n]"

let prover_to_string (p: prover): string =
  let frame = get_frame p in
    (frame_to_string frame)
    |> Printf.sprintf "%s" 

let get_status (p: prover) (error: string option) : string =
  let prover_status = prover_to_string p in
  match error with
  | None -> prover_status
  | Some msg -> prover_status ^ "\n---------------------------------------------------------------\nError: \n" ^ msg