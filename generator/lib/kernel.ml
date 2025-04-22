open Ast
open Pretty_printer

type envItem =
  | Assumption of {name: id; t: types}
  | Definition of {name: id; t: types; e: terms}

type frame = {
  env: envItem list;
}

let find_item (f: frame) (name: id) : envItem option =
  List.find_opt (
    function
      | Assumption {name = n; _} -> n = name
      | Definition {name = n; _} -> n = name
    ) 
  f.env

type typing_result =
  | Type of types
  | TypeError of string

(** Calculate the type of the term. Raise the corresponding error when typing failes. *)
let rec calc_type (f : frame) (s : terms) : typing_result = 
  match s with
  | Var x -> 
      calc_type_var f x
  | QRegTerm qs -> 
      calc_type_qreg f qs
  | OptTerm o ->
      calc_type_opt f o
  | LOptTerm lo ->
      calc_type_lopt f lo
  | Assertion _ ->
      raise (Failure "Unexpected assertion for type calculation.")
  | Stmt ss -> 
      calc_type_program f ss
  | Proof ->
      raise (Failure "Unexpected proof term for type calculation.")

and calc_type_var (f : frame) (v : id) : typing_result = 
  match find_item f v with
  | Some (Assumption {t; _}) -> Type t
  | Some (Definition {t; _}) -> Type t
  | None -> TypeError (Printf.sprintf "Variable %s is not defined." v)

and calc_type_qreg (f : frame) (qs : qreg) : typing_result = 
  if List.for_all (fun qv -> (calc_type_var f qv) = Type QVar) qs then
    (* Check whether there are repeated variable in the register *)
    let rec check_repeated lst = 
      match lst with
      | [] -> true
      | x :: xs -> 
          if List.exists (fun y -> x = y) xs then
            false
          else
            check_repeated xs
    in
    if check_repeated qs then
      Type (QReg (List.length qs))
    else
      TypeError (Printf.sprintf "The quantum register %s contains repeated variables." (qreg2str qs))
  else
    TypeError (Printf.sprintf "The quantum register %s is not well typed." (qreg2str qs))

and calc_type_opt (f : frame) (o : opt) : typing_result = 
  match o with
  | Add {o1; o2} -> 
      let t1 = calc_type f o1 in
      let t2 = calc_type f o2 in
        if t1 = t2 then
          t1
        else
          TypeError (Printf.sprintf "The operator %s is not well typed." (opt2str o))

and calc_type_lopt (f : frame) (lo : lopt) : typing_result = 
  match lo with
  | Pair {opt; qs} -> 
      let t = calc_type f opt in
      let qs_t = calc_type_qreg f qs in
      match t, qs_t with
      | Type (Opt n), Type (QReg m) -> 
          if n = m then
            Type LOpt
          else
            TypeError (Printf.sprintf "The operator %s is not well typed, because the system number mismatch." (term2str opt))
      | _ ->
          TypeError (Printf.sprintf "The operator %s is not well typed." (term2str opt))

and calc_type_program (f : frame) (s : stmt_seq) : typing_result = 
  match s with
  | SingleCmd cmd -> 
      calc_type_stmt f cmd
  | cmd1 :: cmd2 -> 
      let t1 = calc_type_stmt f cmd1 in
      let t2 = calc_type_program f cmd2 in
        if t1 = Type Program && t2 = Type Program then
          Type Program
        else
          TypeError (Printf.sprintf "The program %s is not well typed." (stmt_seq_2_str s))

and calc_type_stmt (f :frame) (s : stmt) : typing_result = 
  match s with
  | Skip -> 
      Type Program
  | _ -> 
      Type Program
      (* Not implemented *)



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


(* formatting *)
let envItem2str (item: envItem ): string = 
  match item with
  | Assumption {name; t} -> 
      Printf.sprintf "%s : %s" name (type2str t)
  | Definition {name; t; e} -> 
    Printf.sprintf "%s := %s : %s" name (term2str e) (type2str t)


let env2string (env: envItem list): string =
  let env_str = List.map envItem2str env in
    String.concat "\n" env_str
    |> Printf.sprintf "[\n%s\n]"

(* The whole information about the frame *)
let frame2string (f: frame): string =
  let env_str = env2string f.env in
    Printf.sprintf "Context: %s" env_str

let prover2string (p: prover): string =
  let frame = get_frame p in
    (frame2string frame)
    |> Printf.sprintf "%s" 

type eval_result = 
  | Success
  | ProverError of string
  | Pause

(***********************************************************************)
(* The main function that evaluates the command and updates the state. *)
let rec eval (p: prover) (cmd: command) : eval_result =
  let res =
    match cmd with
    | Def {x; t; e} -> 
        eval_def p x t e
    | DefWithoutType {x; e} ->
        eval_def_without_type p x e
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
    | Pause ->
        Pause
    (* | _ -> raise (Failure "Not implemented yet") *)
  in match res with
    | ProverError msg -> 
        ProverError (msg ^ "\n\nFor the command:\n" ^ (command2str cmd))
    | _ -> res
  

and eval_def (p: prover) (name: id) (t: types) (e: terms) : eval_result =
  let frame = get_frame p in
    match find_item frame name with
    | Some _ -> 
      ProverError (Printf.sprintf "Name %s is already declared." name)
    | None -> 
      (* Type check here *)
      match calc_type frame e with
      | Type t' when t = t' -> 
          (* Add the new definition to the frame. *)
          p.stack <- {env = Definition {name; t; e}::frame.env} :: p.stack;
          Success
      | Type t' -> 
          ProverError (Printf.sprintf "The variable %s is specified as type %s, but term %s has type %s." name (type2str t) (term2str e) (type2str t'))
      | TypeError msg -> 
          ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_def_without_type (p: prover) (name: id) (e: terms) : eval_result =
  let frame = get_frame p in
    match find_item frame name with
    | Some _ -> 
      ProverError (Printf.sprintf "Name %s is already declared." name)
    | None -> 
      (* Type check here *)
      match calc_type frame e with
      | Type t ->   
          (* Add the new definition to the frame. *)
          p.stack <- {env = Definition {name; t; e}::frame.env} :: p.stack;
          Success
      | TypeError msg ->
          ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_var (p: prover) (name: id) (t: types) : eval_result =
  let frame = get_frame p in
    match find_item frame name with
    | Some _ -> 
      ProverError (Printf.sprintf "Name %s is already declared." name)
    | None ->
        (* Check the validity *)
        match t with
        | QVar | Opt _ | Assertion ->
          (* Add the new variable to the frame. *)
          p.stack <- {env = Assumption {name; t}::frame.env} :: p.stack;
          Success
        | _ -> 
          ProverError (Printf.sprintf "Type %s is not allowed for assumptions." (type2str t))

and eval_check (p: prover) (e: terms) : eval_result =
  let frame = get_frame p in
    (* Type check here *)
    match calc_type frame e with
    | Type t -> 
      Printf.printf "Check %s: %s.\n" (term2str e) (type2str t);
      Success
    | TypeError msg -> 
      ProverError (Printf.sprintf "The term %s is not well typed: %s" (term2str e) msg)

and eval_show (p: prover) (x: id) : eval_result =
  let frame = get_frame p in
    let item = find_item frame x in
      match item with
      | Some (Assumption {name; t}) -> 
          Printf.printf "Show %s : %s.\n" name (type2str t);
          Success
      | Some (Definition {name; t; e}) -> 
          Printf.printf "Show %s : %s := %s.\n" name (type2str t) (term2str e);
          Success
      | None -> 
          ProverError (Printf.sprintf "Name %s is not defined." x)

and eval_showall (p: prover) : eval_result =
  let frame = get_frame p in
  Printf.printf "ShowAll:\n%s\n" (env2string frame.env);
  Success
    

and eval_undo (p: prover) : eval_result =
  match p.stack with
  | [] -> ProverError "No frame to undo."
  | _ :: rest -> p.stack <- rest; Success

let get_status (p: prover) (eval_res: eval_result) : string =
  let prover_status = prover2string p in
  match eval_res with
  | Success -> prover_status
  | ProverError msg -> prover_status ^ "\n---------------------------------------------------------------\nError: \n" ^ msg
  | Pause ->
    prover_status ^ "\n---------------------------------------------------------------\n" ^ "Paused by user."


(* the function to evaluate a command list, stops at the first error. *)
let rec eval_list (p: prover) (cmds: command list) : eval_result
  = 
  match cmds with
  | [] -> Success
  | [tail] -> eval p tail
  | cmd :: rest ->
    let res = eval p cmd in
      match res with
      | Success -> eval_list p rest
      | ProverError _ -> res
      | Pause -> Pause