(** [move_to_front lst idx] returns a new list where the element at position
    [idx] in [lst] is placed at the front.  
    Positions are one‑based.  
    Raises [Invalid_argument] if [idx] is out of bounds. *)
let move_to_front lst idx =
  if idx < 0 then invalid_arg "move_to_front: negative index";
  (* Split the list into (prefix, target, suffix). *)
  let rec split i prefix = function
    | [] -> invalid_arg "move_to_front: index out of bounds"
    | x :: xs ->
        if i = idx then (x, List.rev prefix, xs)
        else split (i + 1) (x :: prefix) xs
  in
  let (target, prefix_rev, suffix) = split 1 [] lst in
  target :: List.rev_append prefix_rev suffix

let get_first_elements lst n =
  if n <= 0 then
    []
  else
    let rec aux acc i = function
      | [] -> List.rev acc
      | x :: xs ->
          if i < n then aux (x :: acc) (i + 1) xs
          else List.rev acc
    in
    aux [] 0 lst

(* get_last_elements : 'a list -> int -> 'a list *)
let get_last_elements lst n =
  if n <= 0 then
    []                                     (* edge-case: non-positive n *)
  else
    let len = List.length lst in           (* O(L) pass to know the size *)
    let rec drop k l =                     (* drop (len-n) elements *)
      if k <= 0 then l
      else
        match l with
        | []      -> []                    (* n > len ⇒ whole list returned *)
        | _ :: xs -> drop (k - 1) xs
    in
    drop (len - n) lst