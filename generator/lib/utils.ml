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
