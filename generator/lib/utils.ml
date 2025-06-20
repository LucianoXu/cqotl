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

(** get_last_elements : 'a list -> int -> 'a list *)
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

(** check whether all elements are unique in the list. *)
let all_unique lst =
  let rec aux seen = function
    | [] -> true
    | x :: xs ->
        if List.mem x seen then false
        else aux (x :: seen) xs
  in
  aux [] lst

(** Check whether two lists do not have the same element. *)
let list_disjoint lst1 lst2 =
  let rec aux = function
    | [] -> true
    | x :: xs ->
        if List.mem x lst2 then false
        else aux xs
  in
  aux lst1

(** Remove all elemnets of lst1 that appear in lst2 and return the result. *)
let list_remove lst1 lst2 =
  let rec aux acc = function
    | [] -> List.rev acc
    | x :: xs ->
        if List.mem x lst2 then aux acc xs
        else aux (x :: acc) xs
  in
  aux [] lst1

(** append all elements in lst2 that does not appear in lst1, and return. *)
let list_union lst1 lst2 =
  (* Append elements from lst2 that don't appear in lst1 *)
  let rec aux acc = function
    | [] -> List.rev acc
    | x :: xs ->
        if List.mem x lst1 then aux acc xs
        else aux (x :: acc) xs
  in
  lst1 @ aux [] lst2
  

(* Some wrappers for often used expressions *)
open Ast
let labelled_ketbra (bket: terms) (bbra: terms) (qs: terms) : terms =
  Fun {
      head = _subscript;
      args = [
        Fun {
          head = _apply;
          args = [
            Fun {head = _ket; args = [bket]};
            Fun {head = _bra; args = [bbra]};
          ]
        };
        Fun {
          head = _pair;
          args = [qs; qs]
        }
      ]
    }

let labelled_proj (b: terms) (qs : terms) : terms =
  labelled_ketbra b b qs

let imply_type (p: terms) (q : terms) : terms =
  let t_symbols = get_symbols p @ get_symbols q in
  let name = fresh_name t_symbols "x" in
  Fun {
        head = _forall;
        args = [
          Symbol name;
          p;
          q;
        ]
      }

let bitterm_to_type (p: terms) : terms =
  Fun {
    head = _eq;
    args = [
      p;
      Symbol _true;
    ]
  }