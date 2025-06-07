open Ast
open Pretty_printer
open Utils

(* QVList Calculation *)
type termls_result =
  | TermList of terms list
  | TermError of string

(** the function to calculate the qvlist from the qreg term *)
let rec get_qvlist (qreg : terms) : termls_result =
  match qreg with
  | Symbol _ -> TermList [qreg]
  | Fun {head; args=[t1; t2]} when head=_pair ->
    let t1_list = get_qvlist t1 in
    let t2_list = get_qvlist t2 in
    (
      match t1_list, t2_list with
      | TermList l1, TermList l2  -> TermList (l1 @ l2)
      | TermError msg, _          -> TermError msg
      | _, TermError msg          -> TermError msg
    )
  | _ -> TermError "Cannot calculate the quantum variable list for the given term."

(* return a fresh name for the context *)
let fresh_name_for_ctx (ctx: wf_ctx) (prefix : string): string =
  (* Helper function to get all symbols in an environment list *)
  let get_symbols_from_env (env: envItem list) : string list =
    List.map (function
      | Assumption {name; _} -> name
      | Definition {name; _} -> name
    ) env
  in
  
  (* Get all symbols from both ctx and env *)
  let all_symbols = get_symbols_from_env ctx.ctx @ get_symbols_from_env ctx.env in
  fresh_name all_symbols prefix

(** Create a well-formed context from an environment with empty context. *)
let env2wfctx env = {env=env; ctx=[]}

(** Find the item in the well-formed context. *)
let find_item (wfctx: wf_ctx) (name: string) : envItem option =
  let find_item_single (env: envItem list) (name: string) : envItem option =
    List.find_opt (
      function
        | Assumption {name = n; _} -> n = name
        | Definition {name = n; _} -> n = name
      ) 
    (env) 
  in
  let ctx_res = find_item_single wfctx.ctx name in
  match ctx_res with
  | Some _ -> ctx_res
  | None ->
    let env_res = find_item_single wfctx.env name in
    match env_res with
    | Some _ -> env_res
    | None -> None

type typing_result =
  | Type        of terms
  | TypeError   of string

(** Calculate the type of the term. Raise the corresponding error when typing failes. *)
let rec calc_type (wfctx : wf_ctx) (s : terms) : typing_result = 
  match s with

  (* Type *)
  | Symbol sym when sym = _type -> 
    Type (Symbol _type)
  
  (* forall *)
  | Fun {head; args=[Symbol x; t; t']} when head = _forall ->
    begin
      match type_check wfctx t (Symbol _type) with
      | Type _ -> 
        begin
          let new_wfctx = {wfctx with ctx = Assumption {name = x; t = t} :: wfctx.ctx} in
          match type_check new_wfctx t' (Symbol _type) with
          | Type _ -> Type (Symbol _type)
          | TypeError _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t'))
        end
      | TypeError _ ->
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t))
    end
  
  (* function *)
  | Fun {head; args=[Symbol x; t; e]} when head = _fun ->
    begin
      match type_check wfctx t (Symbol _type) with
      | Type _ ->
        begin
          let new_wfctx = {wfctx with ctx = Assumption {name = x; t = t} :: wfctx.ctx} in
          match calc_type new_wfctx e with
          | Type type_e -> 
            let sym = fresh_name_for_term type_e x in
            Type (Fun {head=_forall; args=[Symbol sym; t; substitute type_e x (Symbol sym)]})
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str e) msg)
        end
      | TypeError _ ->
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as Type." (term2str s) (term2str t))
    end
    
  (* apply *)
  | Fun {head; args=[t1; t2]} when head = _apply ->
    begin
      match calc_type wfctx t1 with
      (* function application *)
      | Type (Fun {head; args=[Symbol x; forall_t; forall_t']}) when head = _forall ->
        begin
          match type_check wfctx t2 forall_t with
          | Type _ ->
            Type (substitute forall_t' x t2)
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as a valid argument. %s" (term2str s) (term2str t2) msg)
        end
      (* scalar multiplication *)
      | Type (Symbol sym) when sym = _stype ->
        begin
          match calc_type wfctx t2 with
          | Type (Symbol sym) when sym = _stype -> Type (Symbol _stype)
          | Type (Fun {head; args=[t]}) when head = _ktype ->
            Type (Fun {head=_ktype; args=[t]})
          | Type (Fun {head; args=[t]}) when head = _btype ->
            Type (Fun {head=_btype; args=[t]})
          | Type (Fun {head; args=[t1; t2]}) when head = _otype ->
            Type (Fun {head=_otype; args=[t1; t2]})
          | _ -> TypeError (Printf.sprintf "%s typing failed for scalar multiplication." (term2str s))
        end
      | Type (Fun {head; args=[t]}) when head = _btype ->
        begin
          match calc_type wfctx t2 with
          (* inner product *)
          | Type (Fun {head; args=[t']}) when head = _ktype ->
            if t = t' then
              Type (Symbol _stype)
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not bra and ket of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          (* bra-opt mult *)
          | Type (Fun {head; args=[t1'; t2']}) when head = _otype ->
            if t = t1' then
              Type (Fun {head=_btype; args=[t2']})
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not bra and operator of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | Type (Fun {head; args=[t]}) when head = _ktype ->
        begin
          match calc_type wfctx t2 with
          (* outer product *)
          | Type (Fun {head; args=[t']}) when head = _btype ->
            Type (Fun {head=_otype; args=[t; t']})
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | Type (Fun {head; args=[u; v]}) when head = _otype ->
        begin
          match calc_type wfctx t2 with
          (* opt-ket mult *)
          | Type (Fun {head; args=[v']}) when head = _ktype ->
            if v = v' then
              Type (Fun {head=_ktype; args=[u]})
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not operator and ket of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          | Type (Fun {head; args=[u'; v']}) when head = _otype ->
            if v = u' then
              Type (Fun {head=_otype; args=[u; v']})
            else
              TypeError (Printf.sprintf "%s typing failed. %s and %s are not operator and operator of the consistent classical type." (term2str s) (term2str t1) (term2str t2))
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      (* labelled dirac notation multiplication *)
      | Type (Fun {head; args=[Fun{args=s1; _}; Fun{args=s1'; _}]}) when head = _dtype ->
        begin
          match calc_type wfctx t2 with
          | Type (Fun {head; args=[Fun{args=s2; _}; Fun{args=s2'; _}]}) when head = _dtype -> 
            let s2_sub_s1' = list_remove s2 s1' in
            let s1'_sub_s2 = list_remove s1' s2 in
            if list_disjoint s1 s2_sub_s1' && list_disjoint s2' s1'_sub_s2 then
              Type (Fun 
              {head=_dtype; 
              args=[
                Fun {head=_list; args=s1 @ s2_sub_s1'}; 
                Fun {head=_list; args=s2' @ s1'_sub_s2}
              ];
            })
            else
              TypeError (Printf.sprintf "%s typing failed. quantum vairbale lists are not disjoint." (term2str s))

          | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as DType." (term2str s) (term2str t2))
        end

      (* probabilistic distribution *)
      | Type (Fun {head; args=[ct]}) when head = _pdist ->
        begin
          match type_check wfctx t2 (Fun {head=_cterm; args=[ct]}) with
          | Type _ -> Type (Symbol _stype)
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[%s]. %s" (term2str s) (term2str t2) (term2str ct) msg)
        end

      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* CType *)
  | Symbol sym when sym = _ctype ->
    Type (Symbol _type)

  (* CVar *)
  | Fun {head; args=[t]} when head = _cvar ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* CTerm *)
  | Fun {head; args=[t]} when head = _cterm ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* PDist *)
  | Fun {head; args=[t]} when head = _pdist ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* Set *)
  | Fun {head; args=[t]} when head = _set ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* bit *)
  | Symbol sym when sym = _bit ->
    Type (Symbol _ctype)  

  (* QVList *)
  | Symbol sym when sym = _qvlist ->
    Type (Symbol _type)

  (* OptPair *)
  | Fun {head; args=[t]} when head = _optpair ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* QReg *)
  | Fun {head; args=[t]} when head = _qreg ->
    begin
      match type_check wfctx t (Symbol _ctype) with
      | Type _ -> Type (Symbol _type)
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType. %s" (term2str s) (term2str t) msg)
    end

  (* SType *)
  | Symbol sym when sym = _stype ->
    Type (Symbol _type)

  (* KType *)
  | Fun {head; args=[t]} when head = _ktype ->
    begin
      match calc_type wfctx t with 
      | Type type_t when type_t = Symbol _ctype -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end

  (* BType *)
  | Fun {head; args=[t]} when head = _btype ->
    begin
      match calc_type wfctx t with 
      | Type type_t when type_t = Symbol _ctype -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end

  (* OType *)
  | Fun {head; args=[t1; t2]} when head = _otype ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 when 
        type_t1 = Symbol _ctype && type_t2 = Symbol _ctype -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as CType." (term2str s) (term2str t1) (term2str t2))
    end

  (* DType *)
  | Fun {head; args=[r1; r2]} when head = _dtype ->
    begin
      match calc_type wfctx r1, calc_type wfctx r2 with
      | Type type_r1, Type type_r2 when 
        type_r1 = Symbol _qvlist && type_r2 = Symbol _qvlist -> Type (Symbol _type)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as QVList." (term2str s) (term2str r1) (term2str r2))
    end

  (* ProgStt *)
  | Symbol sym when sym = _progstt -> Type (Symbol _type)

  (* Prog *)
  | Symbol sym when sym = _prog -> Type (Symbol _type)

  (* CQProj *)
  | Symbol sym when sym = _cqproj -> Type (Symbol _type)


  (* Assn *)
  | Symbol sym when sym = _assn -> Type (Symbol _type)


  (*** typing for program statements ***)
  (* seq *)
  | Fun {head; args} when head = _seq ->
    (* Check whether all arguments are typed as prog *)
    let rec check_args args =
      match args with
      | [] -> TypeError "Empty program sequence is not allowed."
      | [prog] -> 
        begin
          match calc_type wfctx prog with
          | Type (Symbol sym) when sym = _progstt -> Type (Symbol _prog)
          | Type _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt." (term2str s) (term2str prog))
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt. %s" (term2str s) (term2str prog) msg)
        end
      | prog :: rest ->
        begin
          match calc_type wfctx prog with
          | Type (Symbol sym) when sym = _progstt -> check_args rest
          | Type _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt." (term2str s) (term2str prog))
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as ProgStt. %s" (term2str s) (term2str prog) msg)
        end
      in
      check_args args

  (* Skip *)
  | Symbol sym when sym = _skip -> Type (Symbol _progstt)

  (* Assign *)
  | Fun {head; args=[Symbol x; t]} when head = _assign ->
    begin
      match calc_type wfctx (Symbol x) with
      | Type (Fun {head=_cvar; args=[a]}) ->
        begin
          match is_cterm wfctx t with
          | Type type_t when type_t = (Fun {head=_cterm; args=[a]}) -> Type (Symbol _progstt)
          | Type _ -> 
            TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type." (term2str s) x (term2str t))
          | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type. %s" (term2str s) x (term2str t) msg)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CVar." (term2str s) x)
    end

  (* PAssign *)
  | Fun {head; args=[Symbol x; miu]} when head = _passign ->
    begin
      match calc_type wfctx miu with
      | Type (Fun {head; args=[t]}) when head = _pdist ->
        begin
        match type_check wfctx (Symbol x) (Fun {head=_cvar; args=[t]}) with
        | Type _ -> Type (Symbol _progstt)
        | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s cannot be typed as CVar[%s]. %s" (term2str s) x (term2str t) msg)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as PDist." (term2str s) (term2str miu))
    end

  (* Init Qubit *)
  | Fun {head; args=[qs]} when head = _init_qubit ->
    begin
      match calc_type wfctx qs with
      | Type (Fun {head=_qreg; args=[_]}) -> Type (Symbol _progstt)
      | Type tt -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s instead of QReg." (term2str s) (term2str qs) (term2str tt))
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as QReg. %s" (term2str s) (term2str qs) msg)
    end

  (* Unitary *)
  | Fun {head; args=[u; qs]} when head = _unitary ->
    begin
      match calc_type wfctx u, calc_type wfctx qs with
      | Type (Fun {head=head1; args=[t1; t1']}), Type (Fun {head=head2; args=[t2]}) when 
      (
        head1 = _otype &&
        head2 = _qreg &&
        t1 = t1' && t1 = t2
      ) ->
        Type (Symbol _progstt)
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* measure *)
  | Fun {head; args=[Symbol x; m_opt; qs]} when head = _meas ->
    begin
      match calc_type wfctx (Symbol x), calc_type wfctx m_opt, calc_type wfctx qs with
      | Type type1, Type type2, Type type3->
        begin
        match type1, type2, type3 with
        | Fun {head=head1; args=[t1]}, Fun {head=head2; args=[t2]}, Fun {head=head3; args=[t3]} when 
          (
            head1 = _cvar && t1 = Symbol _bit &&
            head2 = _optpair && 
            head3 = _qreg &&
            t2 = t3
          ) ->
          Type (Symbol _progstt)

        | Fun {head=head1; args}, _, _ when head1 = _cvar && args <> [Symbol _bit] ->
          TypeError (Printf.sprintf "%s typing failed. %s is typed as %s, instead of CVAR[BIT]." (term2str s) x (term2str (Fun {head=_cvar; args})))
        | _ -> 
          TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end 
      | _ ->
        TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* if *)
  | Fun {head; args=[b; s1; s2]} when head = _if ->
    begin
      match is_cterm wfctx b, calc_type wfctx s1, calc_type wfctx s2 with
      | Type type1, Type type2, Type type3 when type1 = Fun {head=_cterm; args=[Symbol _bit]} && type2 = Symbol _prog && type3 = Symbol _prog ->
        Type (Symbol _progstt)

      | Type (Fun {head; args}), _, _ when head = _cterm && args <> [Symbol _bit] -> 
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit]." (term2str s) (term2str b))

      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* while *)
  | Fun {head; args=[b; s']} when head = _while ->
    begin
      match is_cterm wfctx b, calc_type wfctx s' with
      | Type type1, Type type2 when type1 = Fun {head=_cterm; args=[Symbol _bit]} && type2 = Symbol _prog ->
        Type (Symbol _progstt)
      | Type (Fun {head; _}), _ when head = _cterm -> 
        TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit]." (term2str s) (term2str b))
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* star *)
  | Fun {head; args=[t1; t2]} when head = _star ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          (* product of ctype *)
          | Symbol v1, Symbol v2 when v1 = _ctype && v2 = _ctype ->
            Type (Symbol _ctype)

          (* tensor product - otype *)
          | Fun {head=head1; args=[t1; t2]}, Fun {head=head2; args=[t1'; t2']} when
            head1 = _otype && head2 = _otype ->
              Type (Fun {head=_otype; args=[
                Fun {head=_star; args=[t1; t1']}; 
                Fun {head=_star; args=[t2; t2']}
              ]})

          (* tensor product - ktype *)
          | Fun {head=head1; args=[t1]}, Fun {head=head2; args=[t1']} when
            head1 = _ktype && head2 = _ktype ->
              Type (Fun {head=_ktype; args=[
                Fun {head=_star; args=[t1; t1']}
              ]})
          
          (* tensor product - btype *)
          | Fun {head=head1; args=[t1]}, Fun {head=head2; args=[t1']} when
            head1 = _btype && head2 = _btype ->
              Type (Fun {head=_btype; args=[
                Fun {head=_star; args=[t1; t1']}
              ]})

          (* tensor product - dtype *)
          | Fun {head=head1; args=[Fun{args=s1; _}; Fun{args=s2; _}]}, Fun {head=head2; args=[Fun{args=s1'; _}; Fun{args=s2'; _}]} when
            head1 = _dtype && head2 = _dtype ->
              (* Check the disjointness of symbols *)
              if list_disjoint s1 s1' && list_disjoint s2 s2' then
                Type (Fun {head=_dtype; args=[
                  Fun{head=_list; args=s1 @ s1'};
                  Fun{head=_list; args=s2 @ s2'};
                ]})
              else
                TypeError (Printf.sprintf "%s typing failed. Quantum register list disjointness not satisfied." (term2str s))

          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> 
        TypeError (Printf.sprintf "%s typing failed. %s and %s are not well typed." (term2str s) (term2str t1) (term2str t2))
    end

  (* pair *)
  | Fun {head; args=[t1; t2]} when head = _pair ->
    begin
      match is_cterm wfctx t1, is_cterm wfctx t2 with
      (* classical item pair *)
      | Type (Fun {args=[tt1]; _}), Type (Fun {args=[tt2]; _}) ->
        Type (Fun {head=_cterm; args=[Fun {head=_star; args=[tt1; tt2]}]})
      | _ ->
        match calc_type wfctx t1, calc_type wfctx t2 with

        (* operator pair *)
        | Type (Fun {head=head1; args=[tt1; tt2]}), Type (Fun {head=head2; args=[tt1'; tt2']}) when head1 = _otype && head2 = _otype && tt1 = tt2 && tt1' = tt2' && tt1 = tt1'->
          Type (Fun {head=_optpair; args=[tt1]})

        | Type (Fun {head=head1; _}), Type (Fun {head=head2; _}) when head1 = _otype && head2 = _otype ->
          TypeError (Printf.sprintf "%s typing failed. %s and %s are not square operators of the same type." (term2str s) (term2str t1) (term2str t2))

        (* QReg pair *)
        | Type (Fun {head=head1; args=[tt1]}), Type (Fun {head=head2; args=[tt2]}) when head1 = _qreg && head2 = _qreg ->
          Type (Fun {head=_qreg; args=[Fun{head=_star; args=[tt1; tt2]}]})

        | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as OType." (term2str s) (term2str t1) (term2str t2))
    end

  (* list of qreg *)
  | Fun {head; args} when head = _list ->
    (* check whether all qreg are unique *)
    if not (all_unique args) then
      TypeError (Printf.sprintf "%s typing failed. It contains duplicate quantum variables." (term2str s))
    else
      let rec aux args =
        begin
        match args with
        | [] -> Type (Symbol _qvlist)
        | hd :: tl ->
          match hd with
          | Symbol _ ->
            begin
              match calc_type wfctx hd with
              | Type (Fun {head; _}) when head = _qreg ->
                aux tl
              | _ -> TypeError (Printf.sprintf "%s cannot be typd as QReg." (term2str hd))
            end
          | _ -> 
            TypeError (Printf.sprintf "All elements of the qvlist should be atomic symbols.")
        end
      in aux args


  (**************************************)
  (* Dirac Notation *)
  (* ket *)
  | Fun {head; args=[t]} when head = _ket ->
    begin
      match is_cterm wfctx t with
      | Type (Fun {head=head; args=[t]}) when head=_cterm ->
          Type (Fun {head=_ktype; args=[t]})
      | Type t' -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s, instead of CTerm[_]." (term2str s) (term2str t) (term2str t'))
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t) msg)
    end

  (* bra *)
  | Fun {head; args=[t]} when head = _bra ->
      begin
        match is_cterm wfctx t with
        | Type (Fun {head=head; args=[t]}) when head=_cterm ->
            Type (Fun {head=_btype; args=[t]})
        | Type t' -> TypeError (Printf.sprintf "%s typing failed. %s is typed as %s, instead of CTerm[_]." (term2str s) (term2str t) (term2str t'))
        | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t) msg)
      end

  (* adj *)
  | Fun {head; args=[t]} when head = _adj ->
    begin
      match calc_type wfctx t with
      | Type (Symbol sym) when sym = _stype ->
        Type (Symbol _stype)
      | Type (Fun {head=head; args=[t]}) when head=_ktype ->
        Type (Fun {head=_btype; args=[t]})
      | Type (Fun {head=head; args=[t]}) when head=_btype ->
        Type (Fun {head=_ktype; args=[t]})
      | Type (Fun {head=head; args=[t1; t2]}) when head=_otype ->
        Type (Fun {head=_otype; args=[t2; t1]})
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* zeroo *)
  | Fun {head; args=[t1; t2]} when head = _zeroo ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type (Symbol sym1), Type (Symbol sym2) when sym1 = _ctype && sym2 = _ctype ->
        Type (Fun {head=_otype; args=[t1; t2]})
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as CType." (term2str s) (term2str t1) (term2str t2))
    end

  (* oneo *)
  | Fun {head; args=[t]} when head = _oneo ->
    begin
      match calc_type wfctx t with
      | Type (Symbol sym1) when sym1 = _ctype ->
        Type (Fun {head=_otype; args=[t; t]})
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end
  
  (* plus *)
  | Fun {head; args=[t1; t2]} when head = _plus ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          | Fun {head=head1; _}, _ when head1 = _otype && type_t1 = type_t2 ->
            Type type_t1
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s are not typed as QVList." (term2str s) (term2str t1) (term2str t2))
    end

  (* sum *)
  | Fun {head; args=[s'; f]} when head = _sum ->
    begin
      match calc_type wfctx f with
      | Type (Fun {head=head; args=[Symbol v; t; t']}) when head = _forall ->
        begin
          (* Check the set and input type*)
          match calc_type wfctx s', t with
          | Type (Fun {head=head1; args=[t1]}), Fun {head=head2; args=[t2]} when head1 = _set &&  head2 = _cterm && t1 = t2 ->
          begin
            (* check the type of the function *)
            match t' with
            | Symbol sym when sym = _stype -> 
                Type t'
            | Fun {head; _} when head = _ktype || head = _btype || head = _otype || head = _dtype ->
                Type t'
            | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not a function to SType, KType, BType, OType or DType." (term2str s) (term2str f))
          end
          | _ -> TypeError (Printf.sprintf "%s typing failed. set %s and index %s have inconsistent types." (term2str s) (term2str s') v)
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s must be typed as a function." (term2str s) (term2str f))
    end

  (* trace *)
  | Fun {head; args=[t]} when head = _tr ->
    begin
      match calc_type wfctx t with
      | Type (Fun {head=head; args=[t1; t2]}) when (head = _otype && t1 = t2) || head = _dtype ->
        Type (Symbol _stype)
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as OType or DType." (term2str s) (term2str t))
    end

  (* uset *)
  | Fun {head; args=[t]} when head = _uset ->
    begin
      match calc_type wfctx t with
      | Type (Symbol sym) when sym = _ctype ->
        Type (Fun {head=_set; args=[t]})
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CType." (term2str s) (term2str t))
    end

  
  (* subscript, opt pair*)
  | Fun {head; args=[t1; Fun {head=pair_head; args=[s1; s2]}]} when head = _subscript && pair_head = _pair->
    begin
      match calc_type wfctx t1, calc_type wfctx s1, calc_type wfctx s2 with
      | Type (Fun {head=head1; args=[tt1; tt2]}), 
        Type (Fun {head=head2; args=[tqreg1]}),
        Type (Fun {head=head3; args=[tqreg2]}) when
        (
          head1 = _otype &&
          head2 = _qreg &&
          head3 = _qreg &&
          tt1 = tqreg1 && tt2 = tqreg2
        ) ->
        begin
          match get_qvlist s1, get_qvlist s2 with
          | TermList qv1, TermList qv2 ->
            Type (Fun {head=_dtype; args=[
              Fun {head=_list; args=qv1};
              Fun {head=_list; args=qv2}
            ]})
          | _ -> TypeError (Printf.sprintf "%s typing failed. Cannot calculate quantum variable list of %s or %s." (term2str s) (term2str s1) (term2str s2))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end


  (* true *)
  | Symbol sym when sym = _true -> Type (Fun {head=_cterm; args=[Symbol _bit]})

  (* false *)
  | Symbol sym when sym = _false -> Type (Fun {head=_cterm; args=[Symbol _bit]})

  (* eqeq *)
  | Fun {head; args=[t1; t2]} when head = _eqeq ->
    begin
      match is_cterm wfctx t1 with
      | Type type_t1 ->
        begin
          match type_t1 with
          | Fun {head=head; args=[Symbol _]} when head = _cterm ->
            begin
              match is_cterm wfctx t2 with
              | Type type_t2 when type_t1 = type_t2 -> Type (Fun {head=_cterm; args=[Symbol _bit]})
              | Type _ -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type." (term2str s) (term2str t1) (term2str t2))
              | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s and %s do not have the same classical type. %s" (term2str s) (term2str t1) (term2str t2) msg)
            end
          | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm." (term2str s) (term2str t1))
        end
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t1) msg)
    end

  (* wedge *)
  | Fun {head; args=[t1; t2]} when head = _wedge ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          (* type conjunction *)
          | _ when type_t1 = Symbol _type && type_t2 = Symbol _type ->
            Type (Symbol _type)
          (* boolean conjunction *)
          | _ when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 ->
              Type (Fun {head=_cterm; args=[Symbol _bit]})
          (* cq-projector conjunction *)
          | _ when type_t1 = Symbol _cqproj && type_t2 = Symbol _cqproj ->
              Type (Symbol _cqproj) 


          (* otype projector conjunction *)
          | Fun {head=head1; _}, _ when head1 = _otype && type_t1 = type_t2 ->
            Type type_t1
            
          (* dtype projector conjunction *)
          | Fun {head=head1; args=[Fun{args=s1; _}; Fun{args=s2; _}]},
            Fun {head=head2; args=[Fun{args=s1'; _}; Fun{args=s2'; _}]} when head1 = _dtype && head2 = _dtype && s1 = s2 && s1' = s2' ->
              let new_s1 = list_union s1 s1' in
              let new_s2 = list_union s2 s2' in 
              Type (Fun{head=_dtype; 
                args=[
                  Fun{head=_list; args=new_s1};
                  Fun{head=_list; args=new_s2}]
              })

          | _ ->
              TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end
      
  (* vee *)
  | Fun {head; args=[t1; t2]} when head = _vee ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          if type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 then
            Type (Fun {head=_cterm; args=[Symbol _bit]})
          else match type_t1, type_t2 with

          (* otype projector conjunction *)
          | Fun {head=head1; _}, _ when head1 = _otype && type_t1 = type_t2 ->
            Type type_t1

          (* dtype projector conjunction *)
          | Fun {head=head1; args=[Fun{args=s1; _}; Fun{args=s2; _}]},
            Fun {head=head2; args=[Fun{args=s1'; _}; Fun{args=s2'; _}]} when head1 = _dtype && head2 = _dtype && s1 = s2 && s1' = s2' ->
              let new_s1 = list_union s1 s1' in
              let new_s2 = list_union s2 s2' in 
              Type (Fun{head=_dtype; 
                args=[
                  Fun{head=_list; args=new_s1};
                  Fun{head=_list; args=new_s2}]
              })
          | _ ->
            TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end

  (* not *)
  | Fun {head; args=[t]} when head = _not ->
    begin
      match calc_type wfctx t with
      | Type type_t ->
        begin
          if type_t = Fun {head=_cterm; args=[Symbol _bit]} then
            Type (Fun {head=_cterm; args=[Symbol _bit]})
          else
            TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit]." (term2str s) (term2str t))
        end
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t) msg)
    end
  
  (* imply *)
  | Fun {head; args=[t1; t2]} when head = _imply ->
      begin
        match calc_type wfctx t1, calc_type wfctx t2 with
        | Type type_t1, Type type_t2 ->
          begin
            match type_t1, type_t2 with
            (* boolean implication *)
            | _ when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && type_t2 = type_t1 ->
                Type (Fun {head=_cterm; args=[Symbol _bit]})
                
            (* Sasaki implication (OType) *)
            | Fun {head=head1; args=[tt1; tt2]}, Fun {head=head2; args=[tt1'; tt2']} when head1 = _otype && head2 = _otype && tt1=tt2 && tt1'=tt2' && tt1=tt1' ->
                Type (Fun {head=_otype; args=[tt1; tt1]})

            (* Sasaki implication (DType) *)
            | Fun {head=head1; args=[tt1; tt2]}, Fun {head=head2; args=[tt1'; tt2']} when head1 = _dtype && head2 = _dtype && tt1=tt2 && tt1'=tt2' && tt1=tt1' ->
                Type (Fun {head=_dtype; args=[tt1; tt1]})

            (* cq-projector *)
            | _, Fun {head=head2; _} when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && head2=_dtype ->
                Type (Symbol _cqproj)

            | _ ->
                TypeError (Printf.sprintf "%s typing failed." (term2str s))
          end
        | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
      end

  (* guarded quantum operator *)
  | Fun {head; args=[t1; t2]} when head = _guarded ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          | _, Fun {head=head2; _} when type_t1 = Fun {head=_cterm; args=[Symbol _bit]} && head2 = _dtype ->
            Type type_t2
          | _ -> TypeError (Printf.sprintf "%s typing failed. %s is not typed as CTerm[Bit] or %s is not typed as DType." (term2str s) (term2str t1) (term2str t2))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end

  (* atat: unitary transformation on projectors *)
  | Fun {head; args=[t1; t2]} when head = _atat ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with

          (* unitary transformation on ASSN *)
          | Fun {head=head1; _}, Symbol head2 when head1 = _dtype && head2 = _assn ->
            Type (Symbol _assn)
          
          (* unitary transformation on CQPROJ *)
          | Fun {head=head1; _}, Symbol head2 when head1 = _dtype && head2 = _cqproj ->
            Type (Symbol _cqproj)

          (* unitary transformation on DTYPE *)
          | Fun {head=head1; args=[Fun{args=ls1; _}; Fun{args=ls2; _}]; _}, 
            Fun {head=head2; args=[Fun{args=ls1'; _}; Fun{args=ls2'; _}]; _}
            when head1 = _dtype && head2 = _dtype ->
              (* calculate the type of new labelled Dirac notation *)
              let new_ls1 = (list_remove ls1' ls2) @ ls1 in
              let new_ls2 = (list_remove ls2' ls1) @ ls2 in
              Type (Fun {head=_dtype; args=[
                Fun {head=_list; args=new_ls1};
                Fun {head=_list; args=new_ls2}
              ]})
          | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end

  (* vbar (cq-assertion) *)
  | Fun {head; args=[t1; t2]} when head = _vbar ->
    (* (psi, A) pair of assn *)
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type Fun {head=head2; _} when 
        type_t1 = Symbol _cqproj && head2 = _dtype ->
          Type (Symbol _assn)
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* Eq *)
  | Fun {head; args=[t1; t2]} when head = _eq ->
    begin
      match calc_type wfctx t1 with
      | Type type_t1 ->
        begin
          match type_check wfctx t2 type_t1 with
          | Type _ -> Type (Symbol _type)
          | TypeError _ -> TypeError (Printf.sprintf "%s typing failed. Two sides don't have the same type." (term2str s))
        end
      | TypeError msg -> TypeError (Printf.sprintf "%s typing failed. %s is not well typed. %s" (term2str s) (term2str t1) msg)
    end

  (* inspace *)
  | Fun {head; args=[t1; t2]} when head = _inspace ->
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          (* otype *)
          | Fun {head=head1; _}, Fun {head=head2; _} when 
            head1 = _otype && head2 = _otype ->
              Type (Symbol _type)

          (* labelled dirac notation *)
          | Fun {head=head1; _}, Fun {head=head2; _} when 
            head1 = _dtype && head2 = _dtype ->
            Type (Symbol _type)

          | _ -> 
            TypeError (Printf.sprintf "%s typing failed." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed. %s or %s is not well typed." (term2str s) (term2str t1) (term2str t2))
    end


    
  (* Entailment *)
  | Fun {head; args=[t1; t2]} when head = _entailment -> 
    begin
      match calc_type wfctx t1, calc_type wfctx t2 with
      | Type type_t1, Type type_t2 ->
        begin
          match type_t1, type_t2 with
          (* cq-projector entailment *)
          | _ when type_t1 = Symbol _cqproj && type_t2 = Symbol _cqproj -> Type (Symbol _type)

          (* assertion entailment *)
          | _ when type_t1 = Symbol _assn && type_t2 = Symbol _assn ->
            Type (Symbol _type)

          (* operator entailment *)
          | Fun {head=head1; _}, Fun {head=head2; _} when head1=_dtype && head2=_dtype ->
            Type (Symbol _type)

          (* plain operator entailment *)
          | Fun {head=head1; args=[t1; t2]}, Fun {head=head2; args=[t1'; t2']} when
            head1 = _otype && head2 = _otype && t1 = t2 && t1 = t1' && t1' = t2' ->
              Type (Symbol _type)

          | _ -> 
            TypeError (Printf.sprintf "%s typing failed. Entailment should between two assertions." (term2str s))
        end
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end

  (* Judgement *)
  | Fun {head; args=[pre; s1; s2; post]} when head = _judgement ->
    begin
      match calc_type wfctx pre, calc_type wfctx s1, calc_type wfctx s2, calc_type wfctx post with
      | Type type_pre, Type type_s1, Type type_s2, Type type_post ->
        if type_pre = Symbol _assn && type_s1 = Symbol _prog && type_s2 = Symbol _prog && type_post = Symbol _assn then
          Type (Symbol _type)
        else
          TypeError (Printf.sprintf "%s typing failed." (term2str s))
      | _ -> TypeError (Printf.sprintf "%s typing failed." (term2str s))
    end
  
  (* Variable *)
  | Symbol x ->
    begin
      match find_item wfctx x with
      | Some (Assumption {name=_; t}) -> Type t
      | Some (Definition {name=_; t; e=_}) -> Type t
      | None -> TypeError (Printf.sprintf "The term %s is not defined or assumed." x)
    end

  (* default *)
  | _ -> TypeError (Printf.sprintf "Cannot calculate type of %s." (term2str s))

    


and type_check (wfctx : wf_ctx) (s : terms) (t : terms) : typing_result = 
  let calc_type_res = calc_type wfctx s in
  match calc_type_res with
  (* the same type *)
  | Type t' when t = t' -> Type t


  | Type t' -> 
      TypeError (Printf.sprintf "The term %s is not typed as %s, but %s." (term2str s) (term2str t) (term2str t'))
  | TypeError msg -> TypeError msg
  

and is_cterm (wfctx : wf_ctx) (s : terms) : typing_result =
  let calc_type_res = calc_type wfctx s in
  match calc_type_res with
  | Type (Fun {head; args=[t']}) when head = _cterm -> Type (Fun {head=_cterm; args=[t']})

  (* cvar is cterm *)
  | Type (Fun {head; args=[t']}) when head = _cvar -> Type (Fun {head=_cterm; args=[t']})

  | Type t' -> 
      TypeError (Printf.sprintf "The term %s is not typed as CTerm, but %s." (term2str s) (term2str t'))
  | TypeError msg -> TypeError msg
