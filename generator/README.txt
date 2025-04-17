(* Toplevel Language Syntax *)

(* This is the language for interation with the prover. User use commands to define the program, specify the correctness formula, and prove the correctness. *)

(* This is a comment block *)

(* The toplevel langauge follows the Rocq style. Every command ends with '.' *)

(* Type system for terms
    T ::= qvar                                          # single quantum system
        | qreg(n)                                       # quantum register, n is a positive number, representing the qubit number
        | opt(n)                                        # operators, n is a positive number, representing the qubit number
        | lopt                                          # labelled operators
        | assert                                        # assertion
        | prog                                          # program
        | judgement(assert, prog, prog, assert)         # judgement
        | judgeproof(judgement)                         # proof of judgement
*)

(* We have a global environment to maintain the definitions and variables. Variables in the program definitions should be well typed. 
    We only allow variables of qvar, opt(n), lopt, assert and prog types.
*)

Var q0, q1, q2 : qvar. (* Quantum variables *)
Def qr2 := [q1, q2]. (* Quantum register of 2 qubits *)
(* Var qr2 : qreg(2). it is not allowed *)

Var X : opt(1). (* Operators *)
Var CX : opt(2). (* Operators *)

Check X : opt(1). (* Check the type of X *)
Check X[q0] : lopt. (* Check the type of X[q0] *)
(* Check X[q0, q1] : lopt. type error, X is a 1-qubit operator. *)


(* Definition of Operators. The concrete syntax can be skipped for now. The type system for unitary/projective is also omitted. *)
Def P0 := |0><0|.
Def P1 := |1><1|.
Def I := P0 + P1.


(* The cqwhile language follows the C style. 
    Remark:
        1. All statements end with a semicolon. This will make the language easier to write.
        2. Sequential statements are encoded as a list of more than one statement, rather than using a tuple. This reduces redundant interpretations.

*)

Def subprog := 
    // This is a comment line for programs
    while P0[q0] do
        H[q0];
    end;

Var H : opt(1).
Var U : opt(2).
Var M1 : opt(1).
Var M2 : opt(1).

Def prog :=
    skip;
    q0 := |0>;
    q1 := |0>;
    U[q0, q1];
    H[q0];
    CX[q0, q2];

    // It's better to replace if statement with switch statement
    switch
        M1[q0]: 
            skip;
        M2[q0]: 
            U[q1, q0]; X[q2];
        ...
        Mn[q0]: // assume Mn and Sn are defined.
            Sn;
    end;

    while P0[q0] d0
        subprog;    // call the subprogram
    end;
    .

Def prog_judge := {P} S1 ~ S2 {Q}.

(* Use interactive commands to construct the proof *)
Prove prog_judge_proof : judgeproof(prog_judge).
    apply rule1.
    apply rule2.
    ....
Qed.