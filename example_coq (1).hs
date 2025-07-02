....


Section Goal1.

Definition P0 : 'Hom{Bool, Bool} := [> ''false ; ''false <].
Definition P1 : 'Hom{Bool, Bool} := [> ''true ; ''true <].
Definition Psym2 : 'Hom{Bool * Bool, Bool * Bool} :=
        [> ''(true, false) ; ''(false, true) <] +  
        [> ''(false, true) ; ''(true, false) <] +
        [> ''(true, true) ; ''(true, true) <] +
        [> ''(false, false) ; ''(false, false) <].
Hypothesis (Lemma1 : forall x : bool, ~~ (~~ x) = x).
Hypothesis (Lemma2 : forall x : bool, forall H : ~~ x = true, x = false).

Variable (x : bool).
Variable (x' : bool).
Variable (y : bool).
Variable (y' : bool).
Variable (q1 : qvart Bool).
Variable (q1' : qvart Bool).
Variable (q2 : qvart Bool).
Variable (q2' : qvart Bool).

Hypothesis (disq : qvar_dis [:: (q1 : qvar); (q1' : qvar); (q2 : qvar); (q2' : qvar)]).
Variable (U : 'Hom{Bool, Bool}).
Hypothesis (H : (~ (x == x')) = true).

Example :
forall (rho : 'Hom{Bool, Bool}), 
    (forall (pfspace : (0 : 'End{Bool}) \o rho = rho)),
        q_lifting
            ('[P0 ; 'q2, 'q2] \· \Tr_( 'q2' )( '[rho ; 'q1 , 'q1 ]) \· '[P0^A ; 'q2, 'q2])
                '[(\1 : 'End{Bool}) ; 'q1 , 'q1]
            ('[P0 ; 'q2' , 'q2'] \· \Tr_( 'q2 )( '[rho ; 'q1 , 'q1 ]) \· '[P0^A ; 'q2', 'q2']).
Proof. Abort.

End Goal1.

Example :
forall (pfbj' : ((~ (x == x')) = true)), 
forall (rho' : 'Hom{Bool, Bool}), let rho := '[rho ; 'q1 , 'q1] in
       q_lifting
            ('[P1 ; 'q2 , 'q2] \· \Tr_( 'q2' )(rho) \· '[P1^A ; 'q2 , 'q2])
                (guard_hspace ((~~ ((x == x') && (false == false))) ==> (~~ (~~ (x == x')))) ('[(0 : 'End{Bool}) ; 'q1 , 'q1])
                /\ guard_hspace ((~~ ((x == x') && (true == true))) ==> (~~ (~~ (x == x')))) ('[(0 : 'End{Bool}) ; 'q1 , 'q1]))
            ('[P1 ; 'q2' , 'q2'] \· \Tr_( 'q2 )(rho) \· '[P1^A ; 'q2' , 'q2']).



---------------------------------------
guard_hspace (x : bool) (DType)


---------------------------------------
rho : DType[[q1,q2,q3], [q1,q2,q3]]
===>  rho : 'Hom{Bool*Bool*Bool, Bool*Bool*Bool}
      rho' := '[rho ; (('q1,'q2),'q3) , (('q1,'q2),'q3)]


---------------------------------------
^D  --->  ^A


---------------------------------------
q1 : qvart Bool
q2 : qvart Bool

Psym2_((q1,q2) , (q1,q2)) <-- yingte's tool
'[Psym2 ; ('q1,'q2) , ('q1,'q2)]


'q1 : qreg Bool
('q1, 'q2) : qreg (Bool * Bool)

A_(p,q)  ->  '[A ; p , q]


---------------------------------------

rho \in (0 : 'End{Bool})
A \in B =====> B \o A = A

q_lifting
guard_hspace



A \in B =====> B \o A = A





==========================================
Environment: [
P0 := (|false> @ <false|) : OType[bit, bit]
P1 := (|true> @ <true|) : OType[bit, bit]
Psym2 := ((((|(true, false)> @ <(false, true)|) + (|(false, true)> @ <(true, false)|)) + (|(true, true)> @ <(true, true)|)) + (|(false, false)> @ <(false, false)|)) : OType[(bit * bit), (bit * bit)]
Lemma1 := <opaque> : (forall (x : CTerm[bit]), ((~ (~ x)) = x))
Lemma2 := <opaque> : (forall (x : CTerm[bit]), (forall (H : ((~ x) = true)), (x = false)))
]
Context: [
x : CVar[bit]
x' : CVar[bit]
y : CVar[bit]
y' : CVar[bit]
q1 : QReg[bit]
q1' : QReg[bit]
q2 : QReg[bit]
q2' : QReg[bit]

U : OType[bit, bit]
H : ((~ (x == x')) = true)
]
---------------------------------------------------------------
[Proof Mode]

[Goals]

(1/4) (forall (rho : OType[bit, bit]), (forall (pfspace : (rho \in 0O[bit])), (((P0_(q2, q2) @ tr_q2'(rho_(q1, q1))) @ (P0^D)_(q2, q2)), 1O[bit]_(q1, q1) #, ((P0_(q2', q2') @ tr_q2(rho_(q1, q1))) @ (P0^D)_(q2', q2')))))



(2/4) (forall (pfbj' : ((~ (x == x')) = true)), (forall (rho : DType[[q1], [q1]]), (forall (pfspace : (rho \in 0O[bit]_(q1, q1))), (((P1_(q2, q2) @ tr_q2'(rho)) @ (P1^D)_(q2, q2)), ((((~ ((x == x') /\ (false == false))) -> (~ (~ (x == x')))) |-> 0O[bit]_(q1, q1)) /\ (((~ ((x == x') /\ (true == true))) -> (~ (~ (x == x')))) |-> 0O[bit]_(q1, q1))) #, ((P1_(q2', q2') @ tr_q2(rho)) @ (P1^D)_(q2', q2'))))))