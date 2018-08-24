By Tom Schrijvers, August 2018.

> module Shin3 where
>
> import Prelude hiding (fail)

Syntax
======

V      ::= ... 		expressions of some type
CV, DV ::= ...		computation-valued expressions
EV     ::= ...		environment-valued expressions

C, D ::=                   computations
    | Return V
    | Fail
    | C || C
    | Get CV
    | Put V C

E,F ::= []		zippers
    | E ; || C
    | E ; C ||
    | E ; Put V
    | E ; Get_s

X, Y ::=  []            extended zippers
     | X ; || C
     | X ; C ||
     | X ; Put V
     | X ; Get_s
     | X ; >>= CV
     | X ; C >>=_x

G, H ::= []            top-down environments (reversal of zipper)o
     | G || C
     | C || G
     | Get GV
     | Put W G

Syntax Manipulation
===================

(>>=) :: C -> CV -> C
Return V >>= CV = CV V
Fail     >>= CV = Fail
(C || D) >>= CV = (C >>= CV) || (D >>= CV)
Get DV   >>= CV = Get (\s -> DV x >>= CV)
Put V C  >>= CV = Put V (C >>= CV)

apply : E -> C -> C

apply []           C = C
apply (E ; || D)   C = apply E (C || D)
apply (E ; D ||)   C = apply E (D || C)
apply (E ; Put V)  C = apply E (Put V C)
apply (E ; Get_s)  C = apply E (Get (\s -> C))

applyX : X -> C -> C

applyX []            C = C
applyX (X ; || D)    C = applyX X (C || D)
applyX (X ; D ||)    C = applyX X (D || C)
applyX (X ; Put V)   C = applyX X (Put V C)
applyX (X ; Get_s)   C = applyX X (Get (\s -> C))
applyX (X ; >>= CV)  C = applyX X (C >>= CV)
applyX (X ; D >>=_s) C = applyX X (D >>= \s -> C)

applyG : G -> C -> C

applyG []        C = C
applyG (G || D)  C = applyG G C || D
applyG (D || G)  C = D || apply G C
applyG (Put V G) C = Put V (applyG G C
applyG (Get GV)  C = Get (\s -> apply (GV s) C)

trans : C -> C

trans (Return V) = Return V
trans Fail       = Fail
trans (C || D)   = trans C || trans D
trans (Get CV)   = Get (\x -> trans (CV x))
trans (Put V C)  = Get (\s0 -> (Put V (trans C) || Put s0 Fail))

transE : E -> E

transE []           = []
transE (E ; || D)   = trans E ; || trans D
transE (E ; D ||)   = trans E ; trans D ||
transE (E ; Put V)  = ((trans E ; Get_s) ; || Put s Fail ) ; Put V
transE (E ; Get_s)  = trans E ; Get_s

Theorem trans_apply:
  forall C E,
    trans (apply E C)
    =
    apply (transE E) (trans C).
Proof.
  - case E = []
    trans (apply [] C)
 = (apply)
    trans C
 = (apply)
    apply [] (trans C)
 = (transE)
    apply (transE []) (trans C)

  - case E = E1 ; || D
    trans (apply (E1; || D) C)
 = (apply)
    trans (apply E1 (C || D))
 = (induction hypothesis)
    apply (transE E1) (trans (C || D))
 = (trans)
    apply (transE E1) (trans C || trans D)
 = (apply)
    apply (transE E1 ; || trans D) (trans C)
 = (transE)
    apply (transE (E1 ; || D)) (trans C)

  - case E = E1 ; D ||
    trans (apply (E1; D ||) C)
 = (apply)
    trans (apply E1 (D || C))
 = (induction hypothesis)
    apply (transE E1) (trans (D || C))
 = (trans)
    apply (transE E1) (trans D || trans C)
 = (apply)
    apply (transE E1 ; trans D ||) (trans C)
 = (transE)
    apply (transE (E1 ; D ||)) (trans C)

  - case E = E1 ; Put V
    trans (apply (E1; Put V) C)
 = (apply)
    trans (apply E1 (Put V C))
 = (induction hypothesis)
    apply (transE E1) (trans (Put V C))
 = (trans)
    apply (transE E1) (Get (\s -> Put V (trans C) || Put s Fail))
 = (apply)
    apply (((transE E1 ; Get_s) ; || Put s Fail) ; Put V) (trans C)
 = (transE)
    apply (transE (E1 ; Put V)) (trans C)

  - case E = E1 ; Get_s
    trans (apply (E1; Get_s) C)
 = (apply)
    trans (apply E1 (Get (\s -> C)))
 = (induction hypothesis)
    apply (transE E1) (trans (Get (\s -> C))s)
 = (trans)
    apply (transE E1) (Get (\s -> trans C))
 = (apply)
    apply (transE E1 ; Get_s) (trans C)
 = (transE)
    apply (transE (E1 ; Get_s)) (trans C)
Qed.

Given Semantics
===============

Dom  		semantic domain

run : C -> Dom

<&> : Dom -> Dom -> Dom

<||> : Dom -> Dom -> Dom

<get> : (V -> Dom) -> Dom

<put> : V -> Dom -> Dom

Law run_||:
  forall C D,
    run (C || D)
    =
    run C <||> run D

Law run_get:
  forall CV,
    run (Get CV)
    =
    <get> (\s -> run (CV s))

Law run_put:
  forall V C,
    run (Put V C)
    =
    <put> V (run C)


Law >>=_ret:
  forall E C,
    run (apply E (C >>= Return))
    =
    run (apply E C)

Law >>=_>>=:
  forall E C CV DV,
    run (apply E ((C >>= CV) >>= DV))
    =
    run (apply E (C >>= \x -> (CV x >>= DV)))

Law fail_||:
  forall E C,
    run (apply E (Fail || C))
    =
    run (apply E C)

Law ||_fail:
  forall E C,
    run (apply E (C || Fail))
    =
    run (apply E C)

Law ||_||:
  forall E C1 C2 C3,
    run (apply E ((C1 || C2) || C3))
    =
    run (apply E (C1 || (C2 || C3)))

Law fail_>>=:
  forall E CV,
    run (apply E (Fail >>= CV))
    =
    run (apply E Fail)


Law get_get_G:
  forall E k,
    run (apply E (Get (\s1 -> Get (\s2 -> k s1 s2))))
    =
    run (apply E (Get (\s1 -> k s1 s2)))

Law get_put_G:
  forall E C,
    run (apply E (Get (\s -> Put s C)))
    =
    run (apply E C)

Law put_get_G:
  forall E V k,
    run (apply E (Put V (Get k)))
    =
    run (apply E (Put V (k V)))

Law put_put_G:
  forall E V W C,
    run (apply E (Put V (Put W C)))
    =
    run (apply E (Put W C))

Law put_||_G:
  forall E V C D,
    run (apply E (Put V C || D))
    =
    run (apply E (Put V (C || D)))

Law get_||:
  forall E CV D,
    run (apply E ((Get >>= CV) || D))
    =
    run (apply E (Get >>= \x -> CV x || D))


Law put_ret_||_G:
  forall V W C,
    run (Put V (Return W || C))
    =
    run (Put V (Return W)) <&> run (Put V C)

Wanted Semantics
================

eval : C -> Dom

eval = run . trans

Lemma Meta1:
  forall C D C1,
    (P: forall E CV, eval (apply E (C >>= CV) = eval (apply E (D >>= CV))))
     ->
    (forall E CV, eval (apply E ((C1 >>= \x -> C) >>= CV)) = eval (apply E ((C1 >>= \x -> D) >>= CV)))
Proof:
  - case C1 = Return V
    eval (apply E ((Return V >>= C) >>= CV))
 = (>>=)
    eval (apply E (C[V/x] >>= CV)
 = (P E CV)
    eval (apply E (D[V/x] >>= CV))
 = (>>=)
    eval (apply E ((Return V >>= \x -> D)) >>= CV)

  - case C1 = Fail
    eval (apply E ((Fail >>= \x -> C) >>= CV))
 = (>>=_>>=)
    eval (apply E (Fail >>= \x -> (C >>= CV)))
 = (fail_>>=)
    eval (apply E Fail)
 = (fail_>>=)
    eval (apply E (Fail >>= (\x -> D >>= CV)))
 = (>>=_>>=)
    eval (apply E ((Fail >>= \x -> D) >>= CV))

  - case C1 = C11 || C12
    eval (apply E (((C11 || C12) >>= \x -> C) >>= CV))
 = (>>=_>>=)
    eval (apply E ((C11 || C12) >>= \x -> (C >>= CV)))
 = (>>=)
    eval (apply E (C11 >>= \x -> (C >>= CV) || C12 >>= \x -> (C >>= CV)))
 = (apply)
    eval (apply (E ; (C11 >>= \x -> (C >>= CV)) ||)  (C12 >>= \x -> (C >>= CV))))
 = (>>=_>>=)
    eval (apply (E ; (C11 >>= \x -> (C >>= CV)) ||)  ((C12 >>= \x -> C) >>= CV))
 = (induction hypothesis)
    eval (apply (E ; (C11 >>= \x -> (C >>= CV)) ||)  ((C12 >>= \x -> D) >>= CV))
 = (apply)
    eval (apply E (C11 >>= \x -> (C >>= CV) ||  (C12 >>= \x -> D) >>= CV))
 = (apply)
    eval (apply (E ; || (C12 >>= \x -> D) >>= CV) (C11 >>= \x -> (C >>= CV)))
 = (>>=_>>=)
    eval (apply (E ; || (C12 >>= \x -> D) >>= CV) ((C11 >>= \x -> C) >>= CV))
 = (induction hypothesis)
    eval (apply (E ; || (C12 >>= \x -> D) >>= CV) ((C11 >>= \x -> D) >>= CV))
 = (apply)
    eval (apply E ((C11 >>= \x -> D) >>= CV || (C12 >>= \x -> D) >>= CV)))
 = (>>=)
    eval (apply E ((C11 >>= \x -> D || C12 >>= \x -> D) >>= CV))
 = (>>=)
    eval (apply E (((C11 || C12) >>= \x -> D) >>= CV))

  - case C1 = Put V C11
    eval (apply E ((Put V C11 >>= \x -> C) >>= CV))
 = (>>=_>>=)
    eval (apply E (Put V C11 >>= \x -> (C >>= CV)))
 = (>>=)
    eval (apply E (Put V (C11 >>= \x -> (C >>= CV))))
 = (apply)
    eval (apply (E ; Put V) (C11 >>= \x -> (C >>= CV)))
 = (>>=_>>=)
    eval (apply (E ; Put V) ((C11 >>= \x -> C )>>= CV))
 = (induction hypothesis)
    eval (apply (E ; Put V) ((C11 >>= \x -> D) >>= CV))
 = (>>=_>>=)
    eval (apply (E ; Put V) (C11 >>= \x -> (D >>= CV)))
 = (apply)
    eval (apply E (Put V (C11 >>= \x -> (D >>= CV))))
 = (>>=)
    eval (apply E (Put V C11 >>= \x -> (D >>= CV)))
 = (>>=_>>=)
    eval (apply E ((Put V C11 >>= \x -> D) >>= CV))

  - case C1 = Get (\y -> C11)
    eval (apply E ((Get (\y -> C11) >>= \x -> C) >>= CV))
 = (>>=_>>=)
    eval (apply E (Get (\y -> C11) >>= \x -> (C >>= CV)))
 = (>>=)
    eval (apply E (Get (\y -> (C11 >>= \x -> (C >>= CV)))))
 = (apply)
    eval (apply (E ; Get_y) (C11 >>= \x -> (C >>= CV)))
 = (>>=_>>=)
    eval (apply (E ; Get_y) ((C11 >>= \x -> C )>>= CV))
 = (induction hypothesis)
    eval (apply (E ; Get_y) ((C11 >>= \x -> D) >>= CV))
 = (>>=_>>=)
    eval (apply (E ; Get_y) (C11 >>= \x -> (D >>= CV)))
 = (apply)
    eval (apply E (Get (\y -> (C11 >>= \x -> (D >>= CV)))))
 = (>>=)
    eval (apply E (Get (\y -> C11) >>= \x -> (D >>= CV)))
 = (>>=_>>=)
    eval (apply E ((Get (\y -> C11) >>= \x -> D) >>= CV))
Qed.


Lemma Meta2:
  forall C D,
    (P: forall E CV, eval (apply E (C >>= CV) = eval (apply E (D >>= CV))))
     ->
    (forall X, eval (applyX X C) = eval (applyX X D))
Proof:
  - case X = []
    eval (applyX [] C)
 = (applyX)
    eval C
 = (apply)
    eval (apply [] C)
 = (>>=_ret)
    eval(C >>= Return)
 = (apply)
    eval (apply [] (C >>= Return))
 = (P [] Return)
    eval (apply [] (D >>= Return))
 = (>>=_ret)
    eval (apply [] D)
 = (apply)
    eval D
 = (applyX)
    eval (applyX [] D)

  - case X = X1 ; || D1
    eval (applyX (X1 ; || D1) C)
 = (applyX)
    eval (applyX X1 (C || D1))
 = (induction hypothesis (C || D1) (D || D1) P' --- see below)
    eval (applyX X1 (D || D1))
 = (applyX)
    eval (applyX (X1 ; || D1) D)

     where
       P' : forall E CV, eval (apply E ((C || D1) >>= CV)) = eval (apply E ((D || D1) >>= CV))
       Proof:
           eval (apply E ((C || D1) >>= CV))
        = (>>=)
           eval (apply E ((C >>= CV) || (D1 >>= CV)))
        = (apply)
           eval (apply (E ; || (D1 >>= CV)) (C >>= CV))
        = (P (E ; || (D1 >>= CV)) CV)
           eval (apply (E ; || (D1 >>= CV)) (D >>= CV))
        = (apply)
           eval (apply E ((D >>= CV) || (D1 >>= CV)))
        = (>>=)
           eval (apply E ((D || D1) >>= CV))
       Qed.

  - case X = X1 ; D1 ||
    eval (applyX (X1 ; D1 ||) C)
 = (applyX)
    eval (applyX X1 (D1 || C))
 = (induction hypothesis (D1 || C) (D1 || D)  P' --- see below)
    eval (applyX X1 (D1 || D))
 = (applyX)
    eval (applyX (X1 ; D1 ||) D)

     where
       P' : forall E CV, eval (apply E ((D1 || C) >>= CV)) = eval (apply E ((D1 || D) >>= CV))
       Proof:
           eval (apply E ((D1 || C) >>= CV))
        = (>>=)
           eval (apply E ((D1 >>= CV) || (C >>= CV)))
        = (apply)
           eval (apply (E ; (D1 >>= CV) || ) (C >>= CV))
        = (P (E ; (D1 >>= CV) || ) CV )
           eval (apply (E ; (D1 >>= CV) || ) (D >>= CV))
        = (apply)
           eval (apply E ((D1 >>= CV) || (D >>= CV)))
        = (>>=)
           eval (apply E ((D1 || D) >>= CV))
       Qed.

  - case X = X1 ; Put V
    eval (applyX (X1 ; Put V) C)
 = (applyX)
    eval (applyX X1 (Put V C))
 = (induction hypothesis (Put V C) (Put V D)  P' --- see below)
    eval (applyX X1 (Put V D))
 = (applyX)
    eval (applyX (X1 ; Put V) D)

     where
       P' : forall E CV, eval (apply E (Put V C >>= CV)) = eval (apply E (Put V D >>= CV))
       Proof:
           eval (apply E (Put V C >>= CV))
        = (>>=)
           eval (apply E (Put V (C >>= CV)))
        = (apply)
           eval (apply (E ; Put V) (C >>= CV))
        = (P (E ; Put V) CV)
           eval (apply (E ; Put V) (D >>= CV))
        = (apply)
           eval (apply E (Put V (D >>= CV)))
        = (>>=)
           eval (apply E (Put V D >>= CV))
       Qed.

  - case X = X1 ; Get_s
    eval (applyX (X1 ; Get_s) C)
 = (applyX)
    eval (applyX X1 (Get (\s -> C))
 = (induction hypothesis (Get (\s -> C) (Get (\s -> D))  P' --- see below)
    eval (applyX X1 (Get (\s -> D)))
 = (applyX)
    eval (applyX (X1 ; Get_s) D)

     where
       P' : forall E CV, eval (apply E (Get (\s ->  C) >>= CV)) = eval (apply E (Get (\s -> D) >>= CV))
       Proof:
           eval (apply E (Get (\s -> C) >>= CV))
        = (>>=)
           eval (apply E (Get (\s -> C >>= CV)))
        = (apply)
           eval (apply (E ; Get_s) (C >>= CV))
        = (P (E ; Get_s) CV)
           eval (apply (E ; Get_s) (D >>= CV))
        = (apply)
           eval (apply E (Get (\s -> D >>= CV)))
        = (>>=)
           eval (apply E (Get (\s -> D) >>= CV))
       Qed.


  - case X = X1 ; >>= CV1
    eval (applyX (X1 ; >>= CV1) C)
 = (applyX)
    eval (applyX X1 (C >>= CV1))
 = (induction hypothesis C D P' --- see below)
    eval (applyX X1 (D >>= CV1))
 = (applyX)
    eval (applyX (X1 ; >>= CV1))

     where
       P' : forall E CV, eval (apply E ((C >>= CV1) >>= CV)) = eval (apply E ((D >>= CV1) >>= CV))
       Proof:
           eval (apply E ((C >>= CV1) >>= CV))
        = (>>=_>>=)
           eval (apply E (C >>= (\x -> CV1 x >>= CV)))
        = (P E (\x -> CV1 x >>= CV))
           eval (apply E (D >>= (\x -> CV1 x >>= CV)))
        = (>>=_>>=)
           eval (apply E ((D >>= CV1) >>= CV))
       Qed.

  - case X = X1 ; C1 >>=_x
    eval (applyX (X1 ; C1 >>=_x) C)
 = (applyX)
    eval (applyX X1 (C1 >>= \x -> C))
 = (induction hypothesis with P')
    eval (applyX X1 (C1 >>= \x -> D))
 = (applyX)
    eval (applyX (X1 ; C1 >>=_x) D)

     where
       P' : forall E CV, eval (apply E ((C1 >>= \x -> C) >>= CV)) = eval (apply E ((C1 >>= \x -> D) >>= CV))
     Proof.
         eval (apply E ((C1 >>= \x -> C) >>= CV))
      = (Meta1 C D P)
         eval (apply E ((C1 >>= \x -> D) >>= CV))
     Qed.
Qed.

Lemma get_get_L_1:
  forall E k,
    eval (apply E (Get (\s1 -> Get (\s2 -> k s1 s2))))
    =
    eval (apply E (Get (\s1 -> k s1 s2)))
Proof:
    eval (apply E (Get (\s1 -> Get (\s2 -> k s1 s2))))
 = (eval)
    run (trans (apply E (Get (\s1 -> Get (\s2 -> k s1 s2)))))
 = (trans_apply)
    run (apply (transE E) (trans (Get (\s1 -> Get (\s2 -> k s1 s2)))))
 = (trans)
    run (apply (transE E) (trans (Get (\s1 -> Get (\s2 -> trans (k s1 s2))))))
 = (get_get_G)
    run (apply (transE E) (Get (\s1 -> trans (k s1 s1))))
 = (trans)
    run (apply (transE E) (trans (Get (\s1 -> k s1 s1))))
 = (trans_apply)
    run (trans (apply E (trans (Get (\s1 -> k s1 s1)))))
 = (eval)
    eval (apply E (trans (Get (\s1 -> k s1 s1))))
Qed.

Lemma get_get_L_2:
  forall E k CV,
    eval (apply E (Get (\s1 -> Get (\s2 -> k s1 s2)) >>= CV))
    =
    eval (apply E (Get (\s1 -> k s1 s2) >>= CV))
Proof:
    eval (apply E (Get (\s1 -> Get (\s2 -> k s1 s2)) >>= CV))
 = (>>=)
    eval (apply E (Get (\s1 -> Get (\s2 -> k s1 s2 >>= CV))))
 = (get_get_L_1)
    eval (apply E (Get (\s1 -> k s1 s2 >>= CV)))
 = (>>=)
    eval (apply E (Get (\s1 -> k s1 s2) >>= CV))
Qed.

Lemma put_get_L_1:
  forall E V CV,
    eval (apply E (Put V (Get CV)))
    =
    eval (apply E (Put V (CV V)))
Proof:
    eval (apply E (Put V (Get CV)))
 = (eval,trans_apply)
    run (apply (transE E) (trans (Put V (Get CV))))
 = (trans)
    run (apply (transE E) (Get (\s -> (Put V (Get (\s' -> trans (CV s'))) || Put s Fail))))
 = (put_get_G)
    run (apply (transE E) (Get (\s -> (Put V (trans (CV V)) || Put s Fail)))))
 = (trans)
    run (apply (transE E) (trans (Put V (CV V))))
 = (trans_apply,eval)
 = (eval)
    eval (apply E (Put V (CV V)))
Qed.

Lemma put_get_L_2:
  forall E V k CV,
    eval (apply E (Put V (Get k) >>= CV))
    =
    eval (apply E (Put V (k V) >>= CV))
Proof:
    eval (apply E (Put V (Get k) >>= CV))
 = (>>=)
    eval (apply E (Put V (Get (\s -> k s >>= CV))))
 = (put_get_L_1)
    eval (apply E (Put V (k V >>= CV)))
 = (>>=)
    eval (apply E (Put V (k V) >>= CV))
Qed.

Lemma get_put_L_1:
  forall E C,
    eval (apply E (Get (\s -> Put s C))) -- where s is not free in C
    =
    eval (apply E C)
Proof
    eval (apply E (Get (\s -> Put s C)))
 = (eval)
    run (trans (apply E (Get (\s -> Put s C))))
 = (trans_apply)
    run (apply (transE E) (trans (Get (\s -> Put s C))))
 = (trans)
    run (apply (transE E) (Get (\s -> Get (\s' -> Put s (tarns C) || Put s' Fail))))
 = (get_get_G)
    run (apply (transE E) (Get (\s -> Put s (tarns C) || Put s Fail)))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put s (trans C || Put s Fail))))
 = (get_put_G)
    run (apply (transE E) (Get (\s -> Put s (trans C || Put s Fail))))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put s (trans C) || Put s Fail)))
 = (apply)
    run (apply (transE E ; Get_s) (Put s (trans C) || Put s Fail))
 = (aux)
    run (apply (transE E ; Get_s) (Put s (trans C || Fail)))
 = (||_fail)
    run (apply (transE E ; Get_s) (Put s (trans C)))
 = (apply)
    run (apply (transE E) (Get (\s -> Put s (trans C))))
 = (get_put_G)
    run (apply (transE E) (trans C))
 = (trans_apply)
    run (trans (apply E C))
 = (eval)
    eval (apply E C)
Qed.

Lemma get_put_L_2:
  forall E C CV,
    eval (apply E (Get (\s -> Put s C) >>= CV)) -- where s is not free in C
    =
    eval (apply E (C >>= CV))
Proof
    eval (apply E (Get (\s -> Put s C) >>= CV))
 = (>>=)
    eval (apply E (Get (\s -> Put s (C >>= CV))))
 = (get_put_L_1)
    eval (apply E (C >>= CV))
Qed.

Lemma put_put_L_1:
  forall E V W C,
    eval (apply E (Put V (Put W C)))
    =
    eval (apply E (Put W C))
Proof.
    eval (apply E (Put V (Put W C)))
 = (eval)
    run (trans (apply E (Put V (Put W C)))
 = (trans_apply)
    run (apply (transE E) (trans (Put V (Put W C))))
 = (trans)
    run (apply (transE E) (Get (\s -> Put V (Get (\s' -> Put W (trans C) || Put s' Fail)) || Put s Fail)))
 = (put_get_G)
    run (apply (transE E) (Get (\s -> Put V (Put W (trans C) || Put V Fail) || Put s Fail)))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put V ((Put W (trans C) || Put V Fail) || Put s Fail))))
 = (||_||)
    run (apply (transE E) (Get (\s -> Put V (Put W (trans C) || (Put V Fail || Put s Fail)))))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put V (Put W (trans C) || Put V (Fail || Put s Fail)))))
 = (fail_||)
    run (apply (transE E) (Get (\s -> Put V (Put W (trans C) || Put V (Put s Fail)))))
 = (put_put_G)
    run (apply (transE E) (Get (\s -> Put V (Put W (trans C) || Put s Fail))))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put V (Put W (trans C || Put s Fail)))))
 = (put_put_G)
    run (apply (transE E) (Get (\s -> Put W (trans C || Put s Fail))))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put W (trans C) || Put s Fail)))
 = (trans)
    run (apply (transE E) (trans (Put W C)))
 = (trans_apply)
    run (trans (apply E (Put W C)))
 = (eval)
    eval (apply E (Put W C))
Qed.

Lemma put_put_L_2:
  forall E V W C CV,
    eval (apply E (Put V (Put W C) >>= CV))
    =
    eval (apply E (Put W C >>= CV))
Proof.
    eval (apply E (Put V (Put W C) >>= CV))
 = (>>=)
    eval (apply E (Put V (Put W (C >>= CV))))
 = (put_put_L_1)
    eval (apply E (Put W (C >>= CV)))
 = (>>=)
    eval (apply E (Put W C >>= CV))
Qed.

Lemma put_fail_L_1:
  forall E V,
    eval (apply E (Put V Fail))
    =
    eval (apply E Fail)
Proof.
    eval (apply E (Put V Fail))
 = (eval)
    run (trans (apply E (Put V Fail)))
 = (trans_apply)
    run (apply (transE E) (trans (Put V Fail)))
 = (trans)
    run (apply (transE E) (Get (\s -> Put V Fail || Put s Fail)))
 = (put_||_G)
    run (apply (transE E) (Get (\s -> Put V (Fail || Put s Fail))))
 = (fail_||)
    run (apply (transE E) (Get (\s -> Put V (Put s Fail))))
 = (put_put_G)
    run (apply (transE E) (Get (\s -> Put s Fail)))
 = (get_put_G)
    run (apply (transE E) Fail)
 = (trans)
    run (apply (transE E) (trans Fail))
 = (trans_apply)
    run (trans (apply E Fail))
 = (eval)
    eval (apply E Fail)
Qed.

Lemma put_fail_L_2:
  forall E V CV,
    eval (apply E (Put V Fail >>= CV))
    =
    eval (apply E (Fail >>= CV))
Proof.
    eval (apply E (Put V Fail >>= CV))
 = (>>=)
    eval (apply E (Put V Fail))
 = (put_fail_L_1)
    eval (apply E Fail)
 = (>>=)
    eval (apply E (Fail >>= CV))
Qed.

Lemma put_||_L_1:
  forall E V C D,
    eval (apply E (Put V C || Put V D))
    =
    eval (apply E (Put V (C || D)))
Proof.
    eval (apply E ((Put V C) || (Put V D)))
 = (eval)
    run (trans (apply E ((Put V C) || (Put V D))))
 = (trans_apply)
    run (apply (transE E) (trans (Put V C || Put V D)))
 = (trans)
    run (apply (transE E) (Get (\s -> Put V (trans C) || Put s Fail) || Get (\s' -> Put V (trans D) || Put s' Fail)))
 = (get_||)
    run (apply (transE E) (Get (\s -> (Put V (trans C) || Put s Fail) || Get (\s' -> Put V (trans D) || Put s' Fail))))
 = (||_||)
    run (apply (transE E) (Get (\s -> Put V (trans C) || (Put s Fail || Get (\s' -> Put V (trans D) || Put s' Fail)))))
 = (put_||_G))
    run (apply (transE E) (Get (\s -> Put V (trans C) || Put s (Fail || Get (\s' -> Put V (trans D) || Put s' Fail)))))
 = (fail_||)
    run (apply (transE E) (Get (\s -> Put V (trans C) || Put s (Get (\s' -> Put V (trans D) || Put s' Fail)))))
 = (put_get_G)
    run (apply (transE E) (Get (\s -> Put V (trans C) || Put s (Put V (trans D) || Put s Fail))))
 = (put_put_G)
    run (apply (transE E) (Get (\s -> Put V (trans C) || (Put V (trans D) || Put s Fail))))
 = (||_||)
    run (apply (transE E) (Get (\s -> (Put V (trans C) || Put V (trans D)) || Put s Fail)))
 = (apply)
    run (apply ((transE E ; || Put s Fail) ; Get_s) (Put V (trans C) || Put V (trans D)))
 = (aux)
    run (apply ((transE E ; || Put s Fail) ; Get_s) (Put V (trans C || trans D)))
 = (apply)
    run (apply (transE E) (Get (\s -> (Put V (trans C || trans D)) || Put s Fail)))
 = (trans)
    run (apply (transE E) (trans (Put V (C || D))))
 = (trans_apply)
    run (trans (apply E (Put V (C || D))))
 = (eval)
    eval (apply E (Put V (C || D)))
Qed.

Lemma put_||_L_2:
  forall E V C D CV,
    eval (apply E ((Put V C || Put V D) >>= CV))
    =
    eval (apply E (Put V (C || D) >>= CV))
Proof.
    eval (apply E ((Put V C || Put V D) >>= CV))
 = (>>=)
    eval (apply E (Put V (C >>= CV) || Put V (D >>= CV)))
 = (put_||_L_1)
    eval (apply E (Put V (C >>= CV || D >>= CV)))
 = (>>=)
    eval (apply E (Put V (C || D) >>= CV))
Qed.

Lemma aux:
  forall
    run (apply E (Put V (trans C || D)))
    =
    run (apply E (Put V (trans C) || Put V D))
Proof:
   - case C = Return W

    run (apply E (Put V (trans (Return W) || D)))
= (trans)
    run (apply E (Put V (Return W || D)))
= (exists G. apply E = applyG G)
    run (applyG G (Put V (Return W || D)))

    * case G = []
    run (applyG [] (Put V (Return W || D)))
 = (applyG)
    run (Put V (Return W || D))
 = (put_ret_||_G)
    run (Put V (Return W)) <&> run (Put V D)
 = (put_put_G)
    run (Put V (Return W)) <&> run (Put V (Put V D))
 = (put_ret_||_G)
    run (Put V (Return W || Put V D))
 = (put_put_G)
    run (Put V (Return W) || Put V D)
 = (trans)
    run (Put V (trans (Return W)) || Put V D)
 = (applyG)
    run (applyG []  (Put V (trans (Return W)) || Put V D))
 = (applyG [] = apply E)
    run (apply E (Put V (Return W) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Return W)) || Put V D))

    * case G = C1 || G1
    run (applyG (C1 || G1) (Put V (Return W || D)))
 = (applyG)
    run (C1 || applyG G1 (Put V (Return W || D)))
 = (run_||)
    run C1 <||> run (applyG G1 (Put V (Return W || D)))
 = (induction hypothesis)
    run C1 <||> run (applyG G1 (Put V (Return W) || Put V D))
 = (run_||)
    run (C1 || applyG G1 (Put V (Return W) || Put V D))
 = (applyG)
    run (applyG (C1 || G1) (Put V (Return W) || Put V D))
 = (applyG (C1 || G1) = apply E)
    run (apply E (Put V (Return W) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Return W)) || Put V D))

    * case G = G1 || C1
    run (applyG (G1 || C1) (Put V (Return W || D)))
 = (applyG)
    run (applyG G1 (Put V (Return W || D)) || C1)
 = (run_||)
    run (applyG G1 (Put V (Return W || D))) <||> run C1
 = (induction hypothesis)
    run (applyG G1 (Put V (Return W) || Put V D)) <||> run C1
 = (run_||)
    run (applyG G1 (Put V (Return W) || Put V D) || C1)
 = (applyG)
    run (applyG (G1 || C1) (Put V (Return W) || Put V D))
 = (applyG (G1 || C1) = apply E)
    run (apply E (Put V (Return W) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Return W)) || Put V D))

    * case G = Get GV1
    run (applyG (Get GV1) (Put V (Return W || D)))
 = (applyG)
    run (Get (\s -> applyG (GV1 s) (Put V (Return W || D))))
 = (run_get)
    <get> (\s -> run (applyG (GV1 s) (Put V (Return W || D))))
 = (induction hypothesis)
    <get> (\s -> run (applyG (GV1 s) (Put V (Return W) || Put V D)))
 = (run_get)
    run (Get (\s -> applyG (GV1 s) (Put V (Return W) || Put V D)))
 = (applyG)
    run (applyG (Get GV1) (Put V (Return W) || Put V D))
 = (applyG (Get GV1) = apply E)
    run (apply E (Put V (Return W) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Return W)) || Put V D))

    * case G = Put V1 G1
    run (applyG (Put V1 G1) (Put V (Return W || D)))
 = (applyG)
    run (Put V1 (applyG G1 (Put V (Return W || D))))
 = (run_put)
    <put> V1 (run (applyG G1 (Put V (Return W || D))))
 = (induction hypothesis)
    <put> V1 (run (applyG G1 (Put V (Return W) || Put V D)))
 = (run_put)
    run (Put V1 (applyG G1 (Put V (Return W) || Put V D)))
 = (applyG)
    run (applyG (Put V1 G1) (Put V (Return W) || Put V D))
 = (applyG (Put V1 G1) = apply E)
    run (apply E (Put V (Return W) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Return W)) || Put V D))

   - case C = Fail
    run (apply E (Put V (trans Fail || D)))
 = (trans)
    run (apply E (Put V (Fail || D)))
 = (fail_||)
    run (apply E (Put V D))
 = (put_put_G)
    run (apply E (Put V (Put V D)))
 = (fail_||)
    run (apply E (Put V (Fail || Put V D)))
 = (trans)
    run (apply E (Put V (trans Fail || Put V D)))
 = (put_||_G)
    run (apply E (Put V (trans Fail) || Put V D))

   - case C = (C1 || C2)
    run (apply E (Put V (trans (C1 || C2) || D)))
 = (trans)
    run (apply E (Put V ((trans C1 || trans C2) || D)))
 = (||_||)
    run (apply E (Put V (trans C1 || (trans C2 || D))))
 = (induction hypothesis)
    run (apply E (Put V (trans C1) || Put V (trans C2 || D)))
 = (apply)
    run (apply (E ; Put V (trans C1) ||) (Put V (trans C2 || D)))
 = (induction hypothesis)
    run (apply (E ; Put V (trans C1) ||) (Put V (trans C2) || Put V D))
 = (apply)
    run (apply E (Put V (trans C1) || (Put V (trans C2) || Put V D)))
 = (||_||)
    run (apply E ((Put V (trans C1) || Put V (trans C2)) || Put V D))
 = (apply)
    run (apply (E ; || Put V D) (Put V (trans C1) || Put V (trans C2)))
 = (induction hypothesis)
    run (apply (E ; || Put V D) (Put V (trans C1 || trans C2)))
 = (apply)
    run (apply E (Put V (trans C1 || trans C2) || Put V D))
 = (trans)
    run (apply E (Put V (trans (C1 || C2)) || Put V D))

   - case C = Get CV1
    run (apply E (Put V (trans (Get CV) || D)))
 = (trans)
    run (apply E (Put V (Get (\s -> trans (CV s)) || D)))
 = (put_||_G)
    run (apply E (Put V (Get (\s -> trans (CV s))) || D))
 = (put_get_G)
    run (apply E (Put V (trans (CV V)) || D))
 = (put_||_G)
    run (apply E (Put V (trans (CV V) || D)))
 = (induction hypothesis)
    run (apply E (Put V (trans (CV V)) || Put V D))
 = (put_get_G)
    run (apply E (Put V (Get (\s -> trans (CV s))) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Get CV)) || Put V D))

   - case C = Put W C1
    run (apply E (Put V (trans (Put W C1) || D)))
 = (trans)
    run (apply E (Put V (Get (\s -> Put W (trans C1) || Put s Fail) || D)))
 = (put_||_G)
    run (apply E (Put V (Get (\s -> Put W (trans C1) || Put s Fail)) || D))
 = (put_get_G)
    run (apply E (Put V (Put W (trans C1) || Put V Fail) || D))
 = (put_||_G)
    run (apply E (Put V ((Put W (trans C1) || Put V Fail) || D)))
 = (||_||)
    run (apply E (Put V (Put W (trans C1) || (Put V Fail || D))))
 = (put_||_G)
    run (apply E (Put V (Put W (trans C1) || (Put V (Fail || D)))))
 = (fail_||)
    run (apply E (Put V (Put W (trans C1) || (Put V D))))
 = (put_put_G)
    run (apply E (Put V (Put W (trans C1) || (Put V (Put V D)))))
 = (fail_||)
    run (apply E (Put V (Put W (trans C1) || (Put V (Fail || Put V D)))))
 = (put_||_G)
    run (apply E (Put V (Put W (trans C1) || (Put V Fail || Put V D))))
 = (||_||)
    run (apply E (Put V ((Put W (trans C1) || Put V Fail) || Put V D)))
 = (put_||_G)
    run (apply E (Put V (Put W (trans C1) || Put V Fail) || Put V D))
 = (put_get_G)
    run (apply E (Put V (Get (\s -> Put W (trans C1) || Put s Fail)) || Put V D))
 = (trans)
    run (apply E (Put V (trans (Put W C1)) || Put V D))
Qed.

Implementation of Global State
==============================

> type M s a = s -> ([(a,s)],s)

> fail :: M s a
> fail = \s -> ([],s)

> ret :: a -> M s a
> ret x = \s -> ([(x,s)],s)

> get' :: (s -> M s a) -> M s a
> get' k = \s -> k s s

> put' :: s -> M s a -> M s a
> put' s k = \_ -> k s

> get :: M s s
> get = get' ret

> put :: s -> M s ()
> put s = put' s (ret ())

> (<||>) :: M s a -> M s a -> M s a
> p <||> q = \s0 -> let (xs,s1) = p s0
>                       (ys,s2) = p s1
>                   in (xs ++ ys, s2)

> (<&>) :: M s a -> M s a -> M s a
> p <&> q = \s0 -> let (xs,s1) = p s0
>                      (ys,s2) = p s0
>                   in (xs ++ ys, s2)

> data Prog s a
>   = Return a
>   | Prog s a :||: Prog s a
>   | Get (s -> Prog s a)
>   | Put s (Prog s a)

> run :: Prog s a -> M s a
> run (Return x)  = ret x
> run (p :||: q)  = run p <||> run q
> run (Get k)     = get' (run . k)
> run (Put s p)   = put' s (run p)


Lemma put_ret_||_G:
  forall V W C,
    run (Put V (Return W :||: C))
    =
    run (Put V (Return W)) <&> run (Put V C)
Proof:
    run (Put V (Return W :||: C))
 =
    put' V (ret W <||> run C)
 =
    \_ -> let (xs, s1) = ret W V
             (ys, s2) = run C s1
          in (xs ++ ys, s2)
 =
    \_ -> let (ys, s2) = run C V
          in ((W,V):ys, s2)
 =
    \_ -> let (xs, s1) = ret W V
              (ys, s2) = run C V
          in (xs ++ ys, s2)
 =
    \s0 -> let (xs, s1) = put' V (ret W) s0
               (ys, s2) = put' V (run C) s0
           in (xs ++ ys, s2)
 =
    run (Put V (Return W)) <&> run (Put V C)
