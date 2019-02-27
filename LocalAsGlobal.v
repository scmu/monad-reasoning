Require Coq.Lists.List.
Require Coq.Program.Equality.

Require Coq.Logic.FunctionalExtensionality.

Module Type SemanticInterface.
Import Coq.Logic.FunctionalExtensionality.

(* The type of state. *)
Parameter S : Type.

(* The semantic domain *)
Parameter D : Type -> Type.

(* The algebra for the signature *)
Parameter retD: forall {A}, A -> D A.
Parameter failD : forall {A}, D A.
Parameter orD : forall {A}, D A -> D A -> D A.
Parameter getD : forall {A}, (S -> D A) -> D A.
Parameter putD : forall {A}, S -> D A -> D A.

(* State Laws *)
Parameter get_get_G_D:
  forall {A} (k: S -> S -> D A),
    getD (fun s => getD (fun s' => k s s'))
    =
    getD (fun s => k s s).

Parameter get_put_G_D:
  forall {A} (p: D A),
    getD (fun s => putD s p)
   =
   p.

Parameter put_get_G_D:
  forall {A} (s: S) (k: S -> D A),
  putD s (getD k)
  =
  putD s (k s).

Parameter put_put_G_D:
  forall {A} (s s': S) (p: D A),
  putD s (putD s' p)
  =
  putD s' p.

(* Nondeterminism Laws *)
Parameter or1_fail_G_D:
  forall {A} (q: D A),
  orD failD q
  =
  q.

Parameter or2_fail_G_D:
  forall {A} (p: D A),
  orD p failD
  =
  p.

Parameter or_or_G_D:
  forall {A} (p q r: D A),
  orD (orD p q) r
  =
  orD p (orD q r).

(* Global State Law *)
Parameter put_or_G_D:
  forall {A} (p q: D A) (s: S),
   orD (putD s p) q
   = 
   putD s (orD p q).

(* Further laws governing the interaction of state and nondeterminism *)
Parameter put_ret_or_G_D:
  forall {A} (v: S) (w: A) (q: D A),
    putD v (orD (retD w) q)
    =
    orD (putD v (retD w)) (putD v q).

Parameter put_or_comm_G_D:
  forall {A} (p q : D A) (t u : S -> S),
    getD (fun s => orD (orD (putD (t s) p) (putD (u s) q)) (putD s failD))
    =
    getD (fun s => orD (orD (putD (u s) q) (putD (t s) p)) (putD s failD)).

End SemanticInterface.

Module Type Syntax (Sem: SemanticInterface).

Import Sem.

Import Coq.Lists.List.
Import Coq.Program.Equality.
Import Coq.Logic.FunctionalExtensionality.
Import Coq.Program.Basics.

(* We start out by proving some useful lemmas about the semantic domain. *)
Lemma or_comm_ret_G_D:
  forall {A} (x y: A),
    orD (retD x) (retD y) = orD (retD y) (retD x).
Proof.
  intros.
  rewrite <- (get_put_G_D (orD (retD x) (retD y))).
  rewrite <- (get_put_G_D (orD (retD y) (retD x))).
  assert (H : forall (a b : A),
             (fun s => putD s (orD (retD a) (retD b)))
             =
             (fun s => orD (orD (putD s (retD a)) (putD s (retD b))) (putD s failD))).
  - intros; apply functional_extensionality; intro s.
    rewrite put_ret_or_G_D.
    rewrite <- (or2_fail_G_D (putD s (retD b))) at 1.
    rewrite (put_or_G_D (retD b) failD s).
    rewrite put_ret_or_G_D.
    rewrite or_or_G_D.
    reflexivity.
  - rewrite (H x y); rewrite (H y x).
    apply put_or_comm_G_D.
Qed.


Lemma get_put_G_D':
  forall {A} (p: S -> D A),
    getD (fun s => putD s (p s))
    =
    getD p.
Proof.
  intros.
  assert (H : (fun s => putD s (p s)) = (fun s => putD s (getD (fun s0 => p s0)))).
  - apply functional_extensionality; intro s.
    rewrite put_get_G_D.
    reflexivity.
  - rewrite H.
    rewrite get_put_G_D.
    auto.
Qed.

Lemma get_or_G_D:
  forall {A} (p: S -> D A) (q: D A),
    getD (fun s => orD (p s) q)
    =
    orD (getD p) q.
Proof.
  intros.
  rewrite <- (get_put_G_D (orD (getD p) q)).
  assert (H : (fun s => putD s (orD (getD p) q))
              = (fun s => putD s (orD (p s) q))).
  - apply functional_extensionality; intro s.
    rewrite <- put_or_G_D.
    rewrite put_get_G_D.
    rewrite put_or_G_D.
    reflexivity.
  - rewrite H.
    rewrite get_put_G_D'.
    reflexivity.
Qed.

Lemma get_ret_or_G_D:
  forall {A} (f : S -> A) (p : S -> D A),
    getD (fun s => orD (retD (f s)) (p s))
    =
    orD (getD (fun s => retD (f s))) (getD p).
Proof.
  intros.
  rewrite <- get_put_G_D' at 1.
  cut ((fun s => putD s (orD (retD (f s)) (p s)))
       =
       (fun s => putD s (orD (retD (f s)) (getD p)))).
  intro H. rewrite H.
  rewrite get_put_G_D'.
  rewrite get_or_G_D.
  reflexivity.
  apply functional_extensionality; intro s.
  rewrite put_ret_or_G_D.
  rewrite <- put_get_G_D.
  rewrite <- put_ret_or_G_D.
  reflexivity.
Qed.

Lemma get_const:
  forall {A} (p : D A),
    getD (fun s => p) = p.
Proof.
  intros.
  rewrite <- get_put_G_D'.
  apply get_put_G_D.
Qed.

(* Programs -- the free monad over the signature of fail + or + get + put.
   These programs are closed, i.e. they contain no free variables.
 *)
Inductive Prog : Type -> Type :=
  | Return : forall {A}, A -> Prog A
  | Fail : forall {A}, Prog A
  | Or : forall {A}, Prog A -> Prog A -> Prog A
  | Get : forall {A}, (S -> Prog A) ->Prog A
  | Put : forall {A}, S -> Prog A ->Prog A.

Fixpoint bind {A B} (p: Prog A) : (A -> Prog B) -> Prog B :=
   match p in (Prog A) return ((A -> Prog B) -> Prog B) with
   | Return v => (fun f => f v)
   | Fail => (fun f => Fail)
   | Or p1 p2 => (fun f => Or (bind p1 f) (bind p2 f))
   | Get p => (fun f => Get (fun s => bind (p s) f))
   | Put v p => (fun f => Put v (bind p f))
  end.

Lemma bind_bind : 
  forall {A B C} (p: Prog A) (k1: A -> Prog B) (k2: B -> Prog C),
     bind (bind p k1) k2 = bind p (fun x => bind (k1 x) k2).
Proof.
  intros A B C p; 
  induction p; intros; simpl; auto.
  - rewrite IHp1, IHp2; auto.
  - f_equal; apply functional_extensionality; intros; rewrite H; auto.
  - rewrite IHp; auto.
Qed.

Lemma bind_return:
  forall {A} (p: Prog A),
     bind p (fun x => Return x) = p.
Proof.
  intros Ap; 
  induction p; intros; simpl; auto.
  - rewrite IHp1, IHp2; auto.
  - f_equal; apply functional_extensionality; intros; rewrite H; auto.
  - rewrite IHp; auto.
Qed.

Lemma bind_return':
  forall {A X} (p: X -> Prog A),
     (fun e => bind (p e)  (fun x => Return x)) = (fun e => p e).
Proof.
  intros.
  apply functional_extensionality; intro e0.
  apply bind_return.
Qed.

Lemma bind_or_left:
  forall {A B} (p1 p2: Prog A) (f: A -> Prog B),
    bind (Or p1 p2) f = Or (bind p1 f) (bind p2 f).
Proof.
  auto.
Qed.

Lemma bind_if:
  forall {A B} (p: bool) (m n: Prog A) (k: A -> Prog B),
    bind (if p then m else n) k
    =
    if p then bind m k else bind n k.
Proof.
  intros; destruct p; auto.
Qed.  

Lemma bind_left_zero:
  forall {A B} (f: A -> Prog B),
    bind Fail f = Fail.
Proof.
  auto.
Qed.

(* Programs with free variables *)

(* Environment as a heterogeneous list *)
Inductive Env : list Type -> Type :=
  | Nil : Env nil
  | Cons : forall {A L}, A -> Env L -> Env (A :: L).

Definition tail_ {E} (env: Env E) :=
  match env in (Env E) return (match E with nil => unit | X::Xs => Env Xs end) with
  | Nil => tt
  | Cons x xs => xs
  end.

Definition tail {C E} (env: Env (C :: E)): Env E := tail_ env.

Definition head_ {E} (env: Env E) :=
  match env in (Env E) return (match E with nil => unit | X::Xs => X end) with
  | Nil => tt
  | Cons x xs => x
  end.

Definition head {C E} (env: Env (C :: E)): C := head_ env.

Lemma cons_head_tail:
  forall {A E} (env: Env (A::E)),
    Cons (head env) (tail env) = env.
Proof.
  intros. dependent destruction env. auto.
Qed.

(* We represent open programs (programs with free variables) abstractly
   as a function that produces a closed program when given an environment
 *)
Definition OProg (E: list Type)  (A: Type): Type := Env E -> Prog A.

Definition comap {A E E'} (p: OProg E A) : (Env E' -> Env E) -> OProg E' A :=
  fun f env => p (f env).

(* Filling in the first free variable *)
Definition cpush {A C E} (c: C) (p: OProg (C :: E) A): OProg E A :=
  comap p (fun env => Cons c env).

(* Ignoring the first free variable *)
Definition clift {A C E} (p: OProg E A): OProg (C :: E) A := comap p tail.

Lemma cpush_clift : 
  forall {A C E} (p: OProg E A)  (c: C),
     cpush c (clift p) = p.
Proof.
  intros; unfold cpush, clift, comap; simpl; auto.
Qed.

Definition obind {E A B} (p: OProg E A) : (A -> OProg E B) -> OProg E B :=
  fun k env => bind (p env) (fun x => k x env).

Lemma obind_from_bind:
  forall {E A B} (p: OProg E A) (k: A -> OProg E B),
    (fun env => bind (p env) (fun x => k x env))
    =
    obind p k.
Proof.
  auto.
Qed.

Lemma obind_obind:
  forall {A B C E} (p: OProg E A) (k1: A -> OProg E B) (k2: B -> OProg E C),
    obind (obind p k1) k2 = obind p (fun x => obind (k1 x) k2).
Proof.
  intros.
  unfold obind.
  apply functional_extensionality; intro env.
  apply bind_bind.
Qed.

Lemma obind_cpush:
  forall {E A B C} {a: C} {p: OProg (C :: E) A} {k: A -> OProg (C::E) B},
    obind (cpush a p) (fun x => cpush a (k x))
   =
   cpush a (obind p k).
Proof.
  intros; unfold obind, cpush, comap; auto.
Qed.

(* Contexts for open programs.
   Predicates like (S -> bool) indicate control flow choices based on information
   that is not statically available.
   Context E1 A E2 B:
           (E1, A) is the environment and return type of the subprogram that is
           expected in the hole.
           (E2, B) is the environment and return type of the whole
           program,
           So this context can be said to construct an open program that returns
           a value of type B given an E2 environment, from an open program that
           returns a value of type A given an E1 environment
   Note that this context type has no support for monadic bind, and therefore it
   deviates from the presentation in the paper.
   Further on, we introduce a data type BContext which also supports binds.
 *)
 
Inductive Context : list Type -> Type -> list Type -> Type -> Type :=
  | CHole  : forall {E A        }, Context E A E A

  | COr1   : forall {E1 E2 A B  }, Context E1 A E2 B ->
                                   OProg E2 B ->
                                   Context E1 A E2 B

  | COr2   : forall {E1 E2 A B  }, OProg E2 B ->
                                   Context E1 A E2 B ->
                                   Context E1 A E2 B

  | CPut   : forall {E1 E2 A B  }, (Env E2 -> S) ->
                                   Context E1 A E2 B ->
                                   Context E1 A E2 B

  | CGet   : forall {E1 E2 A B  }, (S -> bool) ->
                                   (Context E1 A (S::E2) B) ->
                                   (S -> OProg E2 B) ->
                                   Context E1 A E2 B

  | CDelay : forall {E1 E2 A B  }, (Env E2 -> bool) ->
                                   Context E1 A E2 B ->
                                   OProg E2 B ->
                                   Context E1 A E2 B

  | CPush  : forall {E1 E2 A B C}, C ->
                                   Context E1 A (C::E2) B ->
                                   Context E1 A E2 B

  | CLift  : forall {E1 E2 A B C}, Context E1 A E2 B ->
                                   Context E1 A (C::E2) B.

(* Applying a context to a program: produce a complete program from a program
   containing a hole (a context) and a program to be filled into the hole.
 *)
Fixpoint appl {E1 E2: list Type} {A B: Type} (c: Context E1 A E2 B)  : OProg E1 A -> OProg E2 B :=
  match c in (Context E1 A E2 B) return (OProg E1 A -> OProg E2 B) with
  | CHole        => (fun p env => p env)
  | COr1 c q     => (fun p env => Or (appl c p env) (q env))
  | COr2 p c     => (fun q env => Or (p env) (appl c q env))
  | CPut v c     => (fun p env => Put (v env) (appl c p env)) 
  | CGet t c q   => (fun p env => Get (fun s => if t s then cpush s (appl c p) env else q s env))
  | CDelay t c q => (fun p => (fun env => if t env then appl c p env else q env))
  | CPush x c    => (fun p env => cpush x (appl c p) env)
  | CLift c      => (fun p env => clift (appl c p) env) 
  end.

(* Applying a context to a context, aka composing contexts *)
Fixpoint applC {E1 E2 E3: list Type} {A B C: Type} (c: Context E2 B E3 C)  : Context E1 A E2 B -> Context E1 A E3 C:=
  match c in (Context E2 B E3 C) return (Context E1 A E2 B -> Context E1 A E3 C) with
  | CHole        => (fun d => d)
  | COr1 c q     => (fun d => COr1 (applC c d) q)
  | COr2 p c     => (fun d => COr2 p (applC c d))
  | CPut v c     => (fun d => CPut v (applC c d)) 
  | CGet t c q   => (fun d => CGet t (applC c d) q)
  | CDelay t c q => (fun d => CDelay t (applC c d) q)
  | CPush x c    => (fun d => CPush x (applC c d))
  | CLift c      => (fun d => CLift (applC c d))
  end.

(* Alternative zipper-based context.
   Whereas the Context datatype offers a top-down view of a program-with-hole,
   the ZContext datatype offers a bottom-up view of a program-with-hole.

   ZContext E1 A E2 B:
            the hole has environment and type (E1,A); the ZContext
            transforms a program of that type into a program of type B,
            given environment E2.
 *)
Inductive ZContext : list Type -> Type -> list Type -> Type -> Type :=
  | ZTop   : forall {E A},
      ZContext E A E A

  | ZOr1   : forall {E1 E2 A B},
      ZContext E1 A E2 B -> OProg E1 A -> ZContext E1 A E2 B

  | ZOr2   : forall {E1 E2 A B},
      ZContext E1 A E2 B -> OProg E1 A -> ZContext E1 A E2 B

  | ZPut   : forall {E1 E2 A B},
      ZContext E1 A E2 B -> (Env E1 -> S) -> ZContext E1 A E2 B

  | ZGet   : forall {E1 E2 A B},
      ZContext E1 A E2 B -> (S -> bool) -> (S -> OProg E1 A) -> ZContext (S::E1) A E2 B

  | ZDelay : forall {E1 E2 A B},
      ZContext E1 A E2 B -> (Env E1 -> bool) -> OProg E1 A -> ZContext E1 A E2 B

  | ZPush  : forall {E1 E2 A B C},
      ZContext E1 A E2 B -> C -> ZContext (C :: E1) A E2 B

  | ZLift  : forall {E1 E2 A B C},
      ZContext (C::E1) A E2 B -> ZContext E1 A E2 B.

Fixpoint zappl {E1 E2: list Type} {A B: Type} (z: ZContext E1 A E2 B)  : OProg E1 A -> OProg E2 B :=
  match z in (ZContext E1 A E2 B) return (OProg E1 A -> OProg E2 B) with
  | ZTop         => (fun p env => p env)
  | ZOr1 z q     => (fun p     => zappl z (fun env => Or (p env) (q env)))
  | ZOr2 z p     => (fun q     => zappl z (fun env => Or (p env) (q env)))
  | ZPut z v     => (fun p     => zappl z (fun env => Put (v env) (p env)))
  | ZGet z t q   => (fun p     =>
                       zappl z (fun env =>
                                  Get (fun s => if t s
                                                then (cpush s p) env
                                                else q s env)))
  | ZDelay z t q => (fun p     => zappl z (fun env => if t env then p env else q env))
  | ZPush z c    => (fun p     => zappl z (cpush c p))
  | ZLift z      => (fun p     => zappl z (clift p))
  end.


(* Functionality for transforming between zipper contexts and regular contexts. *)

Fixpoint toZContext_ {E1 E2 A B} (c: Context E1 A E2 B):
  (forall {E3 C}, ZContext E2 B E3 C-> ZContext E1 A E3 C) :=
  match c in (Context E1 A E2 B) return ((forall {E3 C}, ZContext E2 B E3 C-> ZContext E1 A E3 C)) with
   | CHole        => (fun _ _ z => z)
   | COr1 c p     => (fun _ _ z => toZContext_ c (ZOr1 z p))
   | COr2 p c     => (fun _ _ z => toZContext_ c (ZOr2 z p))
   | CPut s c     => (fun _ _ z => toZContext_ c (ZPut z s))
   | CGet t c p   => (fun _ _ z => toZContext_ c (ZGet z t p))
   | CDelay t c p => (fun _ _ z => toZContext_ c (ZDelay z t p))
   | CPush a c    => (fun _ _ z => toZContext_ c (ZPush z a))
   | CLift c      => (fun _ _ z => toZContext_ c (ZLift z))
  end.

Definition toZContext {E1 E2 A B} (c: Context E1 A E2 B): ZContext E1 A E2 B := toZContext_ c ZTop.
 
Lemma zappl_toZContext_:
   forall {E1 E2 A B} (c: Context E1 A E2 B) {E3 C} (z: ZContext E2 B E3 C) (p: OProg E1 A),
     zappl (toZContext_ c z) p = zappl z (appl c p).
Proof.
  intros E1 E2 A B c; induction c; intros E3 D z prog; simpl; auto; rewrite IHc; auto.
Qed.

Lemma zappl_toZContext:
   forall {E1 E2 A B} (c: Context E1 A E2 B) (p: OProg E1 A),
     zappl (toZContext c) p = appl c p.
Proof.
  intros; unfold toZContext; rewrite zappl_toZContext_; simpl; reflexivity.
Qed.

Fixpoint fromZContext_ {E2 E3: list Type} {B C: Type} (z: ZContext E2 B E3 C)  : forall {E1 A}, Context E1 A E2 B -> Context E1 A E3 C :=
  match z in (ZContext E2 B E3 C) return (forall {E1 A}, Context E1 A E2 B -> Context E1 A E3 C) with
  | ZTop         => (fun _ _ c => c)
  | ZOr1 z q     => (fun _ _ c => fromZContext_ z (COr1 c q)) 
  | ZOr2 z p     => (fun _ _ c => fromZContext_ z (COr2 p c))
  | ZPut z v     => (fun _ _ c => fromZContext_ z (CPut v c))
  | ZGet z t q   => (fun _ _ c => fromZContext_ z (CGet t c q))
  | ZDelay z t q => (fun _ _ c => fromZContext_ z (CDelay t c q))
  | ZPush z x    => (fun _ _ c => fromZContext_ z (CPush x c))
  | ZLift z      => (fun _ _ c => fromZContext_ z (CLift c))
  end.

Definition fromZContext {E1 E2: list Type}  {A B: Type} (z: ZContext E1 A E2 B)  : Context E1 A E2 B :=
  fromZContext_ z CHole. 

Lemma  appl_fromZContext_:
  forall {B C E2 E3} (z: ZContext E2 B E3 C) {E1 A} (c: Context E1 A E2 B) (p: OProg E1 A),
       appl (fromZContext_ z c) p = zappl z (appl c p).
Proof.
  intros B C E2 E3 z; induction z; intros E0 A0 c0 p; auto; simpl; rewrite IHz; auto.
Qed.

Lemma  appl_fromZContext:
  forall {A B E1 E2} (z: ZContext E1 A E2 B) (p: OProg E1 A),
       appl (fromZContext z) p = zappl z p.
Proof.
  intros; unfold fromZContext; rewrite appl_fromZContext_; auto.
Qed.

Lemma toZContext_fromZContext_:
  forall {E2 E3 B C} (z: ZContext E2 B E3 C) {E1 A} (c: Context E1 A E2 B),
  toZContext (fromZContext_ z c) = toZContext_ c z.
Proof.
  intros E2 E3 B C z; induction z; intros E0 A0 c0; simpl; auto; rewrite IHz; auto.
Qed. 

Lemma toZContext_fromZContext:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B),
  toZContext (fromZContext z) = z.
Proof.
  intros; unfold fromZContext; apply toZContext_fromZContext_.
Qed.

Lemma invert_zappl_zput:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B) (v: Env E1 -> S) (q: OProg E1 A),
     zappl z (fun env => Put (v env) (q env))
     =
     zappl (ZPut z v) q.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zappl_zor1:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B)  (p q: OProg E1 A),
     zappl z (fun env => Or (p env) (q env))
     =
     zappl (ZOr1 z q) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zappl_zor2:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B)  (p q: OProg E1 A),
     zappl z (fun env => Or (p env) (q env))
     =
     zappl (ZOr2 z p) q.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zappl_zget:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B)  (p: S -> OProg E1 A),
     zappl z (fun env => Get (fun s => p s env))
     =
     zappl (ZGet z (fun _ => true) (fun _ _ => Fail)) (fun env' => clift (p (head env')) env').
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zappl_zget_or:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B)  (p q: S -> OProg E1 A),
     zappl z (fun env => Get (fun s => Or (p s env) (q s env)))
     =
     zappl (ZOr1 (ZGet z (fun _ => true) (fun _ _ => Fail)) (fun env' => clift (q (head env')) env')) (fun env' => clift (p (head env')) env').
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zappl_zdelay:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B) (b: Env E1 -> bool) (p q: OProg E1 A),
    zappl z (fun env => if (b env) then (p env) else (q env))
    =
    zappl (ZDelay z b q) (fun env => p env).
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zappl_zpush:
  forall {E1 E2 A B C}
         (z: ZContext E1 A E2 B) (x: C) (p: OProg (C::E1) A),
    zappl z (cpush x p)
    =
    zappl (ZPush z x) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.


(* The semantic function for global, i.e. non-backtracking, state *)
Fixpoint run {A} (p : Prog A) : D A :=
  match p with
  | Return x => retD x
  | Fail     => failD
  | Or p q   => orD (run p) (run q)
  | Get p    => getD (fun s => run (p s))
  | Put s p  => putD s (run p)
  end.

Lemma run_ret: forall {A} (x: A), run (Return x) = retD x.
Proof. auto. Qed.

Lemma run_fail: forall {A}, @run A Fail = failD.
Proof. auto. Qed.

Lemma run_or : forall {A} (p q : Prog A), run (Or p q) = orD (run p) (run q).
Proof. auto. Qed.

Lemma run_get: forall {A} (p: S -> Prog A), run (Get p) = getD (fun s => run (p s)).
Proof. auto. Qed.

Lemma run_put:forall {A} (s: S) (p: Prog A), run (Put s p) = putD s (run p).
Proof. auto. Qed.

(* Derived definitions for open programs *)
Definition orun {A E} (p: OProg E A) (env: Env E) : D A :=
  run (p env).

Lemma orun_fail:
  forall {A E},
    @orun A E (fun env => Fail) = fun _ => failD.
Proof.
  intros. apply functional_extensionality. intro env. 
  unfold orun.
  auto.
Qed.

Lemma orun_or:
  forall {A E} (p q: OProg E A),
    orun (fun env => Or (p env) (q env)) = fun env => orD (orun p env) (orun q env).
Proof.
  intros; apply functional_extensionality; intro env; unfold orun. auto.
Qed.

Lemma orun_get:
  forall {A E} (p: S -> OProg E A),
    orun (fun env => Get (fun s => p s env)) = fun env => getD (fun s => orun (p s) env).
Proof.
  intros; apply functional_extensionality; intro env; unfold orun; auto.
Qed.

Lemma orun_put:
  forall {E A} (s: Env E -> S) (p: OProg E A),
    orun (fun env => Put (s env) (p env)) = fun env => putD (s env) (orun p env).
Proof.
  intros; apply functional_extensionality; intro env; unfold orun; auto.
Qed.

(* We will prove some laws for Prog equipped with run.
   The first step is to prove that these laws hold at least at the top level of auto
   program (ie empty context).
   These proofs will be generalized further on.
 *)
Lemma get_get_G':
  forall {A} (k: S -> S -> Prog A),
    run (Get (fun s => Get (fun s' => k s s')))
    =
    run (Get (fun s => k s s)).
Proof.
  intros A k. simpl. apply get_get_G_D.
Qed.

Lemma get_put_G':
  forall {A} (q: Prog A),
    run (Get (fun s => Put s q))
   =
   run q.
Proof.
  intros.
  apply get_put_G_D.
Qed.

Lemma put_get_G':
  forall {A} (s: S) (p: S -> Prog A),
    run (Put s (Get p))
    =
    run (Put s (p s)).
Proof.
  intros. simpl.
  apply (put_get_G_D s (fun s => run (p s))).
Qed.

Lemma put_put_G':
  forall {A} (v1 v2: S) (q: Prog A),
    run (Put v1 (Put v2 q))
   =
   run (Put v2 q).
Proof.
  intros; repeat rewrite run_put; apply put_put_G_D.
Qed.

Lemma put_or_G':
  forall {A} (p q: Prog A) (s: S),
    run (Or (Put s p) q)
   = 
   run (Put s (Or p q)).
Proof.
  intros; apply put_or_G_D.
Qed.

Lemma get_or_G' : forall {A : Type} (p : S -> Prog A) (q : Prog A),
    run (Get (fun s => Or (p s) q))
    =
    run (Or (Get p) q).
Proof.
  intros; apply get_or_G_D.
Qed.  

Lemma or_fail':
  forall {A} (q: Prog A),
    run (Or Fail q)
    =
    run q.
Proof.
  intros; apply or1_fail_G_D.
Qed.

Lemma fail_or':
  forall {A} (q: Prog A),
    run (Or q Fail)
    =
    run q.
Proof.
  intros; apply or2_fail_G_D.
Qed.

Lemma or_or':
  forall {A} (p q r: Prog A),
    run (Or (Or p q) r)
    =
    run (Or p (Or q r)).
Proof.
  intros; apply or_or_G_D.
Qed.

(* Lemma to help generalize proofs for empty contexts to proofs for arbitrary contexts. *)
Lemma meta_G:
  forall {A B E1 E2} {X}  (p q: X -> Prog A)
    (meta_G': forall (x: X), run (p x) = run (q x)) 
    (f: Env E1 -> X)
    (c: Context E1 A E2 B),
    orun (appl c (fun env => p (f env)))
    = 
    orun (appl c (fun env => q (f env))).
Proof.
  intros.
  induction c; simpl.
  - unfold orun.
    apply functional_extensionality.
    simpl.
    intro env0.
    apply meta_G'.
  - repeat rewrite orun_or. rewrite (IHc p q); auto.
  - repeat rewrite orun_or. rewrite (IHc p q); auto.
  - repeat rewrite orun_put. rewrite (IHc p q); auto.
  - repeat rewrite orun_get.
    apply functional_extensionality; intro env.
    f_equal. apply functional_extensionality; intro s; destruct (b s).
    + unfold cpush. unfold comap.
      assert (H : forall r,
                 orun (fun env => appl c r (Cons s env))
                 =
                 fun env => orun (appl c r) (Cons s env)).
      { auto. }
      rewrite H.
      rewrite IHc with (q:=q).
      auto.
      apply meta_G'.
    + reflexivity.
  - change (orun ?f) with (fun env => orun f env);
    apply functional_extensionality; intro env0.
    change (orun (fun env => if b env then ?f env else ?g env) env0) with
        (orun (fun env => if b env0 then f env else g env) env0).
    destruct (b env0).
    + rewrite IHc with (q:=q).
      auto.
      apply meta_G'.
    + reflexivity.
  - unfold cpush, comap.
    change (orun (fun env => appl c0 ?r (Cons c env)))
      with (fun env => orun (appl c0 r) (Cons c env)).
    rewrite IHc with (q:=q); auto.
  - unfold clift, comap.
    change (orun (fun env => appl c ?r (tail env)))
      with (fun env => orun (appl c r) (@tail C _ env)).
    rewrite IHc with (q:=q); auto.
Qed.

(* Now we can generalize to arbitrary (but bind-free) contexts. *)
Lemma get_get_G:
  forall {A B E1 E2} (c: Context E1 A E2 B) (k: S -> S -> OProg E1 A),
    orun (appl c (fun env => Get (fun s1 => Get (fun s2 => k s1 s2 env))))
    = 
    orun (appl c (fun env => Get (fun s1 => k s1 s1 env))).
Proof.
  intros A B E1 E2 c k.
  apply (@meta_G A B E1 E2 (S -> S -> Prog A) 
     (fun k => Get (fun s1 => Get (fun s2 => k s1 s2)))
     (fun k => Get (fun s1 => k s1 s1))
     get_get_G'
     (fun env s1 s2 => k s1 s2 env)
).
Qed.

Lemma get_put_G:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (k: OProg E1 A),
    orun (appl c (fun env => Get (fun s => Put s (k env))))
   =
   orun (appl c k).
Proof.
  intros.
 apply (@meta_G A B E1 E2 (Prog A) 
     (fun q => Get (fun s => Put s q))
     (fun q => q)
     get_put_G'
     (fun env => k env)
 ).
Qed.

Lemma put_get_G:
  forall {A B E1 E2} (c: Context E1 A E2 B) (k: S -> OProg E1 A) (v: Env E1 -> S),
    orun (appl c (fun env => Put (v env) (Get (fun s => k s env))))
    = 
    orun (appl c (fun env => Put (v env) ( k (v env) env))).
Proof.
  intros A B E1 E2 c k v;
  apply (@meta_G A B E1 E2 (S * (S -> Prog A))
     (fun x => Put (fst x) (Get (snd x)))
     (fun x => Put (fst x) (snd x (fst x)))
     (fun x => put_get_G' (fst x) (snd x))
    (fun env => (v env, fun s => k s env))
  ).
Qed.

Lemma put_put_G:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (v1 v2: Env E1 -> S) (k: OProg E1 A),
    orun (appl c (fun env => Put (v1 env) (Put (v2 env) (k env))))
    =
    orun (appl c (fun env => Put (v2 env) (k env))).
Proof.
  intros.
   apply (@meta_G A B E1 E2 ((S * S) * (Prog A))
     (fun t => Put (fst (fst t)) (Put (snd (fst t)) (snd t)))
     (fun t => Put (snd (fst t)) (snd t))
     (fun t => put_put_G' (fst (fst t)) (snd (fst t)) (snd t))
    (fun env => ((v1 env, v2 env), k env))
  ).
Qed.

Lemma put_or_G:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (p: OProg E1 A) (q: OProg E1 A) (s: Env E1 -> S),
    orun (appl c (fun env => Or (Put (s env) (p env)) (q env)))
   = 
   orun (appl c (fun env => Put (s env) (Or (p env) (q env)))).
Proof.
  intros.
  apply (@meta_G A B E1 E2 ((Prog A * Prog A) * S)
     (fun t => Or (Put (snd t) (fst (fst t))) (snd (fst t)))
     (fun t => Put (snd t) (Or (fst (fst t)) (snd (fst t))))
     (fun t => put_or_G' (fst (fst t)) (snd (fst t)) (snd t))
    (fun env => ((p env, q env), s env))
  ).
Qed.

Lemma get_or_G:
  forall {E1 E2 A B}
         (c: Context E1 A E2 B) (p: S -> OProg E1 A) (q: OProg E1 A),
    orun (appl c (fun env => Get (fun s =>
                                    Or ((fun s' => p s' env) s) (q env))))
    =
    orun (appl c (fun env => Or (Get (fun s =>
                                        ((fun s' => p s' env) s))) (q env))).
Proof.
  intros.
  apply (@meta_G A B E1 E2 ((S -> Prog A) * Prog A)
                 (fun t => Get (fun s => Or (fst t s) (snd t)))
                 (fun t => Or (Get (fun s => (fst t s))) (snd t))
                 (fun t => get_or_G' (fst t) (snd t))
                 (fun env => ((fun s => p s env), q env))).
Qed.

Lemma or_fail:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (q: OProg E1 A), 
    orun (appl c (fun env => Or Fail (q env)))
    =
    orun (appl c q).
Proof.
  intros.
  apply (@meta_G A B E1 E2 (Prog A)
     (fun t => Or Fail t)
     (fun t => t)
     (fun t => or_fail' t)
    (fun env => q env)
  ).
Qed.

Lemma fail_or:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (q: OProg E1 A), 
    orun (appl c (fun env => Or  (q env) Fail))
    =
    orun (appl c q).
Proof.
  intros.
  apply (@meta_G A B E1 E2 (Prog A)
     (fun t => Or t Fail)
     (fun t => t)
     (fun t => fail_or' t)
    (fun env => q env)
  ).
Qed.

Lemma or_or:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (p q r: OProg E1 A),
    orun (appl c (fun env => Or (Or (p env) (q env)) (r env)))
   =
   orun (appl c (fun env => Or (p env) (Or (q env) (r env)))).
Proof.
  intros.
  apply (@meta_G A B E1 E2 ((Prog A * Prog A) * Prog A)
     (fun t => Or (Or (fst (fst t)) (snd (fst t))) (snd t))
     (fun t => Or (fst (fst t)) (Or (snd (fst t)) (snd t)))
     (fun t => or_or' (fst (fst t)) (snd (fst t)) (snd t))
    (fun env => ((p env, q env), r env))
  ).
Qed.

Lemma put_ret_or_G:
  forall {A} (v: S) (w: A) (q: Prog A),
  run (Put v (Or (Return w) q))
  =
  run (Or (Put v (Return w)) (Put v q)).
Proof.
  intros.
  apply put_ret_or_G_D.
Qed.

(* The function trans takes a program p and produces a program p' such that
   the result of running p under local state semantics is the same as the result
   of running p' under global state semantics.
 *)
Fixpoint trans {A} (p: Prog A): Prog A :=
  match p with
  | Return x => Return x
  | Or p q   => Or (trans p) (trans q)
  | Fail     => Fail
  | Get p    => Get (fun s => trans (p s))
  | Put s p  => Get (fun s0 => Or (Put s (trans p)) (Put s0 Fail))
  end.

Definition otrans {E A} (p: OProg E A) : OProg E A :=
  fun env => trans (p env).

(* Translating contexts *)
Fixpoint transC {E1 E2: list Type} {A B: Type} (c: Context E1 A E2 B) : Context E1 A E2 B :=
  match c in (Context E1 A E2 B) return (Context E1 A E2 B) with
  | CHole        => CHole
  | COr1 c q     => COr1 (transC c) (otrans q)
  | COr2 p c     => COr2 (otrans p) (transC c)
  | CPut v c     => CGet (fun s => true)
                         (COr1
                            (CPut (fun env => v (tail env))
                                  (CLift (transC c)))
                            (fun env => Put (head env) Fail))
                         (fun s env => Fail)
  | CGet t c q   => CGet t (transC c) (fun s => otrans (q s))
  | CDelay t c q => CDelay t (transC c) (otrans q) 
  | CPush x c    => CPush x (transC c)
  | CLift c      => CLift (transC c)
  end.

Lemma otrans_cpush:
 forall {A C E1}  (p: OProg (C::E1) A) (x: C),
  cpush x (otrans p) = otrans (cpush x p).
Proof.
  intros A C E p x; unfold cpush, comap, otrans; auto.
Qed.

Lemma otrans_clift:
 forall {A C E}  (p: OProg E A),
  @clift _ C _ (otrans p) = otrans (clift p).
Proof.
  intros; unfold clift, otrans, comap; reflexivity.
Qed.

Lemma otrans_appl:
 forall {A B E1 E2} (c: Context E1 A E2 B) (p: OProg E1 A),
  otrans (appl c p) = appl (transC c) (otrans p).
Proof.
  intros A B E1 E2 c; induction c; intro p; simpl.
  - change (fun env => ?p env) with p; auto.
  - rewrite <- IHc; unfold otrans; simpl; auto.
  - rewrite <- IHc; unfold otrans; simpl; auto.
  - rewrite <- IHc. unfold otrans; simpl; auto.
  - unfold otrans at 1; apply functional_extensionality; intro env; simpl; apply f_equal;
     apply functional_extensionality; intro s; rewrite <- IHc; unfold otrans.
     destruct (b s); auto.
 - rewrite <- IHc. unfold otrans; simpl; auto; apply functional_extensionality; intro env; destruct (b env); auto.
 - rewrite <- IHc. rewrite (otrans_cpush (appl c0 p) c). unfold otrans; simpl; auto.
 - rewrite <- IHc. rewrite otrans_clift; auto.
Qed.

(* The derived semantic function of local state *)
Definition evl : forall {A}, Prog A -> D A := 
  fun _ p => run (trans p).

Definition oevl : forall {A E}, OProg E A -> Env E -> D A := 
  fun _ _ p => orun (otrans p).

Lemma oevl_fail:
  forall {A E},
    @oevl A E (fun env => Fail) = fun env => failD.
Proof.
  auto.
Qed.

Lemma evl_or:
  forall {A} (m1 m2: Prog A),
    evl (Or m1 m2) = orD (evl m1) (evl m2).
Proof.
  auto.
Qed.
  
Lemma oevl_or:
  forall {A E} (p q: OProg E A),
    oevl (fun env => Or (p env) (q env)) = fun env => orD (oevl p env) (oevl q env).
Proof.
  auto.
Qed.

Lemma evl_get:
  forall {A} (p: S -> Prog A),
    evl (Get p) = getD (fun s => evl (p s)).
Proof.
  auto.
Qed.

Lemma oevl_get:
  forall {A E} (p: S -> OProg E A),
    oevl (fun env => Get (fun s => p s env)) = fun env => getD (fun s => oevl (p s) env).
Proof.
  auto.
Qed.

Lemma oevl_put:
  forall {A E} (s: Env E -> S) (p: OProg E A),
    oevl (fun env => Put  (s env) (p env)) = fun env => getD (fun s0 => orD (putD (s env) (oevl p env)) (putD s0 failD)).
Proof.
  auto.
Qed.

(* Now we prove that evl is, in fact, a semantic function for local,
   i.e. backtracking, state.
   We start out by proving that it gives rise to a state monad and auto
   nondeterminism monad.
 *)
Lemma get_get_L_0:
  forall {A} (k: S -> S -> Prog A),
    evl (Get (fun s1 => Get (fun s2 => k s1 s2)))
    =
    evl (Get (fun s1 => k s1 s1)).
Proof.
  intros A k. unfold evl; simpl. apply get_get_G'.
Qed.

Lemma put_fail_L_0:
  forall {A} (s: S),
    evl (Put s Fail)
    =
    evl (Fail: Prog A).
Proof.
  intros.
  unfold evl.
  unfold trans.
  unfold run.
  assert (H: (fun s0 : S => orD (putD s (failD: D A)) (putD s0 failD))
             =
             (fun s0 => putD s0 failD)).
  - apply functional_extensionality; intro s0.
    rewrite put_or_G_D.
    rewrite or1_fail_G_D.
    rewrite put_put_G_D.
    reflexivity.
  - rewrite H.
    rewrite get_put_G_D.
    reflexivity.
Qed.

Lemma Meta1_Base:
  forall {A B E} (p q: OProg (A::E) B) 
    (P: forall {C D E'} (c: Context (A::(E)) C E' D) (k : B -> OProg (A::(E)) C), 
            oevl (appl c (obind p k)) = oevl (appl c (obind q k))) 
    (r: OProg E A),
    (forall {C} (k: B -> OProg E C) (env: Env E), 
            oevl (obind (obind r (fun x => cpush x p)) k) env
            = 
            oevl (obind (obind r (fun x => cpush x q)) k) env).
Proof.
  intros A B E p q P r C k env.
  unfold oevl, orun, otrans, obind.
     induction (r env); simpl.
      ** fold (obind (cpush a p) (fun x : B => k x) env);
          fold (obind (cpush a q) (fun x : B => k x) env).
      change (fun x => ?h x) with h.
      assert (k = (fun x => cpush a (clift (k x)))).
     --  apply functional_extensionality; intro y; rewrite cpush_clift; auto.
     -- rewrite H; repeat rewrite obind_cpush.
          change (cpush a (obind ?p (fun x : B => clift (k x)))) with (appl (CPush a CHole)  (obind p (fun x : B => clift (k x)))).
          unfold oevl, orun, otrans in P. generalize env. apply equal_f; apply P.
     ** auto.
     ** rewrite (IHp0_1 p q), (IHp0_2 p q); auto.
     ** apply f_equal, functional_extensionality; intro x; rewrite (H x p q); auto.
     ** apply f_equal, functional_extensionality; intro s0. 
         apply equal_f, f_equal.  apply f_equal; auto.
Qed.

Lemma Meta1:
  forall {A B E} (p q: OProg (A::E) B) 
    (P: forall {C D E'} (c: Context (A::E) C E' D) (k : B -> OProg (A::E) C), 
            oevl (appl c (obind p k)) = oevl (appl c (obind q k))) (r: OProg E A),
    (forall {C D E'} (c: Context E C E' D) (k: B -> OProg E C) (env: Env E'), 
            oevl (appl c (obind (obind r (fun x => cpush x p)) k)) env
            = 
            oevl (appl c (obind (obind r (fun x => cpush x q)) k)) env).
Proof.
  intros A B E p q P r C D E' c.
  dependent induction c; intros k env.
  - change (appl CHole ?p) with p. apply Meta1_Base; auto.
  - simpl. repeat rewrite oevl_or. rewrite (IHc p q); auto.
  - simpl. repeat rewrite oevl_or. rewrite (IHc p q); auto.
  - simpl. repeat rewrite oevl_put. rewrite (IHc p q); auto.
  - simpl. repeat rewrite oevl_get. apply f_equal; apply functional_extensionality; intro s0. 
    destruct (b s0).
    * unfold cpush, comap.
      change (oevl (fun env0 => appl c ?p (Cons s0 env0)) env)
        with (oevl (appl c p) (Cons s0 env)).
      rewrite (IHc p q); auto.
    * auto.
  - simpl. 
    change (oevl
              (fun env0 : Env E2 => if b env0 then ?p env0  else o env0)
              env) with (oevl
                           (fun env0 : Env E2 => if b env then p env0 else o env0)
                           env).
    destruct (b env).
    * apply IHc; auto.
    * auto.
  - simpl. unfold cpush, comap.
    change (oevl (fun env0 : Env E2 => ?b (Cons c env0)) env) with (oevl b (Cons c env)).
    apply IHc. auto.
  - simpl. unfold clift, comap.
    change (oevl (fun env0 => appl c ?p (tail env0)) env) with
        (oevl (appl c p) (tail env)). auto. 
Qed.

Lemma inverse_functional_extensionality:
  forall {A B} (f g: A -> B),
  f = g -> forall x, f x = g x.
Proof.
  intros; rewrite H; auto.
Qed.

Lemma evl_meta:
  forall {A B E1 E2} {X}  (p q: X -> Prog A)
    (meta_G': forall (x: X), evl (p x) = evl (q x)) 
    (f: Env E1 -> X)
    (c: Context E1 A E2 B),
    oevl (appl c (fun env => p (f env)))
    = 
    oevl (appl c (fun env => q (f env))).
Proof.
  intros; induction c.
  - simpl; unfold oevl; unfold orun, otrans.
     apply functional_extensionality; intro env0.
     unfold evl in meta_G'.
     apply meta_G'.
 - simpl; unfold oevl, evl, otrans, orun in *; simpl; apply functional_extensionality; intro env0.
  repeat rewrite run_or; simpl in IHc. apply equal_f. apply f_equal. generalize env0. 
  apply inverse_functional_extensionality. rewrite (IHc p q).
  auto.
  auto.
  - simpl; unfold oevl, evl, otrans, orun in *; simpl; apply functional_extensionality; intro env0.
  repeat rewrite run_or; simpl in IHc. apply f_equal. generalize env0. 
  apply inverse_functional_extensionality. rewrite (IHc p q).
  auto.
  auto.
 - simpl;  unfold oevl, evl, otrans, orun in *; simpl.
    apply functional_extensionality; intro env0.
    repeat rewrite run_get; apply f_equal.
   apply functional_extensionality; intro s0.
   repeat rewrite run_or.
  apply equal_f.
  apply f_equal.
  repeat rewrite run_put.
  apply f_equal.
  generalize env0. apply inverse_functional_extensionality.
  rewrite (IHc p q).
  auto.
  auto.
 - simpl;  unfold oevl, evl, otrans, orun in *; simpl.
    apply functional_extensionality; intro env0.
    repeat rewrite run_get; apply f_equal.
    apply functional_extensionality; intro s0.
    destruct (b s0).
    * unfold cpush, comap.
      generalize (Cons s0 env0). apply inverse_functional_extensionality.
      rewrite (IHc p q).
     reflexivity.
     auto.
  * auto.
 - simpl;  unfold oevl, evl, otrans, orun in *; simpl.
   apply functional_extensionality; intro env0.
   destruct (b env0).
  * generalize env0; apply inverse_functional_extensionality.
     rewrite (IHc p q). auto.
     auto.
  * auto.
 - simpl;  unfold oevl, evl, otrans, orun in *; simpl.
    unfold cpush, comap.
    apply functional_extensionality; intro env0.
    generalize (Cons c env0); apply inverse_functional_extensionality.
    apply (IHc p q). auto.
 - simpl;  unfold oevl, evl, otrans, orun in *; simpl.
    unfold clift, comap.
    apply functional_extensionality; intro env0.
    generalize (tail env0); apply inverse_functional_extensionality.
    apply (IHc p q). auto.
Qed.

Lemma get_get_L_1:
  forall {A B E1 E2} (c: Context E1 A E2 B) (k: S -> S -> OProg E1 A),
    oevl (appl c (fun env => Get (fun s1 => Get (fun s2 => k s1 s2 env))))
    =
    oevl (appl c (fun env => Get (fun s1 => k s1 s1 env))).
Proof.
  intros A B E1 E2 c k.
  apply (evl_meta 
     (fun k => Get (fun s1 => Get (fun s2 => k s1 s2)))
     (fun k => Get (fun s => k s s))
     get_get_L_0 
    (fun env => (fun s1 s2 => k s1 s2 env))).
Qed.

Lemma put_get_L_1:
  forall {A B E1 E2} (c: Context E1 A E2 B) (k: S -> OProg E1 A) (v: Env E1 -> S),
    oevl (appl c (fun env => Put (v env) (Get (fun s => k s env))))
    =
    oevl (appl c (fun env => Put (v env) (k (v env) env))).
Proof.
  intros.
   unfold oevl; repeat rewrite otrans_appl; unfold otrans; simpl.
  repeat rewrite <- zappl_toZContext.
  repeat rewrite invert_zappl_zget_or.
  unfold clift, comap.
  repeat rewrite <- appl_fromZContext.
  rewrite put_get_G.
  auto.
Qed.

Lemma put_fail_L_1:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (v: Env E1 -> S),
    oevl (appl c (fun env => Put (v env) Fail))
   = 
   oevl (appl c (fun env => Fail)).
Proof.
  intros.
  unfold oevl; repeat rewrite otrans_appl; unfold otrans; simpl.
  repeat rewrite <- zappl_toZContext.
  rewrite invert_zappl_zget.
  unfold clift, comap.
  repeat rewrite <- appl_fromZContext.
  rewrite put_or_G.
  repeat rewrite <- zappl_toZContext.
  repeat rewrite (toZContext_fromZContext).
  change (zappl ?z
     (fun env : Env (S :: E1) =>
      Put (v (tail env)) (Or Fail (Put (head env) Fail))))
   with
     (zappl (ZPut z (fun env => v (tail env)))
     (fun env : Env (S :: E1) =>
      Or Fail (Put (head env) Fail))).
  rewrite <- appl_fromZContext.
  rewrite or_fail.
  rewrite appl_fromZContext.
  simpl.
  rewrite invert_zappl_zget.
  rewrite <- appl_fromZContext.
  unfold clift, cpush, comap.
  rewrite put_put_G.
  rewrite appl_fromZContext.
  simpl.
  unfold cpush, comap.
  unfold head, head_.
  rewrite <- appl_fromZContext.
  rewrite get_put_G.
  rewrite appl_fromZContext.
  reflexivity.
Qed.

Lemma put_or_trans:
  forall {E1 A} (p: OProg E1 A)
         {E2 B} (c: Context E1 A E2 B) (v: Env E1 -> S) (q: OProg E1 A),
    orun (appl c (fun env => Put (v env) (Or (otrans p env) (q env))))
    =
    orun (appl c (fun env => Or (Put (v env) (otrans p env)) (Put (v env) (q env)))).
Proof.
  intros E1 A p E2 B c v q.
  induction c; simpl.

  (* Proof for empty context *)
  - unfold orun, otrans; apply functional_extensionality; intro env.
    induction (p env). 
    + simpl trans.
      rewrite <- put_ret_or_G.
      reflexivity.
    + simpl trans.
      rewrite put_or_G'.
      change (run (Put ?s ?k)) with (putD s (run k)).
      repeat rewrite or_fail'.
      change (putD ?s (run ?p)) with (run (Put s p)).
      rewrite put_put_G'.
      reflexivity.
    + simpl trans.
      change (run (Put ?s ?p)) with (putD s (run p)).
      rewrite or_or'.
      rewrite <- run_put.
      change (Or (trans p0_2) (q env))
        with ((fun env => Or (trans p0_2) (q env)) env).
      rewrite (IHp0_1(fun env => Or (trans p0_2) (q env))).
      rewrite run_or.
      rewrite IHp0_2; auto.
      rewrite <- run_or.
      rewrite <- or_or'.
      rewrite run_or.
      change (trans p0_2) with ((fun env => trans p0_2) env) at 1.
      rewrite <- IHp0_1.
      rewrite <- run_or; auto.
      auto.
    + simpl trans.

      rewrite run_or.
      rewrite put_get_G'.
      rewrite <- run_or.

      rewrite <- H; auto.

      generalize (v env). intro.
      change (Or (trans (p0 s)) (q env))
        with ((fun s' => Or (trans (p0 s')) (q env)) s).
      rewrite <- put_get_G'.

      repeat rewrite run_put.
      rewrite get_or_G'.
      reflexivity.

    + simpl trans.
      rewrite <- put_or_G'.

      repeat rewrite run_or.
      rewrite put_get_G'.
      repeat rewrite <- run_or.

      rewrite put_or_G'; rewrite put_or_G'.
      rewrite run_put; rewrite run_put.
      repeat rewrite or_or'.
      rewrite run_or.
      rewrite put_or_G'.
      rewrite run_or.
      rewrite put_or_G'.
      repeat rewrite run_put.
      repeat rewrite or_fail'.
      rewrite <- run_put.
      rewrite <- run_put.
      rewrite <- run_put.
      rewrite put_put_G'.
      reflexivity.

  (* Proofs for non-empty context *)
  - repeat rewrite orun_or.
    apply functional_extensionality; intro.
    change (orD ?t (orun o x)) with ((fun u => orD u (orun o x)) t).
    f_equal.
    rewrite IHc.
    reflexivity.

  - repeat rewrite orun_or.
    apply functional_extensionality; intro env.
    f_equal.
    rewrite IHc.
    reflexivity.

  - repeat rewrite orun_put.
    apply functional_extensionality; intro env.
    f_equal.
    rewrite IHc.
    reflexivity.

  - repeat rewrite orun_get.
    apply functional_extensionality; intro env.
    f_equal.
    apply functional_extensionality; intro s.
    destruct (b s); auto.
    unfold cpush, comap.
    unfold orun.
    change (run (appl c ?p ?e)) with (orun (appl c p) e).
    rewrite IHc.
    reflexivity.

  - unfold orun.
    apply functional_extensionality; intro env.
    destruct (b env); auto.
    change (run (appl c ?p ?e)) with (orun (appl c p) e).
    rewrite IHc.
    reflexivity.
    
  - unfold orun, cpush, comap.
    change (run (appl c0 ?p ?e)) with (orun (appl c0 p) e).
    rewrite IHc.
    reflexivity.

  - unfold orun, clift, comap.
    change (run (appl c ?p ?e)) with (orun (appl c p) e).
    rewrite IHc.
    reflexivity.
Qed.

Lemma get_put_L_1:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (p: OProg E1 A),
    oevl (appl c (fun env => Get (fun s => Put s (p env))))
    =
    oevl (appl c p).
Proof.
  intros. unfold oevl. repeat rewrite otrans_appl. unfold otrans. simpl.
  rewrite get_get_G.
  repeat rewrite <- zappl_toZContext.
  rewrite invert_zappl_zget.
  unfold clift, comap.
  repeat rewrite <- appl_fromZContext.
  rewrite put_or_G.
  rewrite <- zappl_toZContext.
  repeat rewrite toZContext_fromZContext.
  simpl; unfold cpush, comap, head, head_, tail, tail_.
  rewrite invert_zappl_zget.
  unfold clift, comap.
  rewrite <-  appl_fromZContext.
  rewrite <- put_or_G.
  change (fun env : Env (S :: E1) =>
      Or (Put (head env) (trans (p (tail env)))) (Put (head env) Fail))
    with (fun env : Env (S :: E1) =>
      Or (Put (head env) (otrans (fun env => p (tail env)) env)) (Put (head env) ((fun env => Fail) env))).
  rewrite <- put_or_trans.
  rewrite appl_fromZContext.
  simpl.
  unfold cpush, comap, head, head_.
  change (fun env : Env E1 =>
      Get
        (fun s : S =>
         Put s
           (Or (otrans (fun env0 : Env (S :: E1) => p (tail env0)) (Cons s env))
              Fail)))
     with 
 (fun env : Env E1 =>
      Get
        (fun s : S =>
         Put s
           (Or (otrans (fun env0 : Env (E1) => p env0) env)
              Fail))).
  rewrite zappl_toZContext.
  rewrite get_put_G.
  rewrite appl_fromZContext.
  rewrite zappl_toZContext.
  rewrite fail_or.
  auto.
Qed.

Lemma put_put_L_1:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (v: Env E1 -> S) (w: Env E1 -> S) (p: OProg E1 A),
    oevl (appl c (fun env => Put (v env) (Put (w env) (p env))))
    =
    oevl (appl c (fun env => Put (w env) (p env))).
Proof.
  intros.
  unfold oevl.
  repeat rewrite otrans_appl.
  unfold otrans.
  simpl.
  rewrite <- zappl_toZContext.
  rewrite invert_zappl_zget_or.
  unfold clift, comap.
  rewrite <- appl_fromZContext.
  rewrite put_get_G.
  rewrite <- put_or_G.
  rewrite appl_fromZContext.
  change (zappl ?z (fun env => Or (Put (v (tail env))
           (Put (w (tail env)) (trans (p (tail env))))) (Put (v (tail env)) Fail)))
     with (zappl (ZOr1 z (fun env => (Put (v (tail env)) Fail))) (fun env => Put (v (tail env))
           (Put (w (tail env)) (trans (p (tail env)))))). 
  rewrite <- appl_fromZContext.
  rewrite put_put_G.
  rewrite appl_fromZContext. 
  simpl.
  unfold cpush, comap.
  rewrite invert_zappl_zget.
  rewrite <- appl_fromZContext.
  unfold clift, comap.
  rewrite or_or.
  rewrite <- zappl_toZContext.
  rewrite invert_zappl_zor2.
  rewrite <- appl_fromZContext.
  rewrite put_or_G.
  rewrite appl_fromZContext.
  rewrite invert_zappl_zput.
  rewrite <- appl_fromZContext.
  rewrite or_fail.
  rewrite appl_fromZContext.
  rewrite <- invert_zappl_zput.
  rewrite <- appl_fromZContext.
  rewrite put_put_G.
  rewrite appl_fromZContext.
  simpl.
  rewrite zappl_toZContext.
  rewrite appl_fromZContext.
  simpl.
  unfold cpush, comap.
  unfold tail, tail_, head, head_.
  rewrite zappl_toZContext.
  auto.
Qed.

(* We don't just want to prove these laws for bind-free contexts, but also for contexts
   in which monadic bind operators may occur.
   First step: generalize proofs of the form
     `oevl (appl c p)         = oevl (appl c q)` to
     `oevl (appl c (p >>= k)) = oevl (appl c (q >>= k))`
   Then we define contexts with binds and the associated infrastructure.
   Finally, we prove a lemma `bapp_from_appl` that lets us generalize our proofs to
   proofs for arbitrary contexts with bind.
*)
Lemma get_get_L_2:
  forall {A B C E1 E2} (c: Context E1 C E2 B) (k: S -> S -> OProg E1 A) (q: A -> OProg E1 C),
    oevl (appl c (obind (fun env => Get (fun s1 => Get (fun s2 => k s1 s2 env))) q))
    =
    oevl (appl c (obind (fun env => Get (fun s1 => k s1 s1 env)) q)).
Proof.
  intros A B C E1 E2 c k q.
  unfold obind; simpl. rewrite get_get_L_1; auto.
Qed.

Lemma put_get_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (k: S -> OProg E1 A) (v: S) q,
    oevl (appl c (obind (fun env => Put v (Get (fun s => k s env)) ) q))
    =
    oevl (appl c (obind (fun env => Put v (k v env)) q)).
Proof.
  intros; unfold obind; simpl; apply put_get_L_1.
Qed.

Lemma get_put_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (p: OProg E1 A) (q: A -> OProg E1 B),
    oevl (appl c (obind (fun env => Get (fun s => Put s (p env))) q))
    =
    oevl (appl c (obind p q)).
Proof.
    intros; unfold obind; simpl; apply get_put_L_1.
Qed.

Lemma put_fail_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (v: Env E1 -> S) (q: A -> OProg E1 B),
    oevl (appl c (obind (fun env => Put (v env) Fail) q))
   = 
   oevl (appl c (obind (fun env => Fail) q)).
Proof.
  intros; unfold obind; simpl; apply put_fail_L_1.
Qed.

Lemma put_put_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (v: Env E1 -> S) (w: Env E1 -> S) (p: OProg E1 A) (k: A -> OProg E1 B),
    oevl (appl c (obind (fun env => Put (v env) (Put (w env) (p env))) k))
    =
    oevl (appl c (obind (fun env => Put (w env) (p env)) k)).
Proof.
    intros; unfold obind; simpl; apply put_put_L_1.
Qed.

(* Contexts with bind *)
Inductive BContext : list Type -> Type -> list Type -> Type -> Type :=
  | BHole  : forall {E A}        , BContext E A E A

  | BOr1   : forall {E1 E2 A B}  , BContext E1 A E2 B ->
                                   OProg E2 B ->
                                   BContext E1 A E2 B

  | BOr2   : forall {E1 E2 A B}  , OProg E2 B ->
                                   BContext E1 A E2 B ->
                                   BContext E1 A E2 B

  | BPut   : forall {E1 E2 A B}  , (Env E2 -> S) ->
                                   BContext E1 A E2 B ->
                                   BContext E1 A E2 B

  | BGet   : forall {E1 E2 A B}  , (S -> bool) ->
                                   (BContext E1 A (S::E2) B) ->
                                   (S -> OProg E2 B) ->
                                   BContext E1 A E2 B

  | BDelay : forall {E1 E2 A B}  , (Env E2 -> bool) ->
                                   BContext E1 A E2 B ->
                                   OProg E2 B ->
                                   BContext E1 A E2 B

  | BPush  : forall {E1 E2 A B C}, C ->
                                   BContext E1 A (C::E2) B ->
                                   BContext E1 A E2 B

  | BLift  : forall {E1 E2 A B C}, BContext E1 A E2 B ->
                                   BContext E1 A (C::E2) B

  (* [] >>= k *)
  | BBind1 : forall {E1 E2 A B C}, BContext E1 A E2 B ->
                                   (B -> OProg E2 C) ->
                                   BContext E1 A E2 C

  (* m >>= \x -> [] *)
  | BBind2 : forall {E1 E2 A B C}, OProg E2 A ->
                                   BContext E1 B (A::E2) C ->
                                   BContext E1 B E2 C.

(* Zipper variant of context with bind *)
Inductive ZBContext : list Type -> Type -> list Type -> Type -> Type :=
| ZBTop   : forall {E A}, ZBContext E A E A
              
| ZBOr1   : forall {E1 E2 A B}, ZBContext E1 A E2 B ->
                                OProg E1 A ->
                                ZBContext E1 A E2 B
                                                   
| ZBOr2   : forall {E1 E2 A B}, ZBContext E1 A E2 B ->
                                OProg E1 A ->
                                ZBContext E1 A E2 B
                                                   
| ZBPut   : forall {E1 E2 A B}, ZBContext E1 A E2 B ->
                                (Env E1 -> S) ->
                                ZBContext E1 A E2 B
                                                      
| ZBGet   : forall {E1 E2 A B}, ZBContext E1 A E2 B ->
                                (S -> bool) ->
                                (S -> OProg E1 A) ->
                                ZBContext (S::E1) A E2 B
                                                                         
| ZBDelay : forall {E1 E2 A B}, ZBContext E1 A E2 B ->
                                (Env E1 -> bool) ->
                                OProg E1 A ->
                                ZBContext E1 A E2 B
                                                                       
| ZBPush  : forall {E1 E2 A B C}, ZBContext E1 A E2 B ->
                                  C ->
                                  ZBContext (C::E1) A E2 B
                                          
| ZBLift  : forall {E1 E2 A B C}, ZBContext (C::E1) A E2 B ->
                                  ZBContext E1 A E2 B
(* [] >>= k *)
| ZBBind1 : forall {E1 E2 A B C}, ZBContext E1 B E2 C ->
                                  (A -> OProg E1 B) ->
                                  ZBContext E1 A E2 C

(* m >>= \x -> [] *)
| ZBBind2 : forall {E1 E2 A B C}, ZBContext E1 B E2 C ->
                                  OProg E1 A ->
                                  ZBContext (A::E1) B E2 C.


Fixpoint bappl {E1 E2: list Type} {A B: Type} (c: BContext E1 A E2 B)  : OProg E1 A -> OProg E2 B :=
  match c in (BContext E1 A E2 B) return (OProg E1 A -> OProg E2 B) with
  | BHole        => (fun p env => p env)
  | BOr1 c q     => (fun p env => Or (bappl c p env) (q env))
  | BOr2 p c     => (fun q env => Or (p env) (bappl c q env))
  | BPut v c     => (fun p env => Put (v env) (bappl c p env)) 
  | BGet t c q   => (fun p env => Get (fun s =>
                                         if t s then cpush s (bappl c p) env else q s env))
  | BDelay t c q => (fun p => (fun env => if t env then bappl c p env else q env))
  | BPush x c    => (fun p env => cpush x (bappl c p) env)
  | BLift c      => (fun p env => clift (bappl c p) env)
  | BBind1 c k   => (fun p env => bind (bappl c p env) (fun x => k x env))
  | BBind2 p c   => (fun q env => bind (p env) (fun x => cpush x (bappl c q) env))
  end.

Fixpoint zbappl {E1 E2: list Type} {A B : Type} (z: ZBContext E1 A E2 B) : OProg E1 A -> OProg E2 B :=
  match z in (ZBContext E1 A E2 B) return (OProg E1 A -> OProg E2 B) with
  | ZBTop         => (fun p env => p env)
  | ZBOr1 z q     => (fun p     => zbappl z (fun env => Or (p env) (q env)))
  | ZBOr2 z p     => (fun q     => zbappl z (fun env => Or (p env) (q env)))
  | ZBPut z v     => (fun p     => zbappl z (fun env => Put (v env) (p env)))
  | ZBGet z t q   => (fun p     =>
                        zbappl z (fun env =>
                                   Get (fun s => if t s
                                                 then (cpush s p) env
                                                 else q s env)))
  | ZBDelay z t q => (fun p     =>
                        zbappl z (fun env =>
                                    if t env then p env else q env))
  | ZBPush z c    => (fun p     => zbappl z (cpush c p))
  | ZBLift z      => (fun p     => zbappl z (clift p))
(* p : OProg E1 A
   zbappl z: OProg E1 A -> OProg E2 B
 *)
  | ZBBind1 z k => fun p => zbappl z (fun env => bind (p env) (fun x => k x env))
  | ZBBind2 z m => fun p => zbappl z (fun env =>
                                        bind (m env) (fun x => cpush x p env))
  end.

Fixpoint toZBContext_ {E1 E2 A B} (c: BContext E1 A E2 B):
  (forall {E3 C}, ZBContext E2 B E3 C -> ZBContext E1 A E3 C) :=
  match c in (BContext E1 A E2 B) return ((forall {E3 C}, ZBContext E2 B E3 C-> ZBContext E1 A E3 C)) with
   | BHole        => (fun _ _ z => z)
   | BOr1 c p     => (fun _ _ z => toZBContext_ c (ZBOr1 z p))
   | BOr2 p c     => (fun _ _ z => toZBContext_ c (ZBOr2 z p))
   | BPut s c     => (fun _ _ z => toZBContext_ c (ZBPut z s))
   | BGet t c p   => (fun _ _ z => toZBContext_ c (ZBGet z t p))
   | BDelay t c p => (fun _ _ z => toZBContext_ c (ZBDelay z t p))
   | BPush a c    => (fun _ _ z => toZBContext_ c (ZBPush z a))
   | BLift c      => (fun _ _ z => toZBContext_ c (ZBLift z))
   | BBind1 c k   => (fun _ _ z => toZBContext_ c (ZBBind1 z k))
   | BBind2 p c   => (fun _ _ z => toZBContext_ c (ZBBind2 z p))
  end.

Definition toZBContext {E1 E2 A B} (c: BContext E1 A E2 B): ZBContext E1 A E2 B := toZBContext_ c ZBTop.
 
Lemma zbappl_toZBContext_:
   forall {E1 E2 A B} (c: BContext E1 A E2 B) {E3 C} (z: ZBContext E2 B E3 C) (p: OProg E1 A),
     zbappl (toZBContext_ c z) p = zbappl z (bappl c p).
Proof.
  intros E1 E2 A B c; induction c; intros E3 D z prog; simpl; auto; rewrite IHc; auto.
Qed.

Lemma zbappl_toZBContext:
   forall {E1 E2 A B} (c: BContext E1 A E2 B) (p: OProg E1 A),
     zbappl (toZBContext c) p = bappl c p.
Proof.
  intros; unfold toZBContext; rewrite zbappl_toZBContext_; simpl; reflexivity.
Qed.

Fixpoint fromZBContext_ {E2 E3: list Type} {B C: Type} (z: ZBContext E2 B E3 C)  : forall {E1 A}, BContext E1 A E2 B -> BContext E1 A E3 C :=
  match z in (ZBContext E2 B E3 C) return (forall {E1 A}, BContext E1 A E2 B -> BContext E1 A E3 C) with
  | ZBTop         => (fun _ _ c => c)
  | ZBOr1 z q     => (fun _ _ c => fromZBContext_ z (BOr1 c q)) 
  | ZBOr2 z p     => (fun _ _ c => fromZBContext_ z (BOr2 p c))
  | ZBPut z v     => (fun _ _ c => fromZBContext_ z (BPut v c))
  | ZBGet z t q   => (fun _ _ c => fromZBContext_ z (BGet t c q))
  | ZBDelay z t q => (fun _ _ c => fromZBContext_ z (BDelay t c q))
  | ZBPush z x    => (fun _ _ c => fromZBContext_ z (BPush x c))
  | ZBLift z      => (fun _ _ c => fromZBContext_ z (BLift c))
  | ZBBind1 z k   => (fun _ _ c => fromZBContext_ z (BBind1 c k))
  | ZBBind2 z q   => (fun _ _ c => fromZBContext_ z (BBind2 q c))
  end.

Definition fromZBContext {E1 E2: list Type} {A B: Type} (z: ZBContext E1 A E2 B)  : BContext E1 A E2 B :=
  fromZBContext_ z BHole. 

Lemma bappl_fromZBContext_:
  forall {B C E2 E3} (z: ZBContext E2 B E3 C) {E1 A} (c: BContext E1 A E2 B) (p: OProg E1 A),
       bappl (fromZBContext_ z c) p = zbappl z (bappl c p).
Proof.
  intros. induction z; intros; auto; simpl; rewrite IHz; auto.
Qed.

Lemma bappl_fromZBContext:
  forall {A B E1 E2} (z: ZBContext E1 A E2 B) (p: OProg E1 A),
       bappl (fromZBContext z) p = zbappl z p.
Proof.
  intros; unfold fromZBContext; rewrite bappl_fromZBContext_; auto.
Qed.

Lemma invert_zbappl_zbor1:
  forall {E1 E2 A B} (z: ZBContext E1 A E2 B)  (p q: OProg E1 A),
     zbappl z (fun env => Or (p env) (q env))
     =
     zbappl (ZBOr1 z q) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zbor2:
  forall {E1 E2 A B} (z: ZBContext E1 A E2 B)  (p q: OProg E1 A),
     zbappl z (fun env => Or (p env) (q env))
     =
     zbappl (ZBOr2 z p) q.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zbput:
  forall {E1 E2 A B} (z: ZBContext E1 A E2 B) (v: Env E1 -> S) (q: OProg E1 A),
     zbappl z (fun env => Put (v env) (q env))
     =
     zbappl (ZBPut z v) q.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zbdelay:
  forall {E1 E2 A B}
         (z: ZBContext E1 A E2 B) (t: Env E1 -> bool) (p q: OProg E1 A),
    zbappl z (fun env => if t env then p env else q env)
    =
    zbappl (ZBDelay z t q) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zbpush:
  forall {E1 E2 A B C}
         (z: ZBContext E1 A E2 B) (x: C) (p: OProg (C::E1) A),
    zbappl z (cpush x p)
    =
    zbappl (ZBPush z x) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zblift:
  forall {E1 E2 A B C}
         (z: ZBContext (C::E1) A E2 B) (x: C) (p: OProg E1 A),
    zbappl z (clift p)
    =
    zbappl (ZBLift z) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zbbind1:
  forall {E1 E2 A B C}
         (z: ZBContext E1 B E2 C) (p: OProg E1 A) (k: A -> OProg E1 B),
    zbappl z (obind p k)
    =
    zbappl (ZBBind1 z k) p.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma invert_zbappl_zbbind2:
  forall {E1 E2 A B C}
         (z: ZBContext E1 B E2 C) (p: OProg E1 A) (q: OProg (A::E1) B),
    zbappl z (obind p (fun x => cpush x q))
    =
    zbappl (ZBBind2 z p) q.
Proof.
  intros; simpl; unfold cpush, clift, comap, head, tail, head_, tail_; auto.
Qed.

Lemma obind_clift:
  forall {E1 A} (p q: OProg E1 A)
         (P : forall {C : Type}
                     {E2 : list Type}
                     {B : Type}
                     (c : Context E1 C E2 B)
                     (k : A -> OProg E1 C),
             oevl (appl c (obind p k)) = oevl (appl c (obind q k))),
    (forall {C0 C: Type}
            {E0 : list Type}
            {B0 : Type}
            (c : Context (C :: E1) C0 E0 B0)
            (k : A -> OProg (C :: E1) C0),
        oevl (appl c (obind (clift p) k)) = oevl (appl c (obind (clift q) k))).
Proof.
  intros; dependent induction c.
  - simpl.
    assert (forall p, (fun env : Env (C :: E1) => obind (clift p) k env) =
            (fun env : Env (C :: E1) => obind (clift p) k (Cons (head env) (tail env)))).
    + intros. apply functional_extensionality; intro env. 
      rewrite cons_head_tail; auto.
    + rewrite H; rewrite (H q). 
      unfold obind.


      change (fun env : Env (C :: E1) =>
                bind (clift ?p (Cons (head env) (tail env)))
                     (fun x : A => k x (Cons (head env) (tail env))))
        with (fun env : Env (C :: E1) =>
                (obind p (fun (x : A) env'' => k x (Cons (head env) env'')))
                  (tail env)).
      change (oevl (fun env : Env (C :: E1) =>
                      obind ?p
                            (fun (x : A) (env'' : Env E1) =>
                               k x (Cons (head env) env'')) (tail env)))
        with 
          (fun env : Env (C :: E1) =>
             oevl ((fun e : Env E1 =>
                      obind p
                            (fun (x : A) (env'' : Env E1) =>
                               k x (Cons (head env) env'')) e)) (tail env)).
      apply functional_extensionality; intro env.
      pose proof (P _ _ _ CHole (fun (x : A) (env'' : Env E1) =>
                                   k x (Cons (head env) env''))).
      unfold appl in H0.
      rewrite H0.
      reflexivity.
  - simpl appl.
    repeat rewrite oevl_or.
    apply functional_extensionality; intro env.
    rewrite (IHc E1 p q P); auto.
  - simpl appl.
    repeat rewrite oevl_or.
    apply functional_extensionality; intro env.
    rewrite (IHc E1 p q P); auto.
  - simpl appl.
    repeat rewrite oevl_put.
    apply functional_extensionality; intro env.
    rewrite (IHc E1 p q P); auto.
  - simpl appl.
    repeat rewrite oevl_get.
    apply functional_extensionality; intro env.
    apply f_equal.
    apply functional_extensionality; intro s.
    destruct (b s); auto.
    unfold cpush, comap.
    unfold obind.
    change (oevl (fun env0 => appl c ?f (Cons s env0)) env)
      with (oevl (appl c f) (Cons s env)).
    change (oevl
              (appl c
                    (fun env0 => bind (clift ?r env0) (fun x => k x env0)))
              (Cons s env))
      with (oevl (appl c (obind (clift r) k)) (Cons s env)).
    rewrite (IHc E1 p q P); auto.

  - simpl.
    unfold oevl, orun, otrans.
    apply functional_extensionality; intro env.
    destruct (b env); auto.
    change (run (trans (appl c (obind (clift ?r) k) env)))
      with (oevl (appl c (obind (clift r) k)) env).
    rewrite (IHc E1 p q P); auto.
  - simpl appl.
    unfold cpush, comap.
    change (oevl (fun env => appl c1 (obind (clift ?r) k) (Cons c env)))
      with (fun env0 => (oevl (fun env => appl c1 (obind (clift r) k) env) (Cons c env0))).
    apply functional_extensionality; intro env0.
    rewrite (IHc E1 p q P); auto.
  - simpl.
    unfold clift at 1; unfold clift at 2. unfold comap.
    change (oevl (fun env : Env (C0 :: E2) => ?f (tail env)))
      with (fun env : Env (C0 :: E2) => oevl f (tail env)).
    rewrite (IHc E1 p q P); reflexivity.
Qed.

Lemma bapp_from_appl:
  forall {A B E1 E2} (p q: OProg E1 A)
         (P: forall {C E2 B} (c: Context E1 C E2 B) (k: A -> OProg E1 C),
             oevl (appl c (obind p k)) = oevl (appl c (obind q k)))
         (b: BContext E1 A E2 B),
    oevl (bappl b p) = oevl (bappl b q).


Proof.
  intros a B E1 E2 p q P b.
  repeat rewrite <- zbappl_toZBContext.
  induction (toZBContext b).
  - simpl.
    change (fun env => ?r env)
      with (appl CHole (fun env => r env)).
    assert (H: forall (r : OProg E A),
               (fun env => r env) = (obind r (fun x _ => Return x))).
    + intro r. unfold obind.
      apply functional_extensionality; intro env.
      rewrite bind_return.
      reflexivity.
    + rewrite (H p); rewrite (H q); apply P.
  - repeat rewrite <- invert_zbappl_zbor1.
    apply IHz.
    intros.
    unfold obind.
    assert (H: forall (r: OProg E1 A),
               (fun env => bind (Or (r env) (o env)) (fun x => k x env))
               =
               (fun env =>
                  Or (bind (r env) (fun x => k x env))
                     (bind (o env) (fun x => k x env)))).
    + intro r; apply functional_extensionality; intro env.
      rewrite bind_or_left. reflexivity.
    + rewrite (H p); rewrite (H q).
      repeat rewrite <- zappl_toZContext.
      repeat rewrite invert_zappl_zor1.
      repeat rewrite <- appl_fromZContext.
      change (fun env => bind (?r env) (fun x => k x env))
        with (obind r k).
      apply P.
    + apply b.
  - repeat rewrite <- invert_zbappl_zbor2.
    apply IHz.
    intros.
    unfold obind.
    assert (H: forall (r: OProg E1 A),
               (fun env => bind (Or (o env) (r env)) (fun x => k x env))
               =
               (fun env =>
                  Or (bind (o env) (fun x => k x env))
                     (bind (r env) (fun x => k x env)))).
    + intro r; apply functional_extensionality; intro env.
      apply bind_or_left.
    + rewrite (H p); rewrite (H q).
      repeat rewrite <- zappl_toZContext.
      repeat rewrite invert_zappl_zor2.
      repeat rewrite <- appl_fromZContext.
      apply P.
    + apply b.
  - repeat rewrite <- invert_zbappl_zbput; apply IHz; intros; unfold obind.
    assert (H: forall (r: OProg E1 A),
               (fun env => bind (Put (s env) (r env)) (fun x => k x env))
               =
               (fun env =>
                  Put (s env) (bind (r env) (fun x => k x env)))).
    + auto.
    + rewrite (H p); rewrite (H q).
      repeat rewrite <-zappl_toZContext;
        repeat rewrite invert_zappl_zput;
        repeat rewrite <- appl_fromZContext.
      apply P.
    + apply b.
  - repeat rewrite <- invert_zbappl_zbget.
    apply IHz.
    intros.
    unfold obind.
    assert (H: forall (r: OProg (S :: E1) A),
               (fun env =>
                  bind (Get (fun s =>
                               if b0 s then cpush s r env else o s env))
                       (fun x => k x env))
               =
               (fun env =>
                  Get (fun s
                       => if b0 s
                          then cpush s (fun env' =>
                                          bind (r env')
                                               (fun x => k x env)) env
                          else bind (o s env) (fun x => k x env)))).
    + intro r; apply functional_extensionality; intro env.
      simpl.
      assert (H':
                (fun s => bind (if b0 s then cpush s r env else o s env)
                               (fun x => k x env))
                =
                (fun s => if b0 s
                          then cpush s
                                     (fun env' =>
                                        bind (r env') (fun x => k x env))
                                     env
                          else bind (o s env) (fun x => k x env))).
      * apply functional_extensionality; intro s.
        rewrite bind_if.
        unfold cpush, comap.
        reflexivity.
      * rewrite H'; reflexivity.
    + rewrite (H p); rewrite (H q).
      repeat rewrite <- zappl_toZContext.
      repeat rewrite invert_zappl_zget.
      unfold clift, comap, cpush, comap.
      repeat rewrite invert_zappl_zdelay.
      repeat rewrite <- appl_fromZContext.


      assert (H': forall (r: OProg (S::E1) A),
                 (fun env => bind (r (Cons (head env) (tail env)))
                                  (fun x => k x (tail env)))
                 =
                 (obind r (fun x env => k x (tail env)))).
      * intro r.
        unfold obind.
        apply functional_extensionality; intro env.
        rewrite cons_head_tail.
        reflexivity.
      * rewrite (H' p); rewrite (H' q).
        apply P.
    + apply (fromZBContext z).
  - repeat rewrite <- invert_zbappl_zbdelay.
    apply IHz.
    + intros. unfold obind.
    assert (H: forall (r: OProg E1 A),
               (fun env => bind (if b0 env then r env else o env)
                                (fun x => k x env))
               =
               (fun env => if b0 env
                           then bind (r env) (fun x => k x env)
                           else bind (o env) (fun x => k x env))).
    intro r; apply functional_extensionality; intro env.
    apply bind_if.
    rewrite (H p); rewrite (H q).
    repeat rewrite <- zappl_toZContext.
    repeat rewrite invert_zappl_zdelay.
    repeat rewrite <- appl_fromZContext.
    rewrite obind_from_bind.
    apply P.
    + apply b.
  - repeat rewrite <- invert_zbappl_zbpush.
    apply IHz. intros. unfold obind.
    assert (H: forall (r: OProg (C :: E1) A),
               (fun env => bind (cpush c r env) (fun x => k x env))
               =
               (cpush c (fun env' => bind (r env')
                                          (fun x => k x (tail env'))))).
    intro r; apply functional_extensionality; intro env.
    unfold cpush, comap.
    simpl.
    reflexivity.
    rewrite (H p); rewrite (H q).
    repeat rewrite <- zappl_toZContext.
    repeat rewrite invert_zappl_zpush.
    repeat rewrite <- appl_fromZContext.
    repeat rewrite obind_from_bind.
    apply P.
    apply (fromZBContext z).
  - simpl.
    apply IHz.
    + intros; apply obind_clift; auto. 
    + apply (fromZBContext z).
  - repeat rewrite <- invert_zbappl_zbbind1.
    apply IHz. intros.
    repeat rewrite obind_obind.
    apply P.
    apply (fromZBContext z).
  - repeat rewrite <- invert_zbappl_zbbind2.
    apply IHz; intros.
    change (oevl (appl c ?b))
      with (fun env => oevl (appl c b) env).
    apply functional_extensionality; intro env.
    apply Meta1.
    intros; apply P.
    apply (fromZBContext z).
Qed.
    

Lemma get_get_L:
  forall {A B E1 E2}
         (c: BContext E1 A E2 B) (k: S -> S -> OProg E1 A),
    oevl (bappl c (fun env => Get (fun s1 => Get (fun s2 => k s1 s2 env))))
    =
    oevl (bappl c (fun env => Get (fun s1 => k s1 s1 env))).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply get_get_L_2.
Qed.

Lemma get_put_L:
  forall {A B E1 E2}
         (c: BContext E1 A E2 B) (p: OProg E1 A),
    oevl (bappl c (fun env => Get (fun s => Put s (p env))))
    =
    oevl (bappl c p).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply get_put_L_2.
Qed.

Lemma put_get_L:
  forall {A B E1 E2}
         (c: BContext E1 A E2 B) (k: S -> OProg E1 A) (v: S),
    oevl (bappl c (fun env => Put v (Get (fun s => k s env))))
    =
    oevl (bappl c (fun env => Put v (k v env))).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply put_get_L_2.
Qed.

Lemma put_put_L:
  forall {A B E1 E2}
         (c: BContext E1 A E2 B) (v: Env E1 -> S) (w: Env E1 -> S) (p: OProg E1 A),
    oevl (bappl c (fun env => Put (v env) (Put (w env) (p env))))
    =
    oevl (bappl c (fun env => Put (w env) (p env))).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply put_put_L_2.
Qed.

Lemma put_fail_L:
  forall {E1 E2 A B} (c: BContext E1 A E2 B) (v: Env E1 -> S),
  oevl (bappl c (fun env => Put (v env) Fail))
  =
  oevl (bappl c (fun env => Fail)).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply put_fail_L_2.
Qed.

(* Now we get to proving the local state laws. *)
Lemma right_zero_L_0:
  forall {A B} (m: Prog A),
    evl (bind m (fun x => Fail))
    =
    evl (Fail : Prog B).
Proof.
  intros.
  induction m .
  - unfold bind; reflexivity.
  - unfold bind; reflexivity.
  - rewrite bind_or_left.
    rewrite evl_or.
    rewrite IHm1, IHm2.
    unfold evl.
    simpl.
    apply or1_fail_G_D.
  - change (bind (Get p) (fun _ => Fail))
      with (Get (fun s => (bind (p s) (fun _ => Fail : Prog B)))).
    rewrite evl_get.
    assert (H': (fun s => evl (bind (p s) (fun _ => Fail : Prog B)))
                =
                (fun s => evl Fail)).
    + apply functional_extensionality; intro s.
      apply H.
    + rewrite H'.
      unfold evl, trans, run.
      apply get_const.
  - change (bind (Put s m) ?k)
      with (Put s (bind m k)).
    change (evl (Put s ?k))
      with (getD (fun s0 => orD (putD s (evl k)) (putD s0 failD))).
    rewrite IHm.
    change (getD (fun s0 => orD (putD s (evl Fail)) (putD s0 failD)))
      with (evl (Put s (Fail: Prog B))).
    rewrite put_fail_L_0.
    reflexivity.
Qed.

Lemma right_zero_L_1':
  forall {E1 E2 A B C X} (c: Context E1 C E2 B) (m: X -> Prog A) (f: Env E1 -> X),
    oevl (appl c (fun env => bind (m (f env)) (fun x => Fail)))
    =
    oevl (appl c (fun env => Fail)).
Proof.
  intros.
  change (fun env => bind (m (f env)) (fun x => Fail))
    with (fun env => (fun x => bind (m x) (fun x => (Fail: Prog C))) (f env)).
  change (fun env: Env E1 => Fail)
    with (fun env: Env E1 => (fun x => (Fail: Prog C)) (f env)).
  apply evl_meta.
  intro x.
  apply right_zero_L_0.
Qed.

Lemma right_zero_L_1:
  forall {E1 E2 A B C} (c: Context E1 C E2 B) (m: OProg E1 A),
    oevl (appl c (fun env => bind (m env) (fun x => Fail)))
    =
    oevl (appl c (fun env => Fail)).
Proof.
  intros.
  apply right_zero_L_1'.
Qed.

Lemma right_zero_L_2:
  forall {E1 E2 A B C} (c: Context E1 C E2 B) (m: OProg E1 A) (q: A -> OProg E1 C),
    oevl (appl c (obind (fun env => bind (m env) (fun x => Fail)) q))
    =
    oevl (appl c (obind (fun env => Fail) q)).
Proof.
  intros.
  unfold obind.
  assert (H:
            (fun env => bind (bind (m env)
                                   (fun _ => Fail))
                             (fun x => q x env))
            =
            (fun env => bind (m env) (fun _ => Fail))).
  - apply functional_extensionality; intro env.
    rewrite bind_bind.
    simpl.
    reflexivity.
  - rewrite H.
    simpl.
    apply right_zero_L_1.
Qed.

Lemma right_zero_L:
  forall {E1 E2 A B}
         (c: BContext E1 A E2 B) (m: OProg E1 A),
    oevl (bappl c (fun env => bind (m env) (fun x => Fail)))
    =
    oevl (bappl c (fun env => Fail)).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply right_zero_L_2.
Qed.

Lemma get_swap_vars:
  forall {A} (k : S -> D A),
    getD (fun _ => getD (fun s => k s))
    =
    getD (fun t => getD (fun _ => k t)).
Proof.
  intros.
  repeat rewrite get_get_G_D.
  reflexivity.
Qed.

Lemma get_get_or_lambdas_G':
  forall {A} (p q : S -> Prog A),
    run (Get (fun s1 => Get (fun s2 => Or (p s1) (q s1))))
    =
    run (Get (fun s1 => Get (fun s2 => Or (p s2) (q s1)))).
Proof.
  intros.
  repeat rewrite get_get_G'.
  reflexivity.
Qed.

Lemma get_or_trans:
  forall {A} (p q: S -> Prog A),
    run (Get (fun s => Or (trans (p s)) (q s)))
    =
    run (Or (Get (fun s => trans (p s))) (Get q)).
Proof.
  intros.
  simpl.
  change (           fun s => run (trans (p s))    )
    with (fun s' => (fun s => run (trans (p s))) s').
  rewrite <- get_get_G_D.
  change (          (fun s => orD (run (trans (p s))) (run (q s)))    )
    with (fun s' => (fun s => orD (run (trans (p s))) (run (q s))) s').
  rewrite <- get_get_G_D.
  
  assert (H_get_vars :
    getD (fun _ => getD (fun s' => orD (run (trans (p s'))) (run (q s'))))
    =
    getD (fun s => getD (fun s' => orD (run (trans (p s ))) (run (q s'))))).
  repeat rewrite get_get_G_D;  reflexivity.
  
  rewrite H_get_vars.
  rewrite get_swap_vars.
  rewrite <- get_or_G_D.
  f_equal; apply functional_extensionality; intro s.
  induction (p s); simpl.
  - rewrite get_ret_or_G_D.
    reflexivity.
  - rewrite get_const.
    rewrite or1_fail_G_D.
    f_equal; apply functional_extensionality; intro t.
    rewrite or1_fail_G_D.
    reflexivity.
  - assert (H :
      (fun s' : S => orD (orD (run (trans p0_1)) (run (trans p0_2))) (run (q s')))
      =
      (fun s'     => orD (run (trans p0_1)) (run (Or (trans p0_2) (q s'))))).
    apply functional_extensionality; intro s'; apply or_or_G_D.
    rewrite H.
    
    assert (H_get_vars_p1 :
      getD (fun _ : S => getD (fun s' : S => orD (run (trans (p s'))) (run (Or (trans p0_2) (q s'))))) =
      getD (fun s : S => getD (fun s' : S => orD (run (trans (p s))) (run (Or (trans p0_2) (q s')))))).
    repeat rewrite get_get_G_D; reflexivity.
    rewrite (IHp0_1 _ _ H_get_vars_p1).
    simpl run.
    
    assert (H_get_vars_p2 :
      getD (fun _ : S => getD (fun s' : S => orD (run (trans (p s'))) (run (q s')))) =
      getD (fun s : S => getD (fun s' : S => orD (run (trans (p s))) (run (q s'))))).
    repeat rewrite get_get_G_D; reflexivity.
    rewrite (IHp0_2 _ _ H_get_vars_p2).
    
    rewrite <- or_or_G_D.
    assert (H_get_vars_p1' :
      getD (fun _ : S => getD (fun s' : S => orD (run (trans (p s'))) (run (trans p0_2)))) =
      getD (fun s : S => getD (fun s' : S => orD (run (trans (p s))) (run (trans p0_2))))).
    repeat rewrite get_get_G_D; reflexivity.
      
    rewrite (IHp0_1 _ _ H_get_vars_p1').
    reflexivity.
  - rewrite get_swap_vars.
    assert (get_or_H :
      (fun s' : S => orD (getD (fun s0 : S => run (trans (p0 s0)))) (run (q s')))
      =
      (fun s' : S => (getD (fun s0 : S => orD (run (trans (p0 s0))) (run (q s')))))).
    apply functional_extensionality; intro s'; rewrite get_or_G_D; reflexivity.
    rewrite get_or_H.
    assert (swap_vars :
      getD (fun s' : S => getD (fun s0 : S => orD (run (trans (p0 s0))) (run (q s'))))
      =
      getD (fun s' : S => getD (fun s0 : S => orD (run (trans (p0 s'))) (run (q s0))))).
    repeat rewrite get_get_G_D; reflexivity.
    rewrite swap_vars.
    assert (apply_IH:
      (fun s' : S => getD (fun s0 : S => orD (run (trans (p0 s'))) (run (q s0))))
      =
      (fun s' : S => orD (getD (fun _ => run (trans (p0 s')))) (getD (fun s0 => run (q s0))))).
    apply functional_extensionality; intro. 
    assert (H' : getD (fun _ : S => getD (fun s' : S => orD (run (trans (p s'))) (run (q s')))) 
                   =
                   getD (fun s0 : S => getD (fun s' : S => orD (run (trans (p s0))) (run (q s'))))).
    repeat rewrite get_get_G_D; reflexivity.
    rewrite (H _ _ _ H'); reflexivity.
    rewrite apply_IH.
    rewrite get_or_G_D.
    reflexivity.
  - rewrite get_get_G_D.
    rewrite <- get_or_G_D.
    assert (or_get_H :
      (fun s' : S => orD (getD (fun s1 : S => orD (putD s0 (run (trans p0))) (putD s1 failD))) (run (q s')))
      =
      (fun s' : S => (getD (fun s1 : S => orD (orD (putD s0 (run (trans p0))) (putD s1 failD)) (run (q s')))))).
    apply functional_extensionality; intro s'.
    rewrite get_or_G_D.
    reflexivity.
    rewrite or_get_H.
    assert (H :
      (fun s1 : S => orD (orD (putD s0 (run (trans p0))) (putD s1 failD)) (getD (fun s2 : S => run (q s2))))
      =
      (fun s1 => orD (putD s0 (run (trans p0))) (putD s1 (run (q s1))))).
    + apply functional_extensionality; intro s1.
      rewrite or_or_G_D.
      rewrite (put_or_G_D failD _ _).
      rewrite or1_fail_G_D.
      rewrite put_get_G_D.
      reflexivity.
    + rewrite H.
      rewrite get_get_G_D.
      f_equal; apply functional_extensionality; intro s1.
      rewrite or_or_G_D.
      rewrite (put_or_G_D failD _ _).
      rewrite or1_fail_G_D.
      reflexivity.
Qed.

Lemma put_or_trans':
  forall {A} (p: Prog A) (v: S) (q: Prog A),
    run (Put v (Or (trans p) q))
    =
    run (Or (Put v (trans p)) (Put v q)).
Proof.
  intros.
  assert (H1: orun (appl (CHole: Context nil A nil A)
                         (fun env =>
                            Put ((fun _ => v) env)
                                (Or (otrans (fun _ => p) env) ((fun _ => q) env))))
              =
              (fun env => run (Put v (Or (trans p) q)))).
  unfold orun, otrans.
  auto.
  assert (H2: orun (appl (CHole: Context nil A nil A)
                         (fun env =>
                            Or (Put ((fun _ => v) env) (otrans (fun _ => p) env))
                               (Put ((fun _ => v) env) ((fun _ => q) env))))
              =
              (fun env => run (Or (Put v (trans p)) (Put v q)))).
  unfold orun, otrans.
  auto.
  change (run ?r) with ((fun env => run r) Nil).
  rewrite <- H1.
  change (run ?r) with ((fun env => run r) Nil).
  rewrite <- H2.
  rewrite put_or_trans.
  reflexivity.
Qed.

Lemma run_trans_trans:
  forall {A} (p : Prog A),
    run (trans (trans p))
    =
    run (trans p).
Proof.
  intros; induction p; auto; simpl trans.
  - rewrite run_or.
    rewrite IHp1; rewrite IHp2.
    auto.
  - rewrite run_get.
    assert (H': (fun s => run (trans (trans (p s))))
                =
                (fun s => run (trans (p s)))).
    apply functional_extensionality; intro s.
    apply H.
    rewrite H'.
    auto.
  - rewrite run_get.
    cut (getD (fun s0 =>
            run (Or (Get (fun s1 =>
                            Or (Put s (trans (trans p))) (Put s1 Fail)))
                    (Get (fun s1 =>
                            Or (Put s0 Fail) (Put s1 Fail)))))
         =
         getD (fun s0 =>
            (putD s0
                  (run (Or (Put s0 Fail)
                           (Get (fun s1 =>
                                   Or (Put s (trans (trans p)))
                                      (Put s1 Fail)))))))).
    + intro H. rewrite H.
      rewrite get_put_G_D'.
      cut (forall (q : Prog A),
              (fun s0 => run (Or (Put s0 Fail) q))
              =
              (fun s0 => run (Put s0 q))).
      * intro H'; rewrite H'.
        rewrite <- run_get.
        rewrite get_put_G'.
        simpl run.
        rewrite IHp.
        reflexivity.
      * intro q; apply functional_extensionality; intro s0.
        simpl.
        rewrite put_or_G_D.
        rewrite or1_fail_G_D.
        reflexivity.
    + 
      cut ((fun s0 => run (Or (Get (fun s1 =>
                                      Or (Put s (trans (trans p)))
                                         (Put s1 Fail)))
                              (Get (fun s1 =>
                                      Or (Put s0 Fail) (Put s1 Fail)))))
           =
           (fun s0 => run (Get (fun s1 =>
                                      Or (Put s (trans (trans p)))
                                         (Put s1 Fail))))).
      * intro H. rewrite H.
        simpl.
        rewrite get_get_G_D.
        f_equal; apply functional_extensionality; intro s0.
        rewrite put_or_G_D.
        rewrite put_or_G_D.
        rewrite or1_fail_G_D.
        rewrite put_put_G_D.
        rewrite put_get_G_D.
        rewrite put_or_G_D.
        rewrite put_put_G_D.
        reflexivity.

      * apply functional_extensionality; intro s0.
        simpl.
        cut ((fun s1 => orD (putD s0 failD) (putD s1 (failD : D A)))
            =
            (fun s1 => putD s1 failD)).
        intro H. rewrite H.
        rewrite get_put_G_D.
        rewrite or2_fail_G_D.
        reflexivity.
        
        apply functional_extensionality; intro s1.
        rewrite put_or_G_D.
        rewrite or1_fail_G_D.
        rewrite put_put_G_D.
        reflexivity.
Qed.
    
Lemma get_or_trans_trans:
  forall {A} (p : Prog A) (q : S -> Prog A),
    run (Get (fun s => Or (trans p) (trans (q s))))
    =
    run (Or (trans p) (Get (fun s => trans (q s)))).
Proof.
  intros.
  rewrite get_or_trans.
  repeat rewrite run_or.
  rewrite run_get.
  rewrite <- get_put_G_D'.
  rewrite get_put_G_D.
  reflexivity.
Qed.

Lemma or_trans_put_put:
  forall {A} (p : Prog A) (s : S),
    run (Put s (trans p)) = run (Or (trans (Put s p)) (Put s Fail)).
Proof.
  intros.
  simpl.
  rewrite <- get_or_G_D.
  cut ((fun s0 : S =>
          orD (orD (putD s (run (trans p))) (putD s0 failD)) (putD s failD))
       =
       (fun s0 => putD s (run (trans p)))).
  intro H. rewrite H.
  rewrite get_const.
  reflexivity.
  apply functional_extensionality; intro s0.
  rewrite or_or_G_D.
  rewrite (put_or_G_D failD (putD s failD) s0).
  rewrite or1_fail_G_D.
  rewrite put_put_G_D.
  rewrite <- run_fail; repeat rewrite <- run_put; rewrite <- run_or.
  rewrite <- put_or_trans'.
  simpl.
  rewrite or2_fail_G_D.
  reflexivity.
Qed.

Lemma split_get_or_G_D:
  forall {A} (p q : S -> D A),
    getD (fun s => orD (p s) (putD s (q s)))
    =
    getD (fun t => orD (getD (fun s => orD (p s) (putD s failD)))
                       (putD t (getD q))).
Proof.
  intros.
  assert (H: (fun t => orD (getD (fun s => orD (p s) (putD s failD)))
                           (putD t (getD q)))
             =
             (fun t => getD (fun s =>
                               orD (p s)
                                   (orD (putD s failD)
                                        (putD t (getD q)))))).
  - apply functional_extensionality; intro t.
    rewrite <- get_or_G_D.
    f_equal; apply functional_extensionality; intro s.
    apply or_or_G_D.
  - rewrite H.
    rewrite get_get_G_D.
    f_equal; apply functional_extensionality; intro s.
    rewrite put_or_G_D.
    rewrite or1_fail_G_D.
    rewrite put_put_G_D.
    rewrite put_get_G_D.
    reflexivity.
Qed.

Lemma put_ret_trans_comm:
  forall {A} (x : A) (q : Prog A) (t u : S -> S),
    run (Get (fun s => Or (Or (Put (t s) (Return x))
                              (Put (u s) (trans q)))
                          (Put s Fail)))
    =
    run (Get (fun s => Or (Or (Put (u s) (trans q))
                              (Put (t s) (Return x)))
                          (Put s Fail))).
Proof.
  intros A x q.
  induction q; intros t u.
  - simpl.
    apply put_or_comm_G_D.
  - simpl.
    apply put_or_comm_G_D.
  - simpl trans.
    assert (H: (fun s : S => run (Or (Or (Put (t s) (Return x)) (Put (u s) (Or (trans q1) (trans q2)))) (Put s Fail)))
               =
               (fun s => run (Or (Or (Put (t s) (Return x))
                                     (Put (u s) (trans q1)))
                                 (Put s
                                      (Put (u s) (Or (trans q2)
                                                     (Put s Fail))))))).

    + apply functional_extensionality; intro s.
      simpl.
      rewrite <- run_or.
      rewrite <- run_put.
      rewrite put_or_trans'.
      simpl.
      rewrite put_put_G_D.
      rewrite <- (put_or_G_D _ _ (u s)).
      rewrite <- (or_or_G_D _ _ (putD s failD)).
      rewrite (or_or_G_D _ _ (putD (u s) (run (trans q2)))).
      reflexivity.
    + rewrite run_get.
      rewrite H.
      simpl.
      rewrite split_get_or_G_D.

      assert (Hq1: (fun t0 =>
                      orD (getD (fun s =>
                                   orD (orD (putD (t s) (retD x))
                                            (putD (u s) (run (trans q1))))
                                       (putD s failD)))
                          (putD t0 (getD (fun s =>
                                            putD (u s) (orD (run (trans q2))
                                                            (putD s failD))))))
                   =
                   (fun t0 =>
                      (orD (run (Get (fun s =>
                                        Or (Or (Put (u s) (trans q1))
                                               (Put (t s) (Return x)))
                                           (Put s Fail))))
                           (putD t0 (getD (fun s =>
                                             putD (u s) (orD (run (trans q2))
                                                             (putD s failD)))))))).
      apply functional_extensionality; intro h; rewrite <- IHq1; auto.
      rewrite Hq1.
      simpl.
      rewrite <- split_get_or_G_D.
      assert (assoc: 
                (fun s => orD (orD (putD (u s) (run (trans q1)))
                                   (putD (t s) (retD x)))
                              (putD s (putD (u s) (orD (run (trans q2))
                                                       (putD s failD)))))
                =
                (fun s => orD (putD (u s) (run (trans q1)))
                              (putD s (orD (putD (t s) (retD x))
                                           (putD (u s) (orD (run (trans q2))
                                                            (putD s failD))))))).
      * apply functional_extensionality; intro s.
        rewrite put_put_G_D.
        rewrite or_or_G_D.
        f_equal.
        rewrite put_or_G_D.
        rewrite put_put_G_D.
        reflexivity.
      * rewrite assoc.
        rewrite split_get_or_G_D.
        assert (Hq2:
(fun t0 : S =>
     orD (getD (fun s : S => orD (putD (u s) (run (trans q1))) (putD s failD)))
       (putD t0
          (getD
             (fun s : S =>
              orD (putD (t s) (retD x))
                (putD (u s) (orD (run (trans q2)) (putD s failD)))))))
=
(fun t0 =>
     (orD (getD (fun s : S => orD (putD (u s) (run (trans q1))) (putD s failD)))
       (putD t0
            (run
          (Get
             (fun s : S =>
              Or (Or (Put (u s) (trans q2)) (Put (t s) (Return x)))
                  (Put s Fail)))))))).
        ** apply functional_extensionality; intro t0.
           rewrite <- IHq2.
           simpl.
           f_equal.
           assert (assoc':
                     (fun s : S =>
                        orD (putD (t s) (retD x))
                            (putD (u s) (orD (run (trans q2)) (putD s failD))))
                     =
                     (fun s : S =>
                        orD (orD (putD (t s) (retD x)) (putD (u s) (run (trans q2))))
                            (putD s failD))).
           apply functional_extensionality; intro s.
           rewrite or_or_G_D.
           rewrite (put_or_G_D _ _ (u s)).
           reflexivity.
           rewrite assoc'.
           reflexivity.

        ** rewrite Hq2.
           simpl.
           rewrite <- split_get_or_G_D.
           assert (assoc':
(fun s : S =>
     orD (putD (u s) (run (trans q1)))
       (putD s
          (orD (orD (putD (u s) (run (trans q2))) (putD (t s) (retD x)))
             (putD s failD))))
=
(fun s : S =>
     orD
       (orD (putD (u s) (orD (run (trans q1)) (run (trans q2))))
          (putD (t s) (retD x))) (putD s failD))).
           *** apply functional_extensionality; intro s.
               repeat rewrite put_or_G_D.
               rewrite put_put_G_D.
               rewrite <- put_or_G_D.
               repeat rewrite <- run_fail.
               repeat rewrite <- run_ret.
               repeat rewrite <- run_put.
               repeat rewrite <- run_or.
               repeat rewrite <- run_put.
               repeat rewrite <- run_or.
               rewrite <- put_or_trans'.
               simpl.
               repeat rewrite or_or_G_D.
               reflexivity.

           *** rewrite assoc'.
               reflexivity.

  - simpl trans.
    assert (H':
      run (Get (fun s : S => Or (Or (Put (t s) (Return x)) (Put (u s) (Get (fun s0 : S => trans (p s0))))) (Put s Fail)))
      =
      run (Get (fun a => Get (fun s =>
        Or (Or (Put (t s) (Return x)) (Put (u s) (trans (p (u a)))))
           (Put s Fail))))).
    + rewrite get_get_G'.
      repeat rewrite run_get.
      f_equal; apply functional_extensionality; intro s.
      simpl.
      rewrite put_get_G_D.
      reflexivity.
    
    + rewrite H'.
      repeat rewrite run_get.
      assert (H'':
        (fun s : S =>
   run (Get (fun s0 : S => Or (Or (Put (t s0) (Return x)) (Put (u s0) (trans (p (u s))))) (Put s0 Fail))))
        =
        (fun s =>
          run (Get (fun s0 => Or (Or (Put (u s0) (trans (p (u s)))) (Put (t s0) (Return x))) (Put s0 Fail))))).
      * apply functional_extensionality; intro a.
        apply H.
      * rewrite H''.
        simpl.
        rewrite get_get_G_D.
        f_equal; apply functional_extensionality; intro s.
        rewrite put_get_G_D.
        reflexivity.

  - simpl trans.
    assert (H: (fun h =>
                  run (Or
                         (Or (Put (t h) (Return x))
                             (Put (u h)
                                  (Get (fun i =>
                                           Or (Put s (trans q))
                                              (Put i Fail)))))
                         (Put h Fail)))
               =
               (fun h =>
                  run
                    (Or (Or (Put (t h) (Return x)       )
                            (Put s     (trans q)))
                        (Put h Fail)))).
    + apply functional_extensionality; intro h.
      simpl.
      rewrite put_get_G_D.
      rewrite <- (put_or_G_D (putD s (run (trans q))) _).
      rewrite put_put_G_D.
      rewrite or_or_G_D.
      rewrite or_or_G_D.
      rewrite (put_or_G_D _ _ (u h)).
      rewrite or1_fail_G_D.
      rewrite put_put_G_D.
      rewrite or_or_G_D.
      reflexivity.
    + rewrite run_get.
      rewrite H.
      rewrite <- run_get.
      rewrite IHq.
      assert (H': (fun h =>
                     run (Or
                            (Or (Put (u h)
                                     (Get (fun i =>
                                             Or (Put s (trans q))
                                                (Put i Fail))))
                                (Put (t h) (Return x)))
                            (Put h Fail)))
                  =
                  (fun h =>
                     run
                       (Or (Or (Put s     (trans q))
                               (Put (t h) (Return x)))
                           (Put h Fail)))).
      * apply functional_extensionality; intro h.
        simpl.
        rewrite put_get_G_D.
        rewrite <- (put_or_G_D (putD s (run (trans q))) _).
        rewrite put_put_G_D.
        rewrite or_or_G_D.
        rewrite or_or_G_D.
        rewrite (put_or_G_D _ _ (u h)).
        rewrite or1_fail_G_D.
        rewrite (put_or_G_D _ _ (t h)).
        rewrite put_put_G_D.
        repeat rewrite or_or_G_D.
        repeat rewrite put_or_G_D.
        reflexivity.
      * rewrite (run_get (fun s0 => Or
                                      (Or
                                         (Put (u s0) (Get (fun s1 =>
                                                             Or (Put s (trans q))
                                                                (Put s1 Fail))))
                                         (Put (t s0) (Return x))) (Put s0 Fail))).
        rewrite H'.
        rewrite <- run_get.
        reflexivity.
        
Qed.

Lemma or_trans_G':
  forall {A} (p q : Prog A),
    run (Or (trans p) (trans q)) = run (Or (trans q) (trans p)).
Proof.
  intros.
  induction p.
  - simpl trans.
    rewrite <- get_put_G'.
    rewrite <- (get_put_G' (Or (trans q) (Return a))).
    repeat rewrite run_get.
    cut ((fun s : S => run (Put s (Or (Return a) (trans q))))
         =
         (fun s =>
            run (Or (Or (Put s (Return a))
                        (Put s (trans q)))
                    (Put s Fail)))).
    intro H; rewrite H.
    cut ((fun s : S => run (Put s (Or (trans q) (Return a))))
         =
         (fun s =>
            run (Or (Or (Put s (trans q))
                        (Put s (Return a)))
                    (Put s Fail)))).
    intro H'. rewrite H'.
    repeat rewrite <- run_get.
    apply put_ret_trans_comm.


    apply functional_extensionality; intro s.
    rewrite run_put.
    rewrite <- fail_or'.
    rewrite <- run_put.
    cut (Or (Or (trans q) (Return a)) Fail
         =
        (Or (trans (Or q (Return a))) Fail)).
    intro H'.
    rewrite H'.
    rewrite put_or_trans'.
    rewrite run_or.
    simpl trans.
    rewrite put_or_trans'.
    simpl.
    reflexivity.
    auto.

    apply functional_extensionality; intro s.
    rewrite run_put.
    rewrite <- fail_or'.
    rewrite <- run_put.
    cut (Or (Or (Return a) (trans q)) Fail
         =
        (Or (trans (Or (Return a) q)) Fail)).
    intro H'.
    rewrite H'.
    rewrite put_or_trans'.
    rewrite run_or.
    simpl.
    rewrite put_ret_or_G_D.
    reflexivity.
    auto.

  - simpl.
    rewrite or1_fail_G_D; rewrite or2_fail_G_D.
    reflexivity.
  - simpl trans.
    rewrite or_or'.
    rewrite run_or.
    rewrite IHp2.
    rewrite <- run_or.
    rewrite <- or_or'.
    rewrite run_or.
    rewrite IHp1.
    rewrite <- run_or.
    rewrite or_or'.
    reflexivity.
  - simpl trans.
    rewrite <- get_or_G'.
    rewrite run_get.
    cut ((fun s => run (Or (trans (p s)) (trans q)))
         = 
         (fun s => run (Or (trans q) (trans (p s))))).
    + intro H'; rewrite H'.
      rewrite <- run_get.
      apply get_or_trans_trans.
    + apply functional_extensionality; intro s.
      apply H.
  - simpl trans.
    rewrite <- get_or_G'.
    simpl run.
    
    assert (H: (fun s0 : S =>
                  orD (orD (putD s (run (trans p))) (putD s0 failD))
                      (run (trans q)))
               =
               (fun s0 =>
                  run (Or (Put s (Or (trans (Put s0 q)) (trans p))) (Put s0 Fail)))).
    + apply functional_extensionality; intro s0.
      rewrite or_or_G_D.
      rewrite (put_or_G_D failD (run (trans q)) s0).
      rewrite or1_fail_G_D.
      rewrite <- (run_put s0 (trans q)).
      rewrite or_trans_put_put.
      rewrite run_or.
      rewrite <- or_or_G_D.
      rewrite put_or_G_D.
      rewrite <- run_or.
      rewrite IHp.
      auto.
    + rewrite H.
      assert (H' : (fun s0 =>
                      run (Or (Put s (Or (trans (Put s0 q)) (trans p)))
                              (Put s0 Fail)))
                   =
                   (fun s0 =>
                      run (Or (Put s0 (trans q))
                              (Or (Put s (trans p))
                                  (Put s0 Fail))))).
      * apply functional_extensionality; intro t.
        rewrite run_or.
        rewrite <- put_or_G'.
        simpl (trans (Put t q)).
        simpl run.
        rewrite put_get_G_D.
        rewrite put_or_G_D.
        rewrite put_or_G_D.
        rewrite put_or_G_D.
        rewrite put_or_G_D.
        rewrite or_or_G_D.
        rewrite (put_or_G_D failD (run (trans p)) s).
        rewrite or1_fail_G_D.
        rewrite <- put_or_G_D.
        rewrite put_put_G_D.
        rewrite <- put_or_G_D.
        rewrite or_or_G_D.
        reflexivity.
      * rewrite H'.
        
        rewrite <- (get_const (run (trans q))).
        change (orD (getD (fun _ : S => run (trans q))) (getD (fun s0 : S => orD (putD s (run (trans p))) (putD s0 failD))))
        with (run (Or (Get (fun _ => trans q)) (Get (fun s0 => Or (Put s (trans p)) (Put s0 Fail))))).
        rewrite <- get_or_trans.
        simpl.
        rewrite <- (get_put_G_D' (fun s0 : S => orD (run (trans q)) (orD (putD s (run (trans p))) (putD s0 failD)))).
        f_equal; apply functional_extensionality; intro s0.
        rewrite put_or_G_D.
        reflexivity.
Qed.
        
    
Lemma or_abcd_focus_bc:
  forall {A} (a b c d : D A),
    orD (orD a b) (orD c d) = orD a (orD (orD b c) d).
Proof.
  intros.
  repeat rewrite or_or_G_D.
  reflexivity.
Qed.

Lemma right_distr_L_0:
  forall {A B} (m: Prog A) (f1 f2: A -> Prog B),
    evl (bind m (fun x => Or (f1 x) (f2 x)))
    =
    evl (Or (bind m f1) (bind m f2)).
Proof.
  intros.
  induction m; auto.
  - unfold evl.
    simpl.
    rewrite or1_fail_G_D.
    reflexivity.
  - unfold evl.
    simpl.
    change (run (trans ?x)) with (evl x).
    rewrite IHm1.
    rewrite IHm2.
    unfold evl.
    simpl.
    rewrite or_or_G_D.
    assert (H:
              (orD (run (trans (bind m1 f2)))
                   (orD (run (trans (bind m2 f1)))
                        (run (trans (bind m2 f2)))))
              =
              (orD (run (trans (bind m2 f1)))
                   (orD (run (trans (bind m1 f2)))
                        (run (trans (bind m2 f2)))))).
    + repeat rewrite <- run_or.
      repeat rewrite <- or_or'.
      rewrite run_or.
      rewrite or_trans_G'.
      rewrite <- run_or.
      reflexivity.
    + rewrite H.
      rewrite <- or_or_G_D.
      reflexivity.
  - simpl bind.

    unfold evl.
    simpl.
    change (run (trans ?x)) with (evl x).

    assert (H': (fun s => evl (bind (p s) (fun x => Or (f1 x) (f2 x))))
                =
                (fun s => evl (Or (bind (p s) f1) (bind (p s) f2)))).
    apply functional_extensionality; intro s.
    apply H.
    rewrite H'.
    assert (unevl: getD (fun s => evl (Or (bind (p s) f1) (bind (p s) f2)))
                   =
                   run (Get (fun s => (Or (trans (bind (p s) f1)) (trans (bind (p s) f2)))))).
    auto.
    rewrite unevl.
    rewrite get_or_trans.
    simpl run.
    reflexivity.
  - 
    simpl bind.
    unfold evl. simpl run.
    assert (H1: (fun s0 =>
                   orD (putD s (run (trans (bind m (fun x => Or (f1 x) (f2 x))))))
                       (putD s0 failD))
                =
                (fun s0 => orD (run (Put s (Or (trans (bind m f1))
                                               (trans (bind m f2)))))
                               (putD s0 failD))).
    apply functional_extensionality.
    intro x.
    change (run (trans ?p)) with (evl p).
    rewrite IHm.
    unfold evl.
    simpl run. simpl trans.
    reflexivity.
    rewrite H1.


    assert (H2: forall (p q: Prog B),
               (fun s0 =>
                  orD (run (Put s (Or (trans p) q))) (putD s0 failD))
               =
               (fun s0 =>
                  run (Or (Or (Put s (trans p)) (Put s0 Fail))
                          (Or (Put s q) (Put s0 Fail))))).
    intros.
    apply functional_extensionality; intro s0.
    rewrite put_or_trans'.
    simpl.
    rewrite or_abcd_focus_bc.
    cut (orD (putD s0 failD) (putD s (run q)) = putD s (run q)).
    intro H. rewrite H. rewrite <- or_or_G_D. reflexivity.
    rewrite put_or_G_D.
    rewrite or1_fail_G_D.
    rewrite put_put_G_D.
    reflexivity.
    
    rewrite H2.
    rewrite <- run_get.
    change (fun s0 : S =>
                (Or (Or (Put s (trans (bind m f1))) (Put s0 Fail))
                    (Or (Put s (trans (bind m f2))) (Put s0 Fail))))
      with (fun s0 => (fun s1 s2 =>
                         (Or (Or (Put s (trans (bind m f1))) (Put s1 Fail))
                             (Or (Put s (trans (bind m f2))) (Put s1 Fail))))
                        s0
                        s0).
    rewrite <- get_get_G'.
    rewrite get_get_or_lambdas_G'.
    rewrite run_get.

    assert (H3:
              (fun s0 =>
                 run (Get (fun s1 =>
                             Or (Or (Put s (trans (bind m f1))) (Put s1 Fail))
                                (Or (Put s (trans (bind m f2))) (Put s0 Fail)))))
              =
              (fun s0 =>
                 run (Or (trans (Put s (trans (bind m f1))))
                         (Or (Put s (trans (bind m f2))) (Put s0 Fail))))).

    (*
                 run (Or (Get (fun _ =>
                                 Or (Put s (trans (bind m f1))) (Put s0 Fail)))
                         (Or (Put s (trans (bind m f2))) (Put s0 Fail))))).
*)
    apply functional_extensionality; intro s0.
    rewrite get_or_G'.
    simpl trans.
    repeat rewrite run_or; f_equal.
    simpl run.
    rewrite run_trans_trans.
    reflexivity.

                              
    rewrite H3.
    rewrite <- run_get.
    rewrite get_or_trans.
    rewrite run_or, run_get, run_get.
    f_equal.
    simpl.
    rewrite get_get_G_D.
    f_equal; apply functional_extensionality; intro s0.
    rewrite run_trans_trans.
    reflexivity.
Qed.

Lemma right_distr_L_1':
  forall {A B C E1 E2 X}
         (c: Context E1 C E2 B)
         (m: X -> Prog A)
         (f1 f2: A -> X -> Prog C)
         (f: Env E1 -> X),
    oevl (appl c (fun env =>
                    bind (m (f env)) (fun x => Or (f1 x (f env)) (f2 x (f env)))))
    =
    oevl (appl c (fun env =>
                    (Or (bind (m (f env)) (fun x => f1 x (f env)))
                        (bind (m (f env)) (fun x => f2 x (f env)))))).
Proof.
  intros.
  
  change (fun env => bind (m (f env)) (fun x => Or (f1 x (f env)) (f2 x (f env))))
    with (fun env => (fun y =>
                        bind (m y) (fun x => Or (f1 x y) (f2 x y)))
                       (f env)).
  change (fun env =>
            Or (bind (m (f env)) (fun x : A => f1 x (f env)))
               (bind (m (f env)) (fun x : A => f2 x (f env))))
    with (fun env => (fun y =>
                        Or (bind (m y) (fun x => f1 x y))
                           (bind (m y) (fun x => f2 x y)))
                       (f env)).
  apply evl_meta.
  intro x.
  apply right_distr_L_0.
Qed.

Lemma right_distr_L_1:
  forall {A B C E1 E2}
         (c: Context E1 C E2 B)
         (m: OProg E1 A)
         (f1 f2: A -> OProg E1 C),
    oevl (appl c (obind m (fun x env => Or (f1 x env) (f2 x env))))
    =
    oevl (appl c (fun env =>
                    (Or (bind (m env) (fun x => f1 x env))
                        (bind (m env) (fun x => f2 x env))))).
Proof.
  intros.
  apply right_distr_L_1'.
Qed.

Lemma right_distr_L_2:
  forall {A B C D E1 E2}
         (c: Context E1 D E2 B)
         (m: OProg E1 A)
         (f1 f2: A -> OProg E1 C)
         (q: C -> OProg E1 D),
    oevl (appl c (obind
                    (obind m (fun x env => Or (f1 x env) (f2 x env)))
                    q))
    =
    oevl (appl c (obind
                    (fun env =>
                       (Or (bind (m env) (fun x => f1 x env))
                           (bind (m env) (fun x => f2 x env))))
                    q)).
Proof.
  intros.
  unfold obind.
  simpl.
  assert (H: (fun env =>
                bind (bind (m env) (fun x => Or (f1 x env) (f2 x env)))
                     (fun x => q x env))
             =
             (obind m (fun x env => Or (bind (f1 x env) (fun y => q y env))
                                       (bind (f2 x env) (fun y => q y env))))).
  unfold obind; apply functional_extensionality; intro env.
  rewrite bind_bind.
  auto.
  rewrite H.
  rewrite right_distr_L_1.
  assert (H':
            (fun env =>
               Or (bind (m env) (fun x => bind (f1 x env) (fun y => q y env)))
                  (bind (m env) (fun x => bind (f2 x env) (fun y => q y env))))
            =
            (fun env =>
               Or (bind (bind (m env) (fun x => f1 x env)) (fun x => q x env))
                  (bind (bind (m env) (fun x => f2 x env)) (fun x => q x env)))).
  apply functional_extensionality; intro env.
  repeat rewrite bind_bind.
  reflexivity.
  rewrite H'.
  reflexivity.
Qed.
    
Lemma right_distr_L:
  forall {A B C E1 E2}
         (b: BContext E1 C E2 B)
         (m: OProg E1 A)
         (f1 f2: A -> OProg E1 C),
    oevl (bappl b (obind m (fun x env => Or (f1 x env) (f2 x env))))
    =
    oevl (bappl b (fun env =>
                     (Or (bind (m env) (fun x => f1 x env))
                         (bind (m env) (fun x => f2 x env))))).
Proof.
  intros.
  apply bapp_from_appl.
  intros.
  apply right_distr_L_2.
Qed.

End Syntax.


(* Finally, we define an implementation for our semantic domain, and prove that it
   conforms to all the semantic domain axioms.
 *)
Module Implementation <: SemanticInterface.

Definition Bag (A: Type) := A -> nat.

Parameter eqDec: forall A (x y: A), (x = y) + (x <> y).

Definition singleton {A: Type}: A -> Bag A :=
 fun x =>
   (fun y => match (eqDec _ x y) with
             | inl _ => 1
             | inr _ => 0
             end).

Definition emptyBag {A: Type}: Bag A :=
 fun y => 0.

Definition union {A: Type}: Bag A -> Bag A -> Bag A :=
 fun xs ys =>
   (fun z => xs z + ys z).

Parameter S : Type.

Definition D : Type -> Type :=
  fun A => S -> (Bag (A * S) * S).

Definition retD : forall {A}, A -> D A :=
 fun A => (fun x => (fun s => (singleton (x,s), s))).

Definition failD : forall {A}, D A :=
 fun A => (fun s => (emptyBag, s)).

Definition orD : forall {A}, D A -> D A -> D A :=
 fun A xs ys =>
   (fun s => match xs s with
             | (ansx, s') => match ys s' with
                             | (ansy, s'') => (union ansx ansy, s'')
                             end
             end).

Definition getD : forall {A}, (S -> D A) -> D A :=
 fun A k =>
    (fun s => k s s).

Definition putD : forall {A}, S -> D A -> D A :=
 fun A s k =>
   (fun _ => k s).

Require Coq.Logic.FunctionalExtensionality.
Import Coq.Logic.FunctionalExtensionality.

Lemma or1_fail_G_D:
 forall {A} (q: D A),
 orD failD q
 =
 q.
Proof.
 intros; simpl; unfold orD, failD, emptyBag, union.
 change q with (fun s => q s).
 apply functional_extensionality; intros s.
 simpl.
 destruct (q s).
 auto.
Qed.

Lemma or2_fail_G_D:
 forall {A} (p: D A),
 orD p failD
 =
 p.
Proof.
 intros; unfold failD, orD, union, emptyBag.
 change p with (fun s => p s) at 2.
 apply functional_extensionality; intro s.
 destruct (p s).
 assert ((fun z : A * S => b z + 0) = b).
   - change b with (fun z => b z).
     apply functional_extensionality; intro z.
      auto.
   - rewrite H; auto.
Qed.

Require Import Coq.Arith.Plus.

Lemma or_or_G_D:
 forall {A} (p q r: D A),
 orD (orD p q) r
 =
 orD p (orD q r).
Proof.
 intros; unfold orD, union.
 apply functional_extensionality; intro s0.
 destruct (p s0).
 destruct (q s).
 destruct (r s1).
 assert ((fun z : A * S => b z + b0 z + b1 z) = (fun z : A * S => b z + (b0 z + b1 z))).
 - apply functional_extensionality; intro z. rewrite plus_assoc. reflexivity.
 - rewrite H; reflexivity.
Qed.

Lemma get_get_G_D:
 forall {A} (k: S -> S -> D A),
   getD (fun s => getD (fun s' => k s s'))
   =
   getD (fun s => k s s).
Proof.
auto.
Qed.

Lemma put_get_G_D:
 forall {A} (s: S) (k: S -> D A),
 putD s (getD k)
 =
 putD s (k s).
Proof.
 auto.
Qed.

Lemma get_put_G_D:
 forall {A} (p: D A),
   getD (fun s => putD s p)
  =
  p.
Proof.
 auto.
Qed.

Lemma put_put_G_D:
 forall {A} (s s': S) (p: D A),
 putD s (putD s' p)
 =
 putD s' p.
Proof.
 auto.
Qed.

Lemma put_or_G_D:
 forall {A} (p q: D A) (s: S),
  orD (putD s p) q
  =
  putD s (orD p q).
Proof.
 auto.
Qed.

Lemma put_ret_or_G_D:
 forall {A}  (v: S) (w: A) (q: D A),
 putD v (orD (retD w) q)
 =
 orD (putD v (retD w)) (putD v q).
Proof.
 auto.
Qed.

Lemma or_ret_ret_G_D:
 forall {A} (x y: A),
   (orD (retD x) (retD y)) = (orD (retD y) (retD x)).
Proof.
 intros; unfold orD, retD, singleton, union.
 apply functional_extensionality; intro s.
 assert ((fun z : A * S =>
match eqDec (A * S) (x, s) z with
| inl _ => 1
| inr _ => 0
end + match eqDec (A * S) (y, s) z with
      | inl _ => 1
      | inr _ => 0
      end) = (fun z : A * S =>
match eqDec (A * S) (y, s) z with
| inl _ => 1
| inr _ => 0
end + match eqDec (A * S) (x, s) z with
      | inl _ => 1
      | inr _ => 0
      end)).
 - apply functional_extensionality; intro z.
   destruct (eqDec (A * S) (x, s) z); destruct (eqDec (A * S) (y, s) z); auto.
 - rewrite H; reflexivity.
Qed. 

Lemma or_comm_ret_G_D:
  forall {A} (x y: A),
    orD (retD x) (retD y) = orD (retD y) (retD x).
Proof.
  intros; unfold orD, retD, union.
  apply functional_extensionality; intro s.
  apply injective_projections; auto.
  simpl; apply functional_extensionality; intro z.
  intuition.
Qed.

Lemma put_or_comm_G_D:
  forall {A} (p q : D A) (t u : S -> S),
    getD (fun s => orD (orD (putD (t s) p) (putD (u s) q)) (putD s failD))
    =
    getD (fun s => orD (orD (putD (u s) q) (putD (t s) p)) (putD s failD)).
Proof.
  intros.
  unfold getD, orD, putD, failD.
  apply functional_extensionality; intro s.
  destruct (p (t s)); destruct (q (u s)); simpl.
  apply injective_projections; simpl; auto.
  unfold union.
  apply functional_extensionality; intro z.
  intuition.
Qed.

End Implementation.
