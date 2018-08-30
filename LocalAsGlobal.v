Module Type Syntax.

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
(* The type of state. *)
Parameter S : Type.

(* Programs -- the free monad over the signature of fail + or + get + put *)
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

(* Programs with free variables *)

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

Lemma obind_cpush:
  forall {E A B C} {a: C} {p: OProg (C :: E) A} {k: A -> OProg (C::E) B},
    obind (cpush a p) (fun x => cpush a (k x))
   =
   cpush a (obind p k).
Proof.
  intros; unfold obind, cpush, comap; auto.
Qed.

(* Contexts for open programs *)
Inductive Context : list Type -> Type -> list Type -> Type -> Type :=
  | CHole   : forall {E A}, Context E A E A
  | COr1    : forall {E1 E2 A B}, Context E1 A E2 B -> OProg E2 B -> Context E1 A E2 B
  | COr2    : forall {E1 E2 A B}, OProg E2 B -> Context E1 A E2 B -> Context E1 A E2 B
  | CPut     : forall {E1 E2 A B}, (Env E2 -> S) -> Context E1 A E2 B -> Context E1 A E2 B
  | CGet     : forall {E1 E2 A B}, (S -> bool) -> (Context E1 A (S::E2) B) -> (S -> OProg E2 B)-> Context E1 A E2 B
  | CDelay  : forall {E1 E2 A B}, (Env E2 -> bool) -> Context E1 A E2 B -> OProg E2 B -> Context E1 A E2 B
  | CPush   : forall {E1 E2 A B C}, C -> Context E1 A (C::E2) B-> Context E1 A E2 B
  | CLift      : forall {E1 E2 A B C}, Context E1 A E2 B -> Context E1 A (C::E2) B.

(* Applying a context to a program *)
Fixpoint appl {E1 E2: list Type} {A B: Type} (c: Context E1 A E2 B)  : OProg E1 A -> OProg E2 B :=
  match c in (Context E1 A E2 B) return (OProg E1 A -> OProg E2 B) with
  | CHole => (fun p env => p env)
  | COr1 c q => (fun p env => Or (appl c p env) (q env))
  | COr2 p c => (fun q env => Or (p env) (appl c q env))
  | CPut v c => (fun p env => Put (v env) (appl c p env)) 
  | CGet t c q => (fun p env => Get (fun s => if t s then cpush s (appl c p) env else q s env))
  | CDelay t c q => (fun p => (fun env => if t env then appl c p env else q env))
  | CPush x c => (fun p env => cpush x (appl c p) env)
  | CLift c => (fun p env => clift (appl c p) env) 
  end.

(* Applying a context to a context, aka composing contexts *)
Fixpoint applC {E1 E2 E3: list Type} {A B C: Type} (c: Context E2 B E3 C)  : Context E1 A E2 B -> Context E1 A E3 C:=
  match c in (Context E2 B E3 C) return (Context E1 A E2 B -> Context E1 A E3 C) with
  | CHole => (fun d => d)
  | COr1 c q => (fun d => COr1 (applC c d) q)
  | COr2 p c => (fun d => COr2 p (applC c d))
  | CPut v c => (fun d => CPut v (applC c d)) 
  | CGet t c q => (fun d => CGet t (applC c d) q)
  | CDelay t c q => (fun d => CDelay t (applC c d) q)
  | CPush x c => (fun d => CPush x (applC c d))
  | CLift c => (fun d => CLift (applC c d))
  end.

(* Alternative zipper-based context *)
Inductive ZContext : list Type -> Type -> list Type -> Type -> Type :=
  | ZHole    : forall {E A}, ZContext E A E A
  | ZOr1     : forall {E1 E2 A B}, ZContext E1 A E2 B -> OProg E1 A -> ZContext E1 A E2 B
  | ZOr2     : forall {E1 E2 A B}, ZContext E1 A E2 B -> OProg E1 A -> ZContext E1 A E2 B
  | ZPut      : forall {E1 E2 A B}, ZContext E1 A E2 B -> (Env E1 -> S) -> ZContext E1 A E2 B
  | ZGet      : forall {E1 E2 A B}, ZContext E1 A E2 B -> (S -> bool) -> (S -> OProg E1 A) -> ZContext (S::E1) A E2 B
  | ZDelay   : forall {E1 E2 A B}, ZContext E1 A E2 B -> (Env E1 -> bool) -> OProg E1 A -> ZContext E1 A E2 B
  | ZPush    : forall {E1 E2 A B C}, ZContext E1 A E2 B -> C -> ZContext (C :: E1) A E2 B
  | ZLift      : forall {E1 E2 A B C}, ZContext (C::E1) A E2 B -> ZContext E1 A E2 B.

Fixpoint zappl {E1 E2: list Type} {A B: Type} (z: ZContext E1 A E2 B)  : OProg E1 A -> OProg E2 B :=
  match z in (ZContext E1 A E2 B) return (OProg E1 A -> OProg E2 B) with
  | ZHole => (fun p env => p env)
  | ZOr1 z q => (fun p => zappl z (fun env => Or (p env) (q env)))
  | ZOr2 z p => (fun q  => zappl z (fun env => Or (p env) (q env)))
  | ZPut z v => (fun p => zappl z (fun env => Put (v env) (p env)))
  | ZGet z t q => (fun p => zappl z (fun env => Get (fun s => if t s then (cpush s p) env else q s env)))
  | ZDelay z t q => (fun p => zappl z (fun env => if t env then p env else q env))
  | ZPush z c => (fun p => zappl z (cpush c p))
  | ZLift z => (fun p => zappl z (clift p))
  end.

Fixpoint toZContext_ {E1 E2 A B} (c: Context E1 A E2 B): (forall {E3 C}, ZContext E2 B E3 C-> ZContext E1 A E3 C) :=
   match c in (Context E1 A E2 B) return ((forall {E3 C}, ZContext E2 B E3 C-> ZContext E1 A E3 C)) with
   | CHole => (fun _ _ z => z)
   | COr1 c p => (fun _ _ z => toZContext_ c (ZOr1 z p))
   | COr2 p c => (fun _ _ z => toZContext_ c (ZOr2 z p))
   | CPut s c => (fun _ _ z => toZContext_ c (ZPut z s))
   | CGet t c p => (fun _ _ z => toZContext_ c (ZGet z t p))
   | CDelay t c p => (fun _ _ z => toZContext_ c (ZDelay z t p))
   | CPush a c => (fun _ _ z => toZContext_ c (ZPush z a))
   | CLift c => (fun _ _ z => toZContext_ c (ZLift z))
  end.

Definition toZContext {E1 E2 A B} (c: Context E1 A E2 B): ZContext E1 A E2 B := toZContext_ c ZHole.

Lemma zappl_toZContext_:
   forall {E1 E2 A B} (c: Context E1 A E2 B) {E3 C} (z: ZContext E2 B E3 C) (p: OProg E1 A),
     zappl (toZContext_ c z) p = zappl z (appl c p).
Proof.
  intros E1 E2 A B c; induction c; intros E3 D z prog; simpl; auto.
  - rewrite IHc; simpl; auto.
  - rewrite IHc; simpl; auto.
  - rewrite IHc; simpl; auto.
  - rewrite IHc; simpl; auto.
  - rewrite IHc; simpl; auto.
  - rewrite IHc; simpl; auto.
  - rewrite IHc; simpl; auto.
Qed.

Lemma zappl_toZContext:
   forall {E1 E2 A B} (c: Context E1 A E2 B) (p: OProg E1 A),
     zappl (toZContext c) p = appl c p.
Proof.
  intros; unfold toZContext; rewrite zappl_toZContext_; simpl; reflexivity.
Qed.

Fixpoint fromZContext_ {E2 E3: list Type} {B C: Type} (z: ZContext E2 B E3 C)  : forall {E1 A}, Context E1 A E2 B -> Context E1 A E3 C :=
  match z in (ZContext E2 B E3 C) return (forall {E1 A}, Context E1 A E2 B -> Context E1 A E3 C) with
  | ZHole => (fun _ _ c => c)
  | ZOr1 z q => (fun _ _ c => fromZContext_ z (COr1 c q)) 
  | ZOr2 z p => (fun _ _ c => fromZContext_ z (COr2 p c))
  | ZPut z v => (fun _ _ c => fromZContext_ z (CPut v c))
  | ZGet z t q => (fun _ _ c =>fromZContext_ z (CGet t c q))
  | ZDelay z t q => (fun _ _ c => fromZContext_ z (CDelay t c q))
  | ZPush z x => (fun _ _ c => fromZContext_ z (CPush x c))
  | ZLift z => (fun _ _ c => fromZContext_ z (CLift c))
  end.

Definition fromZContext {E1 E2: list Type}  {A B: Type} (z: ZContext E1 A E2 B)  : Context E1 A E2 B :=
  fromZContext_ z CHole. 

Lemma  appl_fromZContext_:
  forall {B C E2 E3} (z: ZContext E2 B E3 C) {E1 A} (c: Context E1 A E2 B) (p: OProg E1 A),
       appl (fromZContext_ z c) p = zappl z (appl c p).
Proof.
  intros B C E2 E3 z; induction z; intros E0 A0 c0 p; simpl.
  - auto.
  - rewrite IHz; simpl; auto.
  - rewrite IHz; simpl; auto.
  - rewrite IHz; simpl; auto.
  - rewrite IHz; simpl; auto.
  - rewrite IHz; simpl; auto.
  - rewrite IHz; simpl; auto.
  - rewrite IHz; simpl; auto.
Qed.

Lemma  appl_fromZContext:
  forall {A B E1 E2} (z: ZContext E1 A E2 B) (p: OProg E1 A),
       appl (fromZContext z) p = zappl z p.
Proof.
  intros; unfold fromZContext; rewrite appl_fromZContext_; simpl; auto.
Qed.

Lemma toZContext_fromZContext_:
  forall {E2 E3 B C} (z: ZContext E2 B E3 C) {E1 A} (c: Context E1 A E2 B),
  toZContext (fromZContext_ z c) = toZContext_ c z.
Proof.
  intros E2 E3 B C z; induction z; intros E0 A0 c0.
  - simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
  - simpl; rewrite IHz; simpl; auto.
Qed. 

Lemma toZContext_fromZContext:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B),
  toZContext (fromZContext z) = z.
Proof.
  intros; unfold fromZContext; apply toZContext_fromZContext_.
Qed.

(*
Inductive Concat : list Type -> list Type -> list Type -> Type :=
  | CNil    : forall E, Concat nil E E
  | CCons : forall A E1 E2 E3, Concat E1 E2 E3 -> Concat (A::E1) (A::E2) E3.

Fixpoint concat_nil_r  {E}: Concat E E nil :=
  match E with
  | nil     => CNil nil
  | X::Xs => CCons X Xs Xs nil (concat_nil_r)
  end.
Fixpoint appendEnv_ {E1} (env: Env E1): forall E2, Env E2 -> Env (E1 ++ E2) :=
  match env in (Env E1) return (forall E2, Env E2 -> Env (E1 ++ E2)) with
  | Nil            => (fun E2 env2 => env2)
  | Cons x xs => (fun E2 env2 => Cons x (appendEnv_ xs _ env2))
  end.
*)


(* The semantic domain *)
Parameter D : Type -> Type.

(* The semantic function for global, i.e. non-backtracking, state *)
Parameter run : forall {A}, Prog A -> D A.

(* The algebra for the signature *)
Parameter retD: forall {A}, A -> D A.
Parameter failD : forall {A}, D A.
Parameter orD : forall {A}, D A -> D A -> D A.
Parameter getD : forall {A}, (S -> D A) -> D A.
Parameter putD : forall {A}, S -> D A -> D A.

Parameter andD : forall {A}, D A -> D A -> D A.

(* run is a fold with the algebra *)
Parameter run_ret: forall {A} (x: A), run (Return x) = retD x.
Parameter run_fail: forall {A}, @run A Fail = failD.
Parameter run_or: forall {A} (p q: Prog A), run (Or p q) = orD (run p) (run q).
Parameter run_get: forall {A} (p: S -> Prog A),     run (Get p) = getD (fun s => run (p s)).
Parameter run_put:forall {A} (s: S) (p: Prog A), run (Put s p) = putD s (run p).

(* Derived definitions for open programs *)
Definition orun : forall {A E}, OProg E A -> Env E -> D A := fun _ _ p env => run (p env).

Lemma orun_fail:
  forall {A E},
    @orun A E (fun env => Fail) = fun _ => failD.
Proof.
  intros; apply functional_extensionality; intro env;  unfold orun; auto using run_fail.
Qed.

Lemma orun_or:
  forall {A E} (p q: OProg E A),
    orun (fun env => Or (p env) (q env)) = fun env => orD (orun p env) (orun q env).
Proof.
  intros; apply functional_extensionality; intro env; unfold orun. auto using run_or.
Qed.

Lemma orun_get:
  forall {A E} (p: S -> OProg E A),
    orun (fun env => Get (fun s => p s env)) = fun env => getD (fun s => orun (p s) env).
Proof.
  intros; apply functional_extensionality; intro env; unfold orun; auto using run_get.
Qed.

Lemma orun_put:
  forall {E A} (s: Env E -> S) (p: OProg E A),
    orun (fun env => Put (s env) (p env)) = fun env => putD (s env) (orun p env).
Proof.
  intros; apply functional_extensionality; intro env; unfold orun; auto using run_put.
Qed.


Parameter get_get_G_D:
  forall {A} (k: S -> S -> D A),
    getD (fun s => getD (fun s' => k s s'))
    =
    getD (fun s => k s s).

(*
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Generalizable All Variables.

Print pointwise_relation.

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof. intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x). Qed.
*)

Lemma get_get_G':
  forall {A} (k: S -> S -> Prog A),
    run (Get (fun s => Get (fun s' => k s s')))
    =
    run (Get (fun s => k s s)).
Proof.
  intros A k.
  repeat rewrite run_get.
  erewrite (@f_equal _ _ _ _ (fun s : S => getD (fun s' : S => run (k s s'))) _).
  - rewrite get_get_G_D.
  reflexivity.
  Unshelve.
  apply functional_extensionality; intro s0.
  rewrite run_get; auto.
Qed.

Lemma meta_G:
  forall {A B E1 E2} {X}  (p q: X -> Prog A)
    (meta_G': forall (x: X), run (p x) = run (q x)) 
    (f: Env E1 -> X)
    (c: Context E1 A E2 B),
    orun (appl c (fun env => p (f env)))
    = 
    orun (appl c (fun env => q (f env))).
Proof.
  intros A B E1 E2 X p q meta_G' f c; induction c; simpl.
  - unfold orun; apply functional_extensionality; intro env0; apply meta_G'.
  - repeat rewrite orun_or; apply functional_extensionality; intro env; rewrite (IHc p q); auto.
  - repeat rewrite orun_or; apply functional_extensionality; intro env0; rewrite  (IHc p q); auto.
  - repeat rewrite orun_put; apply functional_extensionality; intro env0; rewrite (IHc p q); auto.
  - repeat rewrite orun_get; apply functional_extensionality; intro env0;
     apply f_equal; apply functional_extensionality; intro s0; destruct (b s0);
     [ unfold cpush, comap; change (orun (fun env => appl c ?p (Cons s0 env)) env0) with
                (orun (appl c p) (Cons s0 env0)); rewrite  (IHc p q); auto | auto ].
  - change (orun ?f) with (fun env => orun f env); apply functional_extensionality; intro env0;
     change (orun (fun env => if b env then ?f env else ?g env) env0) with
                 (orun (fun env => if b env0 then f env else g env) env0); destruct (b env0);
    [ change (fun env => appl c ?p env) with (appl c p); rewrite (IHc p q); auto | auto ].
  - unfold cpush, comap; change (orun (fun env => appl c0 ?p (Cons c env))) with
                                                   (fun env => orun (appl c0 p) (Cons c env));
    apply functional_extensionality; intro env0; rewrite (IHc p q); auto.
 - unfold clift, comap;
   change (orun (fun env => appl c ?p (tail env))) with
               (fun env => orun (appl c p) (@tail C _ env));
   apply functional_extensionality; intro env0; rewrite (IHc p q);
  auto.
Qed.

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

Parameter get_put_G_D:
  forall {A} (p: D A),
    getD (fun s => putD s p)
   =
   p.

Parameter get_put_G:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (k: OProg E1 A),
    orun (appl c (fun env => Get (fun s => Put s (k env))))
   =
   orun (appl c k).

Parameter put_get_G_D:
  forall {A} (s: S) (k: S -> D A),
  putD s (getD k)
  =
  putD s (k s).

Lemma put_get_G':
  forall {A} (s: S) (p: S -> Prog A),
    run (Put s (Get p))
    =
    run (Put s (p s)).
Proof.
  intros; rewrite run_put, run_get, run_put.
  apply (put_get_G_D s (fun s => run (p s))).
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

Parameter put_put_G_D:
  forall {A} (s s': S) (p: D A),
  putD s (putD s' p)
  =
  putD s' p.

Parameter put_put_G':
  forall {A} (v1 v2: S) (q: Prog A),
    run (Put v1 (Put v2 q))
   =
   run (Put v2 q).

Parameter put_put_G:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (v1 v2: Env E1 -> S) (k: OProg E1 A),
    orun (appl c (fun env => Put (v1 env) (Put (v2 env) (k env))))
    =
   orun (appl c (fun env => Put (v2 env) (k env))).

Parameter put_or_G_D:
  forall {A} (p q: D A) (s: S),
   orD (putD s p) q
   = 
   putD s (orD p q).

Parameter put_or_G':
  forall {A} (p q: Prog A) (s: S),
    run (Or (Put s p) q)
   = 
   run (Put s (Or p q)).

Parameter put_or_G:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (p: OProg E1 A) (q: OProg E1 A) (s: Env E1 -> S),
    orun (appl c (fun env => Or (Put (s env) (p env)) (q env)))
   = 
   orun (appl c (fun env => Put (s env) (Or (p env) (q env)))). 

Parameter or_fail:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (q: OProg E1 A), 
    orun (appl c (fun env => Or Fail (q env)))
    =
    orun (appl c q).

Parameter fail_or':
  forall {A} (q: Prog A),
    run (Or q Fail)
    =
    run q.

Parameter fail_or:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (q: OProg E1 A), 
    orun (appl c (fun env => Or  (q env) Fail))
    =
    orun (appl c q).

Parameter or_or':
  forall {A} (p q r: Prog A),
    run (Or (Or p q) r)
    =
    run (Or p (Or q r)).

Parameter or_or:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (p q r: OProg E1 A),
    orun (appl c (fun env => Or (Or (p env) (q env)) (r env)))
   =
   orun (appl c (fun env => Or (p env) (Or (q env) (r env)))).

Parameter put_ret_or_G_D:
  forall {A}  (v: S) (w: A) (q: D A),
  putD v (orD (retD w) q)
  =
  andD (putD v (retD w)) (putD v q).

Parameter put_ret_or_G:
  forall {A} (v: S) (w: A) (q: Prog A),
  run (Put v (Or (Return w) q))
  =
  andD (run (Put v (Return w))) (run (Put v q)).



(*
Definition castConcat_ {E1 E2 E3} (c: Concat E1 E2 E3) :  
  (match E1 with 
   | nil => (forall {A}, OProg E2 A -> OProg E3 A) 
   | X :: Xs => (forall {A}, X -> OProg E2 A -> (forall {E2'}, Concat Xs E2' E3 -> OProg E2' A -> OProg E3 A) -> OProg E3 A)
   end):=
  match c in (Concat E1 E2 E3) return (match E1 with 
                                                           | nil => (forall {A}, OProg E2 A -> OProg E3 A) 
                                                           | X :: Xs => (forall {A}, X -> OProg E2 A -> (forall {E2'}, Concat Xs E2' E3 -> OProg E2' A -> OProg E3 A) -> OProg E3 A) 
                                                           end) with
  | CNil _ => (fun A p => p)
  | CCons _ _ _ _ pf => (fun A x p k => k _ pf (cpush x p))
  end.

Definition castConcatNil {E2 E3} (c: Concat nil E2 E3): forall {A}, OProg E2 A -> OProg E3 A :=
  castConcat_ c.

Definition castConcatCons {X Xs E2 E3} (c: Concat (X::Xs) E2 E3): forall {A}, X -> OProg E2 A -> (forall {E2'}, Concat Xs E2' E3 -> OProg E2' A -> OProg E3 A) -> OProg E3 A :=
  castConcat_ c.

Fixpoint cpushes_ {E1} (env: Env E1): forall {A E2 E3}, Concat E1 E2 E3 -> OProg E2 A -> OProg E3 A :=
  match env in (Env E1) return (forall {A E2 E3}, Concat E1 E2 E3 -> OProg E2 A -> OProg E3 A) with
  | Nil => (fun _ _ _ pf p => castConcatNil pf p)
  | Cons x xs => (fun _ _ _ pf p => castConcatCons pf x p (fun E2' => @cpushes_ _ xs _ E2' _))
  end.

Definition cpushes {E} (env: Env E): forall {A}, OProg E A -> OProg nil A :=
  fun A => cpushes_ env concat_nil_r.
*)








(* Translating the syntx of local state semantics programs to global state semantics programs *)
Fixpoint trans {A} (p: Prog A): Prog A :=
  match p with
  | Return x => Return x
  | Or p q => Or (trans p) (trans q)
  | Fail => Fail
  | Get p => Get (fun s => trans (p s))
  | Put s p => Get (fun s0 => Or (Put s (trans p)) (Put s0 Fail))
  end.

Definition otrans {E A}: OProg E A -> OProg E A :=
  fun p env => trans (p env).

(* Translating contexts *)
Fixpoint transC {E1 E2: list Type} {A B: Type} (c: Context E1 A E2 B) : Context E1 A E2 B :=
  match c in (Context E1 A E2 B) return (Context E1 A E2 B) with
  | CHole           => CHole
  | COr1 c q      => COr1 (transC c) (otrans q)
  | COr2 p c      => COr2 (otrans p) (transC c)
  | CPut v c       => CGet (fun s => true) (COr1 (CPut (fun env => v (tail env)) (CLift (transC c))) (fun env => Put (head env) Fail)) (fun s env => Fail)
  | CGet t c q    => CGet t (transC c) (fun s => otrans (q s))
  | CDelay t c q => CDelay t (transC c) (otrans q) 
  | CPush x c    => CPush x (transC c)
  | CLift c         => CLift (transC c)
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
  intros; unfold oevl, orun, otrans; simpl; rewrite run_fail; auto.
Qed.

Lemma oevl_or:
  forall {A E} (p q: OProg E A),
    oevl (fun env => Or (p env) (q env)) = fun env => orD (oevl p env) (oevl q env).
Proof.
  intros; unfold oevl, orun, otrans; simpl; apply functional_extensionality; intro env; rewrite run_or; auto.
Qed.

Lemma oevl_get:
  forall {A E} (p: S -> OProg E A),
    oevl (fun env => Get (fun s => p s env)) = fun env => getD (fun s => oevl (p s) env).
Proof.
  intros; unfold oevl, orun, otrans; simpl; apply functional_extensionality; intro env; rewrite run_get; auto.
Qed.

Lemma oevl_put:
  forall {A E} (s: Env E -> S) (p: OProg E A),
    oevl (fun env => Put  (s env) (p env)) = fun env => getD (fun s0 => orD (putD (s env) (oevl p env)) (putD s0 failD)).
Proof.
  intros; unfold oevl, orun, otrans; simpl; apply functional_extensionality; intro env; rewrite run_get.
  apply f_equal, functional_extensionality; intro s0. 
  rewrite run_or; rewrite run_put. rewrite run_put; rewrite run_fail. auto.
Qed.

(* Proofs of the local state laws *)

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
     ** repeat rewrite run_or. rewrite (IHp0_1 p q), (IHp0_2 p q); auto.
     ** repeat rewrite run_get. apply f_equal, functional_extensionality; intro x; rewrite (H x p q); auto.
     ** repeat rewrite run_get; apply f_equal, functional_extensionality; intro s0. repeat rewrite run_or.
         apply equal_f, f_equal. repeat rewrite run_put; apply f_equal; auto.
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

Lemma get_get_L_1:
  forall {A B E1 E2} (c: Context E1 A E2 B) (k: S -> S -> OProg E1 A),
    oevl (appl c (fun env => Get (fun s1 => Get (fun s2 => k s1 s2 env))))
    =
    oevl (appl c (fun env => Get (fun s1 => k s1 s1 env))).
Proof.
  intros A B E1 e2 c k; unfold oevl, evl.
  repeat  rewrite otrans_appl; unfold otrans; simpl. rewrite get_get_G; auto.
Qed.

Lemma get_get_L_2:
  forall {A B C E1 E2} (c: Context E1 C E2 B) (k: S -> S -> OProg E1 A) (q: A -> OProg E1 C),
    oevl (appl c (obind (fun env => Get (fun s1 => Get (fun s2 => k s1 s2 env))) q))
    =
    oevl (appl c (obind (fun env => Get (fun s1 => k s1 s1 env)) q)).
Proof.
  intros A B C E1 E2 c k q.
  unfold obind; simpl. rewrite get_get_L_1; auto.
Qed.

Lemma invert_zappl_zput:
  forall {E1 E2 A B} (z: ZContext E1 A E2 B) (v: Env E1 -> S) (q: OProg E1 A),
     zappl z (fun env => Put (v env) (q env))
     =
     zappl (ZPut z v) q.
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

Lemma put_get_L_2:
  forall {A B E1 E2} (c: Context E1 A E2 B) (k: S -> OProg E1 A) (v: S) q,
    oevl (appl c (obind (fun env => Put v (Get (fun s => k s env)) ) q))
    =
    oevl (appl c (obind (fun env => Put v (k v env)) q)).
Proof.
  intros; unfold obind; simpl; apply put_get_L_1.
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
  repeat rewrite invert_zappl_zget.
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

Lemma put_fail_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (v: Env E1 -> S) (q: A -> OProg E1 B),
    oevl (appl c (obind (fun env => Put (v env) Fail) q))
   = 
   oevl (appl c (obind (fun env => Fail) q)).
Proof.
  intros; unfold obind; simpl; apply put_fail_L_1.
Qed.

Lemma put_or_trans:
  forall {E1 A} (p: OProg E1 A) {E2 B} (c: Context E1 A E2 B) (v: Env E1 -> S) (q: OProg E1 A),
    orun (appl c (fun env => Put (v env) (Or (otrans p env) (q env))))
    =
    orun (appl c (fun env => Or (Put (v env) (otrans p env)) (Put (v env) (q env)))).
Proof.
  intros E1 A p.
  - intros E2 B c v q.
    induction c; simpl.
     * unfold orun, otrans; apply functional_extensionality; intro env. induction (p env); simpl.
       -- rewrite put_ret_or_G.
            rewrite <- (put_put_G' (v env) (v env) (q env)).
            rewrite <- put_ret_or_G.
           rewrite <- put_or_G'.
           reflexivity.
       -- rewrite run_put.
            rewrite or_fail'.
            rewrite put_or_G'.
           rewrite run_put.
           rewrite or_fail'.
           repeat rewrite <- run_put.
           rewrite put_put_G'.
           reflexivity.
       -- rewrite run_put.
            rewrite or_or'.
            rewrite <- run_put.
            change (Or (trans p0_2) (q env)) with ((fun env => Or (trans p0_2) (q env)) env).
            rewrite (IHp0_1(fun env => Or (trans p0_2) (q env))).
            rewrite run_or.
            rewrite IHp0_2.
            rewrite <- run_or.
            rewrite <- or_or'.
            rewrite run_or.
            change (trans p0_2) with ((fun env => trans p0_2) env) at 1.
            rewrite <- IHp0_1.
            rewrite <- run_or; auto.
            auto.
            auto.
       -- repeat rewrite <- put_or_G'.
            repeat rewrite run_or.
            repeat rewrite put_get_G'. 
            repeat rewrite <- run_or.
            repeat rewrite put_or_G'.
            rewrite H.
            rewrite put_or_G'.
            reflexivity.
            auto.
      -- repeat rewrite <- put_or_G'.
           repeat rewrite run_or.
           repeat rewrite put_get_G'.
           repeat rewrite <- put_or_G'.
           repeat rewrite run_or.
           repeat rewrite put_put_G'.
           repeat rewrite <- run_or.
           repeat rewrite or_or'.
           repeat rewrite run_or.
           apply f_equal.
           repeat rewrite <- run_or.
           repeat rewrite put_or_G'.
           repeat rewrite run_put.
           repeat rewrite or_fail'.
           repeat rewrite <- run_put.
           rewrite put_put_G'.
           reflexivity.
    * unfold orun in *. apply functional_extensionality; intro env.
      repeat rewrite run_or.
     assert (IHc' : forall (p : OProg E1 A) (v : Env E1 -> S) (q : OProg E1 A) (env: Env E2),
      (run
         (appl c (fun env0 : Env E1 => Put (v env0) (Or (otrans p env0) (q env0)))
            env)) =
      (run
         (appl c
            (fun env0 : Env E1 =>
             Or (Put (v env0) (otrans p env0)) (Put (v env0) (q env0))) env))).
         ** intros p0 v0 q0. apply equal_f. apply IHc.
         ** rewrite IHc'. auto.
   *  unfold orun in *. apply functional_extensionality; intro env.
      repeat rewrite run_or.
     assert (IHc' : forall (p : OProg E1 A) (v : Env E1 -> S) (q : OProg E1 A) (env: Env E2),
      (run
         (appl c (fun env0 : Env E1 => Put (v env0) (Or (otrans p env0) (q env0)))
            env)) =
      (run
         (appl c
            (fun env0 : Env E1 =>
             Or (Put (v env0) (otrans p env0)) (Put (v env0) (q env0))) env))).
         ** intros p0 v0 q0. apply equal_f. apply IHc.
         ** rewrite IHc'. auto.
   * unfold orun in *. apply functional_extensionality; intro env.
     repeat rewrite run_put.
       assert (IHc' : forall (p : OProg E1 A) (v : Env E1 -> S) (q : OProg E1 A) (env: Env E2),
      (run
         (appl c (fun env0 : Env E1 => Put (v env0) (Or (otrans p env0) (q env0)))
            env)) =
      (run
         (appl c
            (fun env0 : Env E1 =>
             Or (Put (v env0) (otrans p env0)) (Put (v env0) (q env0))) env))).
         ** intros p0 v0 q0. apply equal_f. apply IHc.
         ** rewrite IHc'. auto.
   *  unfold orun in *. apply functional_extensionality; intro env.
     repeat rewrite run_get. apply f_equal; apply functional_extensionality; intro s0.
     destruct (b s0).
     -- unfold cpush, comap. 
       assert (IHc' : forall (p : OProg E1 A) (v : Env E1 -> S) (q : OProg E1 A) (env: Env (S::E2)),
      (run
         (appl c (fun env0 : Env E1 => Put (v env0) (Or (otrans p env0) (q env0)))
            env)) =
      (run
         (appl c
            (fun env0 : Env E1 =>
             Or (Put (v env0) (otrans p env0)) (Put (v env0) (q env0))) env))).
         ** intros p0 v0 q0. apply equal_f. apply IHc.
         ** rewrite IHc'. auto.
   -- auto.
  * change (orun (fun env => if b env then ?f env else ?g env))
       with (fun env0 => orun (fun env => if b env0 then f env else g env) env0).
     apply functional_extensionality; intro env0.
     destruct (b env0).
     ** rewrite IHc; auto.
    ** auto. 
  * unfold cpush, comap.
    change (orun (fun env => ?f (Cons c env))) 
      with (fun env => orun f (Cons c env)).
      apply functional_extensionality; intro env.
     rewrite IHc; auto.
  * unfold clift, comap.
        change (orun (fun env => ?f (tail env))) 
      with (fun env => orun f (@tail C _ env)).
      apply functional_extensionality; intro env.
    rewrite IHc; auto.
Qed.

Lemma get_put_L_1:
  forall {E1 E2 A B} (c: Context E1 A E2 B) (p: OProg E1 A),
    oevl (appl c (fun env => Get (fun s => Put s (p env))))
    =
    oevl (appl c p).
Proof.
  intros; unfold oevl; repeat rewrite otrans_appl; unfold otrans; simpl.
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

Lemma get_put_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (p: OProg E1 A) (q: A -> OProg E1 B),
    oevl (appl c (obind (fun env => Get (fun s => Put s (p env))) q))
    =
    oevl (appl c (obind p q)).
Proof.
    intros; unfold obind; simpl; apply get_put_L_1.
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

Lemma put_put_L_2:
  forall {E1 E2 A B C} (c: Context E1 B E2 C) (v: Env E1 -> S) (w: Env E1 -> S) (p: OProg E1 A) (k: A -> OProg E1 B),
    oevl (appl c (obind (fun env => Put (v env) (Put (w env) (p env))) k))
    =
    oevl (appl c (obind (fun env => Put (w env) (p env)) k)).
Proof.
    intros; unfold obind; simpl; apply put_put_L_1.
Qed.

(* TODO:
   - derive non-primitive parameters from primitive parameters
   - prove meta lemma + application to get derived lemmas
   - prove implementation
*)

End Syntax.

Module Implementation <: Syntax.

Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Parameter S : Type.

Definition D : Type -> Type := 
  fun A => S -> (list (A * S) * S).

Definition retD : forall {A}, A -> D A :=
  fun A => (fun x => (fun s => ((x,s) :: nil, s))).

Definition failD : forall {A}, D A :=
  fun A => (fun s => (nil, s)).

Definition orD : forall {A}, D A -> D A -> D A :=
  fun A xs ys => 
      (fun s => match xs s with
                     | (ansx, s') => match ys s' with
                                         | (ansy, s'') => (ansx ++ ansy, s'')
                                         end
                     end).

Definition getD : forall {A}, (S -> D A) -> D A :=
  fun A k => 
     (fun s => k s s).

Definition putD : forall {A}, S -> D A -> D A :=
  fun A s k =>
    (fun _ => k s).

Definition andD : forall {A}, D A -> D A -> D A :=
  fun A xs ys =>
    (fun s => match xs s, ys s with
                   | (ansx,_), (ansy, s') => (ansx ++ ansy, s')
                  end).

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

Lemma or_or_D:
  forall {A} (p q r: D A),
  orD (orD p q) r
  =
  orD p (orD q r).
Proof.
  intros; unfold orD.
  apply functional_extensionality; intro s0.
  destruct (p s0); destruct (q s); destruct (r s1).
  rewrite app_assoc.
  auto.
Qed.

Lemma put_ret_or_G_D:
  forall {A}  (v: S) (w: A) (q: D A),
  putD v (orD (retD w) q)
  =
  andD (putD v (retD w)) (putD v q).
Proof.
  auto.
Qed.


End Implementation.