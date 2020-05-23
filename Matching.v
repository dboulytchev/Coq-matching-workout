Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

(* A workout on certified relational synthesis for pattern matching *)

(* A synonym for names of constructors *)
Definition name := nat.

Definition name_eqb := Nat.eqb.
                             
(* Values; we consider only leaves, unary and binary constructors for
   simplicity. We also do not assign hard arities for constructors.
*)
Inductive Value : Set :=
  L : forall (cst : name)              , Value
| U : forall (cst : name) (s   : Value), Value
| B : forall (cst : name) (l r : Value), Value.

(* Gets the top-level constructor *)
Definition cstOf (v : Value) : name :=
  match v with
    L cst     => cst
  | U cst _   => cst
  | B cst _ _ => cst
  end.

(* Get the height of a value *)
Fixpoint height (v : Value) : nat :=
  match v with
    L _     => 1
  | U _ s   => 1 + height s
  | B _ l r => 1 + Nat.max (height l) (height r)
  end.

(* Patterns *)
Inductive Pattern : Set :=
  pW : Pattern 
| pL : forall (cst : name)                , Pattern
| pU : forall (cst : name) (s   : Pattern), Pattern
| pB : forall (cst : name) (l r : Pattern), Pattern.

(* Gets the depth of a pattern *)
Fixpoint depth (v : Pattern) : nat :=
  match v with
    pW       => 1
  | pL _     => 1
  | pU _ s   => 1 + depth s
  | pB _ l r => 1 + Nat.max (depth l) (depth r)
  end.

(* Declarative semantics for pattern matching *)

(* An ordered sequence of patterns *)
Definition Patterns := list Pattern.

(* The depth of patterns *)
Definition Depth (ps : Patterns) : nat := fold_left (fun d p => Nat.max d (depth p)) ps 0.

(* Matching against a single pattern *)
Fixpoint matchValue (v : Value) (p : Pattern) : bool :=
  match (v, p) with
    (L c    , pL c'      ) => name_eqb c c'
  | (U c s  , pU c' ps   ) => andb (name_eqb c c') (matchValue s ps)
  | (B c l r, pB c' pl pr) => andb (name_eqb c c') (andb (matchValue l pl) (matchValue r pr))  
  | (_, pW)                => true
  | (_, _ )                => false
  end.

(*
A propositional counterpart; I don't know yet if we would need it.

Inductive matchValue : Value -> Pattern -> Prop :=
  mvW : forall (v   : Value), matchValue v pW
| mvL : forall (cst : name ), matchValue (L cst) (pL cst)
| mvU : forall (cst : name ) (s : Value) (sp : Pattern) (H : matchValue s sp),
    matchValue (U cst s) (pU cst sp)
| mvB : forall (cst : name ) (l r : Value) (lp rp : Pattern) (HL : matchValue l lp) (HR : matchValue r rp),
    matchValue (B cst l r) (pB cst lp rp).
 *)

(* Matching against multiple patterns *)
Fixpoint matchoInner (i : nat) (v : Value) (ps : Patterns) : nat :=
  match ps with
    []       => i
  | p :: ps' => if matchValue v p then i else matchoInner (i+1) v ps'
  end.

Definition matcho (v : Value) (ps : Patterns) : nat :=
  matchoInner 0 v ps.

(* Note: the functionality of matcho comes for free! *)

Lemma indexBound_gen (v : Value) (ps : Patterns) (i j : nat) (H : matchoInner i v ps = j) : j <= i + 1 + length ps.
Proof.
  generalize dependent i.
  induction ps; intros i H; unfold matchoInner in H.
  * subst i. omega.
  * destruct (matchValue v a) eqn:D.
    - subst i. omega.
    - fold matchoInner in H. apply IHps in H. simpl. omega.
Qed.

(* Proves that the index of the result in declarative semantics is bounded by 0..length ps + 1*)
Lemma indexBound (v : Value) (ps : Patterns) (i : nat) (H : matcho v ps = i) : i <= 1 + length ps.
Proof. unfold matcho in H. apply indexBound_gen in H. auto. Qed.

(* The switch language *)

(* The matching expression *)
Inductive M : Set :=
  scr  : M
| sub  : forall (m : M), M
| subL : forall (m : M), M
| subR : forall (m : M), M.

(* The depth of a ,atching expression *)
Fixpoint mDepth (m : M) : nat :=
  match m with
    scr    => 1
  | sub  m => 1 + mDepth m
  | subL m => 1 + mDepth m
  | subR m => 1 + mDepth m
  end.
  
(* The semantics of matching expression *)
Inductive Mof : Value -> M -> Value -> Prop :=
  Mscr  : forall              (v      : Value)                                   , Mof v scr      v
| Msub  : forall (cst : name) (v w    : Value) (m : M) (H : Mof v m (U cst w))   , Mof v (sub m)  w
| MsubL : forall (cst : name) (v w w' : Value) (m : M) (H : Mof v m (B cst w w')), Mof v (subL m) w
| MsubR : forall (cst : name) (v w w' : Value) (m : M) (H : Mof v m (B cst w w')), Mof v (subR m) w'.

Lemma MofDeterministic (v w : Value) (m : M) (H : Mof v m w) :
  forall w', Mof v m w' -> w' = w.
Proof.
  generalize dependent w.
  induction m; intros w H w' H'; inversion H; inversion H'.
  * subst v0. subst v. auto.
  * apply (IHm (U cst w) H2 (U cst0 w')) in H6. inversion H6. reflexivity.
  * apply (IHm (B cst w w'0) H2 (B cst0 w' w'1)) in H6. inversion H6. reflexivity.
  * apply (IHm (B cst w0 w) H2 (B cst0 w1 w')) in H6. inversion H6. reflexivity.
Qed.
  
(* The switch language itself *)
Inductive S : Set :=
  Switch : forall (m : M) (bs : list (name * S)) (o : S), S
| Return : forall (i : nat), S.

(* The depth of a switch program *)
Fixpoint sDepth (s : S) : nat :=
  match s with
    Return _        => 0
  | Switch m br oth => fold_left (fun d p =>
                                    match p with
                                      (_, s) => Nat.max d (sDepth s)
                                    end
                                 ) br (Nat.max (mDepth m) (sDepth oth))
  end.

(* The semantics of the switch language *)
Inductive evalo : Value -> S -> nat -> Prop :=
  eReturn : forall (v : Value) (i : nat),
    evalo v (Return i) i
| eOther  : forall (v : Value) (i : nat) (oth : S) (m : M)
                   (H : evalo v oth i),
    evalo v (Switch m [] oth) i
| eHead   : forall (v w : Value) (i : nat) (m : M) (p : name) (ps : list (name * S)) (oth s' : S) 
                   (MH : Mof v m w)
                   (EH : cstOf w = p)
                   (H  : evalo v s' i),
    evalo v (Switch m ((p, s') :: ps) oth) i
| eTail   : forall (v w : Value) (i : nat) (m : M) (p : name) (ps : list (name * S)) (oth s' : S) 
                   (MH : Mof v m w)
                   (EH : cstOf w <> p)
                   (H  : evalo v (Switch m ps oth) i), evalo v (Switch m ((p, s') :: ps) oth) i.

(* The determinism of the switch language semantics *)
Lemma evaloDeterministic (v : Value) (s : S) (i : nat) (H : evalo v s i) :
  forall j,  evalo v s j -> j = i.
Proof.
  intros j Hj. induction H; inversion Hj.
  all: auto.
  all: apply (MofDeterministic v w m MH w0) in MH0; subst w0; exfalso; auto.
Qed.

(* The definition of a correct and complete pattern matching implementation *)
Definition CorrectAndCompleteImplementation (ps : Patterns) (s : S) : Prop :=
  forall (v : Value) (i : nat), matcho v ps = i <-> evalo v s i.

(* Elimination of universal quantifier over the set of answers *)
Lemma answerQantifierElimination (ps : Patterns) (s : S) :
  (forall (v : Value), exists (i : nat),  matcho v ps = i /\ evalo v s i) -> CorrectAndCompleteImplementation ps s.
Proof.
  intro H.
  unfold CorrectAndCompleteImplementation.
  intros v i.
  split; intro H'; specialize (H v); inversion_clear H; inversion_clear H0.
  * rewrite H' in H. subst x. auto.
  * apply (evaloDeterministic v s i H' x) in H1. subst i. auto.
Qed.

(*
Fixpoint DefaultImplementation (ps : Patterns) : S :=
 

Lemma CCIexists (ps : Patterns) : exists (s : S), CorrectAndCompleteImplementation ps s /\ sDepth s <= Depth ps.
  *)

