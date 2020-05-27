(*

  Declarative semantics for pattern matching synthesis problem.

  (C) Dmitry Boulytchev, JetBrains Research, St. Petersburg State University, 2020.

*)

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.
Require Import SyntaxDef.

(* Matching against a single pattern *)
Fixpoint match_patt (v : Value) (p : Pattern) : bool :=
  match (v, p) with
    (L c    , pL c'      ) => name_eqb c c'
  | (N c l r, pN c' pl pr) => andb (name_eqb c c') (andb (match_patt l pl) (match_patt r pr))  
  | (_, pW)                => true
  | (_, _ )                => false
  end.

(* Matching against multiple patterns *)
Fixpoint match_gen (i : nat) (v : Value) (ps : Patterns) : nat :=
  match ps with
    []       => i
  | p :: ps' => if match_patt v p then i else match_gen (i+1) v ps'
  end.

Definition match_ (v : Value) (ps : Patterns) : nat :=
  match_gen 0 v ps.

Notation "<| v ; ps |>" := (match_ v ps) (at level 40, no associativity).

(* Note: the functionality of <| ; |> comes for free. *)

Lemma index_bound_gen (v : Value) (ps : Patterns) (i j : nat) (H : match_gen i v ps = j) : j <= i + 1 + length ps.
Proof.
  generalize dependent i.
  induction ps; intros i H; unfold match_gen in H.
  * subst i. omega.
  * destruct (match_patt v a) eqn:D.
    - subst i. omega.
    - fold match_gen in H. apply IHps in H. simpl. omega.
Qed.

(* Proves that the index of the result in declarative semantics is bounded by 0..length ps + 1*)
Lemma index_bound
      (v  : Value)
      (ps : Patterns)
      (i  : nat)
      (H  : <| v ; ps |> = i) : i <= 1 + length ps.
Proof. unfold match_ in H. apply index_bound_gen in H. auto. Qed.

