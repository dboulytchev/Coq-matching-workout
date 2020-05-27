(*

  Correct and complete implementation definition for pattern matching synthesis problem.

  (C) Dmitry Boulytchev, JetBrains Research, St. Petersburg State University, 2020.

*)

Require Import SyntaxDef.
Require Import Declarative.
Require Import Switch.
        
(* The definition of a correct and complete pattern matching implementation *)
Definition CCI (ps : Patterns) (s : S) : Prop :=
  forall (v : Value) (i : nat), <| v ; ps |> = i <-> v |- s ==> i.

(* Elimination of universal quantifier over the set of answers *)
Lemma answer_quantifier_elimination (ps : Patterns) (s : S) :
  (forall (v : Value), exists (i : nat),  <| v ; ps |> = i /\ v |- s ==> i) -> CCI ps s.
Proof.
  intro H.
  unfold CCI.
  intros v i.
  split; intro H'; specialize (H v); inversion_clear H; inversion_clear H0.
  * rewrite H' in H. subst x. auto.
  * apply (eval_deterministic v s i H' x) in H1. subst i. auto.
Qed.
