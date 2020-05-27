(*

  Syntax definitions for pattern matching synthesis problem.

  (C) Dmitry Boulytchev, JetBrains Research, St. Petersburg State University, 2020.

*)

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.

(* A workout on certified relational synthesis for pattern matching *)

(* A synonym for names of constructors *)
Definition name := nat.

Definition name_eqb := Nat.eqb.
                             
(* Values; we consider only leaves and binary constructors for
   simplicity. We also do not assign hard arities for constructors.
*)
Inductive Value : Set :=
  L : forall (cst : name)              , Value
| N : forall (cst : name) (l r : Value), Value.

(* Gets the top-level constructor *)
Definition cst_of (v : Value) : name :=
  match v with
    L cst     => cst
  | N cst _ _ => cst
  end.

(* Get the height of a value *)
Fixpoint height (v : Value) : nat :=
  match v with
    L _     => 1
  | N _ l r => 1 + Nat.max (height l) (height r)
  end.

(* Patterns *)
Inductive Pattern : Set :=
  pW : Pattern 
| pL : forall (cst : name)                , Pattern
| pN : forall (cst : name) (l r : Pattern), Pattern.

(* Gets the depth of a pattern *)
Fixpoint depth (v : Pattern) : nat :=
  match v with
    pW       => 1
  | pL _     => 1
  | pN _ l r => 1 + Nat.max (depth l) (depth r)
  end.

(* Declarative semantics for pattern matching *)

(* An ordered sequence of patterns *)
Definition Patterns := list Pattern.

(* The depth of patterns *)
Definition Depth (ps : Patterns) : nat := fold_left (fun d p => Nat.max d (depth p)) ps 0.

