(*

  Trivial program for pattern matching implementation.

  (C) Dmitry Boulytchev, JetBrains Research, St. Petersburg State University, 2020.

*)

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import SyntaxDef.
Require Import Declarative.
Require Import Switch.
Require Import CCI.

Fixpoint ti_patt (m : M) (p : Pattern) (yes no : S) : S := 
  match p with
    pW         => yes
  | pL cst     => Switch m [(cst, yes)] no 
  | pN cst l r => Switch m [(cst, ti_patt (subL m) l
                                    (ti_patt (subR m) r yes no)
                                    no)]
                           no
  end.

Fixpoint ti_gen (i : nat) (m : M) (ps : Patterns) : S :=
  match ps with
    []      => Return i
  | p :: ps => ti_patt m p (Return i) (ti_gen (1+i) m ps)
  end.

Definition trivial (ps : Patterns) : S := ti_gen 0 scr ps.
