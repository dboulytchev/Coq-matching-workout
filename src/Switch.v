(*

  Switch language definition for pattern matching synthesis problem.

  (C) Dmitry Boulytchev, JetBrains Research, St. Petersburg State University, 2020.

*)

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Relations.Relation_Definitions.
Require Import SyntaxDef.
Require Import Declarative.

(* The matching expression *)
Inductive M : Set :=
  scr  : M
| subL : forall (m : M), M
| subR : forall (m : M), M.

(* The depth of a matching expression *)
Fixpoint depth_m (m : M) : nat :=
  match m with
    scr    => 1
  | subL m => 1 + depth_m m
  | subR m => 1 + depth_m m
  end.

(* The semantics of matching expression *)
Reserved Notation " v |- m => w" (at level 40, no associativity).

Inductive eval_m : Value -> M -> Value -> Prop :=
  Mscr  : forall              (v      : Value)                                   , v |- scr => v
| MsubL : forall (cst : name) (v w w' : Value) (m : M) (H : v |- m => N cst w w'), v |- subL m => w
| MsubR : forall (cst : name) (v w w' : Value) (m : M) (H : v |- m => N cst w w'), v |- subR m => w'
where "v |- m => w" := (eval_m v m w).

Lemma eval_m_deterministic (v w : Value) (m : M) (H : v |- m => w) :
  forall w', v |- m => w' -> w' = w.
Proof.
  generalize dependent w.
  induction m; intros w H w' H'; inversion H; inversion H'.
  * subst v0. subst v. auto. 
  * apply (IHm (N cst w w'0) H2 (N cst0 w' w'1)) in H6. inversion H6. reflexivity.
  * apply (IHm (N cst w0 w) H2 (N cst0 w1 w')) in H6. inversion H6. reflexivity.
Qed.
  
(* The switch language itself *)
Inductive S : Set :=
  Switch : forall (m : M) (bs : list (name * S)) (o : S), S
| Return : forall (i : nat), S.

Definition branches := list (name * S).

(* The depth of a switch program *)
Fixpoint depth_s (s : S) : nat :=
  match s with
    Return _        => 0
  | Switch m br oth => fold_left (fun d p =>
                                    match p with
                                      (_, s) => Nat.max d (depth_s s)
                                    end
                                 ) br (Nat.max (depth_m m) (depth_s oth))
  end.

(* The semantics of the switch language *)
Reserved Notation "v |- s ==> i" (at level 40, no associativity).

Inductive eval : Value -> S -> nat -> Prop :=
  eReturn : forall (v : Value) (i : nat), v |- Return i ==> i
| eOther  : forall (v : Value) (i : nat) (oth : S) (m : M)
                   (H : eval v oth i), v |- Switch m [] oth ==> i
| eHead   : forall (v w : Value) (i : nat) (m : M) (p : name) (ps : branches) (oth s' : S) 
                   (MH  : v |- m => w)
                   (EH  : cst_of w = p)
                   (H   : v |- s' ==> i), v |- Switch m ((p, s') :: ps) oth ==> i
| eTail   : forall (v w : Value) (i : nat) (m : M) (p : name) (ps : branches) (oth s' : S) 
                   (MH  : v |- m =>  w)
                   (EH  : cst_of w <> p)
                   (H   : v |- Switch m ps oth ==> i), v |- Switch m ((p, s') :: ps) oth ==> i
where "v |- s ==> i" := (eval v s i).

(* The determinism of the switch language semantics *)
Lemma eval_deterministic (v : Value) (s : S) (i : nat) (H : v |- s ==> i) : forall j, v |- s ==> j -> j = i.
Proof.
  intros j Hj. induction H; inversion Hj.
  all: auto.
  all: apply (eval_m_deterministic v w m MH w0) in MH0; subst w0; exfalso; auto.
Qed.

(* Program equivalence *)
Definition s_equiv  (s1 s2 : S) : Prop :=
  forall v i, v |- s1 ==> i <-> v |- s2 ==> i.

Notation "s1 ~~ s2" := (s_equiv s1 s2) (at level 41, no associativity).

(* Equivalence is an equivalence *)
Lemma s_equiv_refl : @reflexive S s_equiv.
Proof. intros. split; intro; auto. Qed.

Lemma s_equiv_symm : @symmetric S s_equiv.
Proof.
  intros x y H.
  split; intro; specialize (H v i); inversion_clear H; auto.
Qed.

Lemma s_equiv_trans : @transitive S s_equiv.
Proof.
  intros x y z H H0.
  split; intro; specialize (H v i); specialize (H0 v i); inversion_clear H; inversion_clear H0; auto.
Qed.

(* Rewriting of equivalent *)
Lemma rewrite_other
      (v    : Value)
      (i    : nat)
      (m    : M)
      (bs   : branches)
      (o o' : S)
      (Heq  : o ~~ o') 
      (Hev  : v |- Switch m bs o ==> i) : v |- Switch m bs o' ==> i.
Proof.
  induction bs; inversion Hev.
  * constructor. specialize (Heq v i). inversion_clear Heq. auto.
  * eapply eHead; eauto.
  * eapply eTail; eauto.
Qed.
  
Lemma rewrite_branches
      (v      : Value)
      (i      : nat)
      (m      : M)
      (bs bs' : branches)
      (o      : S)
      (Heq    : Switch m bs o ~~ Switch m bs' o) 
      (Hev    : v |- Switch m bs o ==> i) : v |- Switch m bs' o ==> i.
Proof.
  specialize (Heq v i). inversion_clear Heq. auto.
Qed.

(* Equivalence is a congruence *)
Lemma s_equiv_congruence
      (m       : M)
      (o1  o2  : S)
      (bs1 bs2 : branches)
      (Eqo     : o1 ~~ o2)
      (Eqbs    : Switch m bs1 o1 ~~ Switch m bs2 o1) : Switch m bs1 o1 ~~ Switch m bs2 o2.
Proof.
  destruct bs1; intros v i; split; intro HL.
    * eapply rewrite_other. eauto. eapply rewrite_branches; eauto.
    * apply s_equiv_symm in Eqo. apply (rewrite_other v i m bs2 o2 o1 Eqo) in HL.
      apply s_equiv_symm in Eqbs.
      apply (rewrite_branches v i m bs2 [] o1 Eqbs) in HL. auto.
    * apply (rewrite_branches v i m (p::bs1) bs2 o1 Eqbs) in HL.
      eapply rewrite_other; eauto.
    * apply (rewrite_branches v i m bs2 (p::bs1) o1). apply s_equiv_symm. auto.
      eapply rewrite_other. apply s_equiv_symm. eauto. auto.
Qed.

(* A property of branches being sorted by constructors *)
Inductive sorted_branches : branches -> Prop :=
  sbNil  : sorted_branches []
| sbCons : forall (cst  : name)
                  (s    : S)
                  (bs   : branches)
                  (Hbs  : sorted_branches bs)
                  (Hord : forall cst' s', In (cst', s') bs -> cst < cst'),
    sorted_branches ((cst, s) :: bs).

(* Inserting in branch in a sort-preserving manner *)
Fixpoint insert (cst : name) (s : S) (bs : branches) : branches :=
  match bs with
    []                => [(cst, s)]
  | (cst', s') :: bs' =>
    if cst <? cst'
    then (cst, s) :: bs
    else if cst =? cst'
         then (cst, s) :: bs'
         else (cst', s') :: insert cst s bs'
  end.

(* Helper lemma *)
Lemma in_insert
      (cst cst' : name)
      (s s'     : S)
      (bs       : branches)
      (Hin      : In (cst', s') (insert cst s bs)) : (cst', s') = (cst, s) \/ In (cst', s') bs.
Proof.
  induction bs; simpl in Hin.
  * inversion_clear Hin. left. auto. auto.
  * destruct a. destruct (cst <? n) eqn:Dlt.
    + inversion Hin; [left | right]; auto.
    + destruct (cst =? n) eqn:Deq.
      - apply (beq_nat_true cst n) in Deq. subst n. inversion_clear Hin.
        { left. auto. }
        { right. simpl. right. auto. }
      - inversion_clear Hin.
        { right. rewrite <-H. constructor. reflexivity. }
        { specialize (IHbs H). inversion IHbs.
          { left. auto. }
          { right. simpl. right. auto. }
        }
Qed.
  
(* Inserting preserves sorting *)
Lemma insert_sorted (cst : name) (s : S) (bs : branches) (Hsort : sorted_branches bs) :
  sorted_branches (insert cst s bs).
Proof.
  induction bs.
  * simpl. econstructor. auto. intros cst' s' Hin. inversion Hin.
  * inversion_clear Hsort. simpl. destruct (cst <? cst0) eqn:Dcst.
    + constructor.
      - constructor; auto.
      - intros cst' s' HIn.
        rewrite (Nat.ltb_antisym cst0 cst) in Dcst.
        apply Bool.negb_true_iff in Dcst.
        apply leb_complete_conv in Dcst.
        inversion HIn.
        { inversion H. subst cst'. assumption. }
        { apply (Hord cst' s') in H. eapply Nat.lt_trans; eauto. }
    + destruct (cst =? cst0) eqn:Deq.
      - apply beq_nat_true in Deq. subst cst. constructor; auto.
      - assert (A : cst0 < cst). 
        { rewrite Nat.ltb_antisym in Dcst.
          apply Bool.negb_false_iff in Dcst.
          apply (leb_complete cst0 cst) in Dcst.
          apply (beq_nat_false cst cst0) in Deq. omega. }
        constructor.
        { auto. }
        { intros cst' s' Hin. apply in_insert in Hin. inversion_clear Hin.
          { inversion H. assumption. }
          { eapply Hord. eauto. }
        }
Qed.          

(* Inserting preserves equivalence *)
Lemma insert_equiv (m : M) (cst : name) (s o : S) (bs : branches) (Hsort : sorted_branches bs) :
  Switch m ((cst, s) :: bs) o ~~ Switch m (insert cst s bs) o.
Proof.
  induction bs; simpl.
  * apply s_equiv_refl.
  * destruct a. destruct (cst <? n) eqn:Dlt.
    + apply s_equiv_refl.
    + destruct (cst =? n) eqn:Deq.
      - apply (beq_nat_true cst n) in Deq. subst n.
        intros v i. split; intro H; inversion_clear H.        
        { eapply eHead; eauto. }
        { eapply eTail; eauto. inversion_clear H0.
          { unfold not in EH.
            exfalso.
            apply (eval_m_deterministic v w m MH w0) in MH0.
            subst w0.
            auto. }
          { assumption. }          
        }
        { eapply eHead; eauto. }
        { eapply eTail; eauto. eapply eTail; eauto. }        
      - apply (beq_nat_false cst n) in Deq.
        intros v i. split; intro H; inversion_clear H.
        { eapply eTail.
          { eauto. }
          { unfold not in *. rewrite EH. auto. }
          { inversion_clear Hsort. specialize (IHbs Hbs v i). inversion_clear IHbs.
            apply H. eapply eHead; eauto.
          }          
        }
        { inversion_clear H0.
          { eapply eHead; eauto. }
          { eapply eTail; eauto.
            inversion_clear Hsort. specialize (IHbs Hbs v i). inversion_clear IHbs.
            apply H0. eapply eTail; eauto.
              apply (eval_m_deterministic v w m MH w0) in MH0. subst w0. auto.
          }
        }
        { eapply eTail.
          { eauto. }
          { unfold not in *. rewrite EH. intro H. symmetry in H. auto. }
          { eapply eHead; eauto. }
        }
        { 
          inversion_clear Hsort. specialize (IHbs Hbs v i). inversion_clear IHbs.
          apply H1 in H0. inversion_clear H0.
          { eapply eHead; eauto. }
          { eapply eTail; eauto.
            { eapply eTail; eauto.
              apply (eval_m_deterministic v w m MH w0) in MH0. subst w0. auto.
            }
          }
        }
Qed.      
      
(* Branch sorting *)
Fixpoint sort_branches (bs : branches) : branches :=
  match bs with
    []             => []
  | (cst, s) :: bs => insert cst s (sort_branches bs)
  end.

(* Branch sort sorts property *)
Lemma sort_sorts_branches (bs : branches) : sorted_branches (sort_branches bs).
Proof.
  induction bs; simpl.
  { constructor. }
  { destruct a. apply insert_sorted. auto. }
Qed.

(* Branch sort preserves the semantic *)
Lemma sort_equiv_branches (m : M) (bs : branches) (o : S) :
  Switch m bs o ~~ Switch m (sort_branches bs) o.
Proof.
  induction bs; intros v i; split; intro H; simpl; auto.
  * destruct a. apply insert_equiv.
    + apply sort_sorts_branches. 
    + inversion_clear H.
      - eapply eHead; eauto. 
      - eapply eTail; eauto. eapply rewrite_branches; eauto.
  * simpl in H. destruct a. apply insert_equiv in H.
    + inversion_clear H.
      - eapply eHead; eauto.
      - eapply eTail; eauto. eapply rewrite_branches; eauto. apply s_equiv_symm. auto.
    + apply sort_sorts_branches.
Qed.       
    
(* A property of programs to have sorted branches *)
Inductive sorted : S -> Prop :=
  nReturn  : forall (i    : nat), sorted (Return i)
| nSwitch  : forall (m    : M)
                    (o    : S)
                    (bs   : branches)
                    (Hso  : sorted o)                                        
                    (Hord : sorted_branches bs), sorted (Switch m bs o).

(* Sorting programs *)
Fixpoint sort (s : S) : S :=
  match s with
    Return i      => Return i
  | Switch m bs o => Switch m (sort_branches bs) (sort o)
  end.

(* Program sorting sorts properly *)
Lemma sort_sorts (s : S) : sorted (sort s).
Proof.
  induction s; simpl; constructor; auto; apply sort_sorts_branches.
Qed.

(* Program sorting preserves equivalence *)
Lemma sort_equiv (s : S) : s ~~ sort s.
Proof.
  induction s; simpl.
  * apply s_equiv_congruence; auto. apply sort_equiv_branches.
  * apply s_equiv_refl.
Qed.