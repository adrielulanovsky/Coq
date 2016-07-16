Section Ej1.

Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Omega.

Fixpoint Elim (n : nat) (l : list nat) : list nat :=
  match l with
      | nil => nil
      | cons a ls => if beq_nat a n then Elim n ls
                                    else cons a (Elim n ls)
  end.

Lemma ej1b_1 : forall (l : list nat) (x : nat), Elim x (Elim x l) = Elim x l.
Proof.
  induction l.
  simpl.
  trivial.
  intro.
  simpl.
  case_eq (beq_nat a x); intro.
  apply IHl.
  simpl.
  rewrite H.
  rewrite IHl.
  trivial.
Qed.

Lemma ej1b_2 : forall (l : list nat) (x : nat), length (Elim x l) <= length l.
Proof.
  induction l; intro.
  simpl.
  trivial.
  simpl.
  case_eq (beq_nat a x); intro.
  pose proof ((Lt.le_lt_n_Sm (length (Elim x l)) (length l)) (IHl x)) as H1.
  pose proof ((Lt.lt_le_weak (length (Elim x l)) (S (length l))) H1).
  assumption.
  simpl.
  SearchAbout le.
  apply Le.le_n_S.
  apply IHl.
Qed.

End Ej1.

Section Ej2.

Variable A : Set.

Inductive Prefijo : list A -> list A -> Prop :=
  | Pre_1 : forall l : list A, Prefijo nil l
  | Pre_2 : forall (a : A) (l1 l2 l3 : list A),
            Prefijo l1 l2 -> Prefijo (cons a l1) (cons a l2).

Lemma inyect : forall (x:A) (l1 l2 : list A),  l1 = l2 -> x :: l1 = x :: l2.
Proof.
  induction l1; intros;
  rewrite H;
  trivial.
Qed.

Lemma ej2b_1 : forall (l1 l2 : list A),
               Prefijo l1 l2 /\ Prefijo l2 l1 -> l1 = l2.
Proof.
  induction l1; intros; inversion H; clear H.
  inversion H1.
  trivial.
  destruct l2.
  inversion H0.
  inversion H0.
  apply (inyect a0 l1 l2).
  apply IHl1.
  inversion H1.
  split; assumption.
Qed.

Lemma ej2b_2 : forall (l1 l2 l3 : list A), 
               Prefijo l1 l2 -> Prefijo l2 l3 -> Prefijo l1 l3.
Proof.
  induction l1; intros.
  constructor.
  inversion H0.
  rewrite <- H1 in H.
  inversion H.
  rewrite <- H2 in H.
  inversion H.
  constructor.
  assumption.
  apply (IHl1 l0 l4);
  assumption.
Qed.

End Ej2.


Section Ej3.

Definition Var := nat.
Definition Valor := nat.
Definition Memoria := Var -> Valor.

Inductive Instr : Set :=
  | Assign : Var -> Valor -> Instr
  | Seq : Instr -> Instr -> Instr
  | IfEq : Var -> Var -> Instr -> Instr
  | Repeat : nat -> Instr -> Instr.

Definition update (m: Memoria) (v: Var) (val : Valor) : Memoria :=
  fun (x : Var) => if beq_nat x v then val
                                     else m x.
Definition lookup (m : Memoria) (v : Var) : Valor := m v.

Inductive Execute : Instr -> Memoria -> Memoria -> Prop :=
  | xAss: forall (v: Var) (val : Valor) (m : Memoria),
          Execute (Assign v val) m (update m v val)
  | xSeq: forall (i1 i2 : Instr) (m1 m2 m3 : Memoria),
          Execute i1 m1 m2 -> Execute i2 m2 m3 -> Execute (Seq i1 i2) m1 m3
  | xIfF: forall (i : Instr) (v1 v2 : Var) (m : Memoria),
          lookup m v1 <> lookup m v2 -> Execute (IfEq v1 v2 i) m m
  | xIfT: forall (i : Instr) (v1 v2 : Var) (m1 m2 : Memoria),
          lookup m1 v1 = lookup m1 v2 -> Execute i m1 m2
          -> Execute (IfEq v1 v2 i) m1 m2
  | xRepO: forall (i : Instr) (m : Memoria), Execute (Repeat 0 i) m m
  | xRepS: forall (i : Instr) (n : nat) (m1 m2 m3 : Memoria),
           Execute i m1 m2 -> Execute (Repeat n i) m2 m3
           -> Execute (Repeat (S n) i) m1 m3.

Lemma ej3d_1 : forall (v : Var) (val : Valor) (m : Memoria),
               lookup (update m v val) v = val.
Proof.
  intros.
  unfold lookup.
  unfold update.
  pose proof beq_nat_refl v.
  rewrite <- H.
  trivial.
Qed.

Lemma ej3d_2 : forall (v1 v2 : Var) (val : Valor) (m : Memoria),
               v1 <> v2 -> lookup (update m v1 val) v2 = lookup m v2.
Proof.
  intros.
  unfold lookup.
  unfold update.
  case_eq (beq_nat v2 v1); intro.
  apply beq_nat_true in H0.
  elim H.
  symmetry.
  trivial.
  trivial.
Qed.

Lemma ej3d_3 : forall (v1 v2 : Var) (m1 m2 : Memoria) (i : Instr),
               lookup m1 v1 = lookup m1 v2 -> Execute (IfEq v1 v2 i) m1 m2
               -> Execute (Repeat 1 i) m1 m2.
Proof.
  intros.
  apply (xRepS i 0 m1 m2 m2).
  inversion H0.
  elim H6.
  rewrite <- H5.
  assumption.
  assumption.
  constructor.
Qed.

Lemma ej3d_4 : forall (n : nat) (m1 m2 : Memoria) (i : Instr),
               Execute (Seq i (Repeat n i)) m1 m2 
               -> Execute (Repeat (S n) i) m1 m2.
Proof.
  intros.
  inversion H.
  apply (xRepS i n m1 m3 m2).
  assumption.
  assumption.
Qed.

Lemma ej3d_5 : forall (n1 n2 : nat) (m1 m2 m3 : Memoria) (i : Instr),
               Execute (Repeat n1 i) m1 m2 -> Execute (Repeat n2 i) m2 m3
               -> Execute (Repeat (n1 + n2) i) m1 m3.
Proof.
  induction n1; intros.
  simpl.
  inversion H.
  assumption.
  replace (S n1 + n2) with (S (n1 + n2)).
  inversion H.
  apply (xRepS i (n1+n2) m1 m4 m3).  
  assumption.
  apply (IHn1 n2 m4 m2 m3).
  assumption.
  assumption.
  omega.
Qed.
               