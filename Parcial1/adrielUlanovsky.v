Section Ej1.
Variables P R : Prop.

Require Import Classical.

Theorem lema1_1 : (P -> R) \/ (R -> P).
Proof.
  elim(classic R); intro.
  left.
  intro.
  assumption.
  right.
  intro.
  absurd R; assumption.
Qed.

End Ej1.


Section Ej2.

Variable Cuad : Prop. (* El animal es cuadrupedo *)
Variable Nada : Prop. (* El animal nada *)
Variable Herb : Prop. (* El animal es herbivoro *)
Variable TLeche : Prop. (* El animal toma leche *)
Variable Vuela : Prop. (* El animal vuela *)

Hypothesis Regla1 : Cuad -> ~Nada.
Hypothesis Regla2 : Herb -> Vuela.
Hypothesis Regla3 : ~TLeche -> Herb.
Hypothesis Regla4 : Vuela \/ ~TLeche.
Hypothesis Regla5 : Vuela -> Herb /\ Cuad.
Hypothesis Regla6 : Nada <-> Herb.

Theorem conclusion : False.
Proof.
  unfold not in Regla1.
  elim Regla6; intros R7 R8.
  elim Regla4.
  intro.
  apply Regla1.
  apply Regla5.
  assumption.
  apply Regla6.
  apply Regla5.
  assumption.
  intro.
  apply Regla1.
  apply Regla5.
  apply Regla2.
  apply Regla3.
  assumption.
  apply R8.
  apply Regla3.
  assumption.
Qed.

End Ej2.


Section Ej3.

Variable C : Set.
Parameter T : C -> C -> Prop.
Parameter U : C -> C -> Prop.

Theorem e3 : (forall (x y : C), (U x y -> ~(T x y))) /\ (exists z:C, T z z)
                    -> exists w:C, ~(U w w).
Proof.
  intro.
  elim H.
  intros.
  elim H1.
  intros.
  exists x.
  unfold not; intro.
  elim (H0 x x); assumption.
Qed.


End Ej3.

Section Ej4.

Variable Bool: Set.
Variable TRUE : Bool.
Variable FALSE : Bool.
Variable Not : Bool -> Bool.
Variable Or : Bool -> Bool -> Bool.
Variable And : Bool -> Bool -> Bool.

Axiom BoolVal : forall b : Bool, b = TRUE \/ b = FALSE.
Axiom NotTrue : Not TRUE = FALSE.
Axiom NotFalse : Not FALSE = TRUE.
Axiom AndTrue : forall b : Bool, And TRUE b = b.
Axiom AndFalse : forall b : Bool, And FALSE b = FALSE.
Axiom OrTrue : forall b : Bool, Or TRUE b = TRUE.
Axiom OrFalse : forall b : Bool, Or FALSE b = b.

Lemma lema4_1 : forall b : Bool, Not (Not b) = b.
Proof.
  intro.
  elim (BoolVal b); intro; rewrite H.
  rewrite NotTrue.
  rewrite NotFalse.
  reflexivity.
  rewrite NotFalse.
  rewrite NotTrue.
  reflexivity.
Qed.

Lemma lema4_2 : forall b1 b2 : Bool, Not (Or b1 b2) = And (Not b1) (Not b2).
Proof.
  intros.
  elim (BoolVal b1); intro; rewrite H.
  rewrite OrTrue.
  rewrite NotTrue.
  rewrite AndFalse.
  reflexivity.
  rewrite OrFalse.
  rewrite NotFalse.
  rewrite AndTrue.
  reflexivity.
Qed.

Lemma lema4_3 : forall b1 : Bool, exists b2 : Bool, Or b1 b2 = Or (Not b1) (Not b2).
Proof.
  intro.
  exists (Not b1).
  elim (BoolVal b1); intro; rewrite H.
  rewrite NotTrue.
  rewrite NotFalse.
  rewrite OrFalse.
  rewrite OrTrue.
  reflexivity.
  rewrite OrFalse.
  rewrite NotFalse.
  rewrite OrTrue.
  reflexivity.
Qed.

End Ej4.



Section Ej5.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall X : Set, Matrix X 0.
Parameter addM   : forall (X : Set) (n: nat), 
                   Matrix X n -> Array X (S n) -> Matrix X (S n). (* agrega filas *)

(* Defs auxiliares: *)

Definition ar1 : Array nat 1 := addA nat 0 1 (emptyA nat).
Definition ar2 : Array nat 2 := addA nat 1 1 (addA nat 0 2 (emptyA nat)).
Definition ar3 : Array nat 3 := addA nat 2 3 (addA nat 1 2 (addA nat 0 1 (emptyA nat))).

Definition M1 : Matrix nat 1 := addM nat 0 (emptyM nat) ar1.
Definition M2 : Matrix nat 2 := addM nat 1 M1 ar2.
Definition M3 : Matrix nat 3 := addM nat 2 M2 ar3.

(* 5.c *)
Definition ej5c : Matrix nat 3 := M3.

End Ej5.