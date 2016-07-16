(* Practica 1 *)

Section P1.
Variables A B C : Prop.

(* Ejercicio 1.1 *)
Theorem e11 : A->A.
Proof.
  intro H.
  assumption.
Qed.

(* Ejercicio 1.2 *)
Theorem e12 : A->B->A.
Proof.
  intro H.
  intro H0.
  assumption.
Qed.

(* Ejercicio 1.3 *)
Theorem e13 : (A->(B->C))->(A->B)->(A->C).
Proof.
  intros.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.



(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.


(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

(*Ej 3.1 *)
(* Prueba 1 *)
Theorem e31: A->A->A.
Proof.
  intros.
  assumption.
Qed.

(* Prueba 2 *)
Theorem e31b: A->A->A.
Proof.
  intro f.
  intro g.
  exact g.
Qed.

(* Ej 3.2 *)
(* Prueba 1 *)
Theorem e32: (A->B->C)->A->(A->C)->B->C.
Proof.
  intros.
  apply H1.
  assumption.
Qed.

(* Prueba 2 *)
Theorem e32b: (A->B->C)->A->(A->C)->B->C.
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.


(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
  intro.
  unfold not.
  intro.
  apply H0.
  assumption.
Qed.


(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
  intros.
  split.
  assumption.
  assumption.
Qed.


(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
  intros.
  apply H.
  (* Esta parte es para la primera prueba: *)
  elim H0.
  intros.
  assumption.

  (* Esta parte es para la segunda prueba: *)
  elim H0.
  intros.
  assumption.
Qed.


(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
  intro.
  left.
  assumption.
Qed.


(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
  intro.
  right.
  assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
  intro.
  elim H.
  (* Esta parte es para la primera prueba: *)
  intro.
  right.
  assumption.

  (* Esta parte es para la segunda prueba: *)
  intro.
  left.
  assumption.
Qed.


(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
  intros.
  elim H1.
  assumption.
  assumption.
Qed.


(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
  intro.
  elim H.
Qed.


(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
  intro f.
  intro g.
  intro a.
  unfold not in *.
  apply g.
  apply f.
  assumption.
Qed.


(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
  unfold not.
  intro.
  absurd A.

  (* Esta parte es para la primera prueba: *)
  elim H.
  intros.
  unfold not.
  assumption.

  (* Esta parte es para la segunda prueba: *)
  elim H.
  intros.
  assumption.
Qed.


(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
  intro.
  unfold not.
  intro.
  elim H0.
  intros.
  apply H2.
  apply H.
  assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
  intro.
  unfold not.
  intro.
  absurd B.
  (* Esta parte es para la primera prueba: *)
  unfold not.
  apply H0.
  elim H.
  intros.
  assumption.

  (* Esta parte es para la segunda prueba: *)
  elim H.
  intros.
  assumption.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
  intro.
  absurd A.

  (* Esta parte es para la primera prueba: *)
  elim H.
  intros.
  assumption.

  (* Esta parte es para la segunda prueba: *)
  elim H.
  intros.
  cut False.
  intro.
  elim H2.

  (* Esta parte es para la tercera prueba: *)
  absurd (~A); assumption.
Qed.


(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
  intro.
  unfold not.
  intro.
  elim H0.
  intros.
  elim H; assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
  unfold iff.
  split; intro.
  elim H.
  intro.
  right.
  assumption.

  (* Esta parte es para la primera prueba: *)
  elim H; intros; [right | left]; assumption.

  (* Esta parte es para la segunda prueba: *)
  elim H.
  intros.
  right.
  assumption.

  elim H; intros; [right | left]; assumption.
Qed.


(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
  intros.
  elim H.
  assumption.
  intro.
  assumption.
Qed.

End P1.



Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
  intros.
  elim H.
  intro.
  assumption.
  intro.
  absurd (~A); assumption.  
Qed.


(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
  intro.
  elim H.
  intro.
  right.
  intro.
  assumption.

  intro.
  left.
  intro.
  absurd A; assumption.
Qed.

(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros.
  unfold not in H0.
  elim H.
  intro.
  right.
  unfold not in *.
  intro.
  elim H0.
  split; assumption.

  intro.
  left.
  assumption.
Qed.


Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: ~~A->A.
Proof.
  apply e71.
  exact (classic A).

(* Otra forma:
  intro.
  elim (classic A).
  intro.
  assumption.
  intro.
  absurd (~A); assumption. *)

Qed.
Print e81.

(* Ej 8.2 *)
Theorem e82: (A->B)\/(B ->A).
Proof.
  apply e72.
  exact (classic A).

(* Otra forma:
  elim (classic B).
  intro.
  left.
  intro. 
  assumption.
  
  intro.
  right.
  intro.
  absurd B; assumption. *)
Qed.

(* Ej 8.3 *)
Theorem e83: ~(A/\B)-> ~A \/ ~B.
Proof.
  apply e73.
  exact (classic A).
Qed.

End Logica_Clasica.




Section ejercicio11.

(* Ej 11 *)
(* Definiciones *)
Variable PF:Prop. (*el paciente tiene fiebre*)
Variable PA:Prop. (*el paciente tiene piel amarillenta*)
Variable PH:Prop. (*el paciente tiene hepatitis*)
Variable PR:Prop. (*el paciente tiene rubeola*)

Hypothesis Regla1: PF \/ PA -> PH \/ PR.
Hypothesis Regla2: PR -> PF.
Hypothesis Regla3: PH /\ ~PR -> PA.


Theorem hola : PH -> PH \/ PR.
Proof.
  intro.
  left.
  assumption.
Qed.

Theorem ej11: (~PA /\ PF) -> PR.
Proof.
  intro.
  elim(classic PR).

(*Caso 1*)
  intro.
  assumption.


(*Caso 2*)
  intro.
  absurd (PA).
  apply H.
  apply Regla3.
  split.

  cut(PH \/ PR).
  intro.
  elim H1.
  intro.
  assumption.
  intro.
  absurd PR.
  assumption.
  assumption.
  apply Regla1.
  left.
  apply H.
  assumption.

Qed.

End ejercicio11.