Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Hypothesis H1: forall x:U, (R x x).
Hypothesis H2: forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Theorem reflexiva: (forall x:U, (R x x)).
Proof.
  intros.
  apply (H1 x).
Qed.

Theorem simetrica: (forall x y:U, (R x y) -> (R y x)).
Proof.
  intros.
  apply (H2 x y x).
  split.
  assumption.
  apply (H1 x).
Qed.

Theorem transitiva: (forall x y z:U, (R x y) /\ (R y z) -> (R x z)).

Proof.
  
  intros.
  apply (H2 y x z).
  split.
  apply (simetrica x y).
  elim H.
  intros.
  assumption.
  elim H.
  intros.
  assumption.
Qed.
End Ejercicio3.


Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
  intros.
  exists x.
  intro;assumption.
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
  exists a;intros.
  exists a.
  apply (H0 a).
  assumption.
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
  intros.
  exists (S a).
  apply (H0 a).
  assumption.
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
  intros.
  exists (S a).
  apply (H (S a)).
  split.
  assumption.
  apply (H0 a).
  assumption.  
Qed.

End Ejercicio5.


Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intro; split; intros; apply (H x).  
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  intro; elim H; intros; elim H0; intros; [left|right]; exists x; assumption.  
Qed.

End Ejercicio7.


Section Ejercicio8.
Variable U   : Set.
Variable T V : U -> Prop.
Variable R   : U -> U -> Prop.

Theorem e81: (exists y:U, forall x:U, R x y) 
                      -> (forall x:U, exists y:U, R x y).
Proof.
  intros.
  elim H.
  intros.
  exists x0.
  apply (H0 x).
Qed.


Theorem T282: (exists y:U, True) /\ (forall x:U, (T x) \/ (V x)) 
                          -> (exists z:U, (T z)) \/ (exists w:U, (V w)).
Proof.
  intro.
  elim H.
  intros.
  elim H0.
  intros.
  assert (T x \/ V x).
  apply (H1 x).
  elim H3; intro; [left | right]; exists x; assumption. 
Qed.

(* La condición (exists y:U, True) es necesaria para la prueba del teorema
   anterior, ya que necesito que exista al menos un elemento x de tipo U.
   Para probar el consecuente:  (exists z:U, (T z)) \/ (exists w:U, (V w))
   es necesario encontrar un testigo para al menos uno de los 2 lados de 
   la disjunción. De no tener la condición mencionada anteriormente, no 
   podré encontrar dicho testigo, y por ende no seguirá siendo cierto para
   cualquier tipo U (si no hay elementos de tipo U la proposición será falsa).
*)

End Ejercicio8.


Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  intros.
  elim(classic(A x));intro.
  assumption.
  unfold not in H.
  elim H.
  exists x.
  intro.
  absurd (A x);assumption.
Qed.

Theorem contrarreciproco: forall x y: Prop, (~y -> ~x) -> (x -> y).
Proof.
  intros.
  elim(classic y); intro.
  assumption.
  absurd x; [apply H|];assumption.
Qed.

Theorem doble_negacion: forall x : Prop, x -> ~~x.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
  apply (contrarreciproco (~forall x :U, A x) (exists x:U,  ~A x)).
  intro.
  apply (doble_negacion (forall x:U, A x)).
  apply not_ex_not_forall.
  assumption.  
Qed.

End Ejercicio9.


Section Ejercicio10y11.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.

Variable sum prod : nat->nat->nat.
Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

(* Ej. 10 *)

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  rewrite -> (sumS (S O) O).
  rewrite -> (sum0 (S O)).
  reflexivity.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  unfold not.
  intros.
  elim H; intros.
  elim H1; intros.  
  apply (disc x).
  rewrite -> H0.
  assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  intro.
  rewrite -> (prodS n O).
  rewrite -> (prod0 n).
  rewrite -> (sum0 n).
  reflexivity.
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  intro.
  unfold not.
  intro.
  elim (disc n). 
  symmetry.
  apply (inj).
  assumption.
Qed.

(* Principio de inducción *)
Axiom induction: forall n:nat, forall P : nat -> Prop,
                              (P O) /\ (forall k: nat, P k -> P (S k)) -> P n.

(* Ej. 11 *)

Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
  unfold not.  
  intros.
  elim (leinv (S n) O); intros.
  apply (disc n).
  symmetry.
  assumption.
  elim H0.
  intros.
  elim H1.
  intros.
  apply (disc x0).
  apply H2.
  assumption.  
Qed.

End Ejercicio10y11.
