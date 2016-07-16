Section Ejercicio3.
Variable A B C: Set.


Definition aplai: (A->B)->A->B.
Proof.
exact(fun f x => f x).
Defined.

Definition composishon: (A->B)->(B->C)->(A->C).
Proof.
exact(fun f g => (fun x => g (f x))).
Defined.

Definition tuais: (A->A)->A->A.
Proof.
exact(fun f x => f (f x)).
Defined.



Definition aplai2: forall A B:Set,(A->B)->A->B.
Proof.
  exact(fun A B (f:A->B) (x:A) => f x).
Defined.

Definition composishon2: forall A B C:Set,(A->B)->(B->C)->(A->C).
Proof.
  exact(fun A B C f g => (fun x => g (f x))).
Defined.

Definition tuais2: forall A:Set,(A->A)->A->A.
Proof.
  exact(fun A f => composishon2 A A A f f).
Defined.

End Ejercicio3.

Section Ejercicio5.
Variable A B C: Set.

(* 5.1 *)
Definition opI : forall A:Set, A->A
             := fun A x => x.

Definition opK : forall A B:Set, A -> B -> A
             := fun A B a b => a.

Definition opS : forall A B C:Set, (A -> B -> C) -> (A -> B) -> A -> C
             := fun A B C (x:A->B->C) (y:A->B) (z: A) => x z (y z).

(* 5.2 *)
Lemma e52 : forall A B : Set, forall x:A, opS A (B->A) A (opK A (B->A)) (opK A B) = opI A.
Proof.
  cbv.
  reflexivity.
Qed.

End Ejercicio5.

Section Ejercicio7.
(* 7.1 *)
Definition Bool := forall X:Set, X -> X -> X.
Definition t : Bool := fun (X:Set) (x:X) (y:X) => x.
Definition f : Bool := fun (X:Set) (x:X) (y:X) => y. 

(* 7.2 *)
Definition If (if2 then2 else2 : Bool) : Bool 
              := fun (X:Set) (x:X) (y:X) => if2 (X:Set) (then2 (X:Set) (x:X) (y:X)) (else2 (X:Set) (x:X) (y:X)).

(* 7.3 *)
Definition Not (b:Bool) : Bool
               := If b f t. 

Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.
  split; cbv;  reflexivity.
Qed.

(* 7.4 *)
Definition And (b1: Bool) (b2: Bool) : Bool
               := If b1 b2 f. 

Definition And' (b1: Bool) (b2: Bool) :Bool
                := If b2 b1 f.

(* 7.5 *)
Infix "&" := And (left associativity, at level 93).

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.
split;[|split];trivial.
Qed.

End Ejercicio7.

(* Ejercicio8 *)
Section ArrayNat.
Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)
Check(add 0 (S 0) empty).

(* 8.2 *)
(* Vector de ceros de largo 2 *)
Check(add 1 0 (add 0 0 empty)).

(* Vector [0,1,0,1] de largo 4 *)
Check(add 3 0 (add 2 1 (add 1 0 (add 0 1 empty)))).

(* 8.3 *)
Parameter Concat : forall n m :nat, ArrayNat n -> ArrayNat m -> ArrayNat (n+m).

(* 8.4 *)
Parameter Zip : forall n:nat, ArrayNat n -> ArrayNat n -> (nat->nat->nat) -> ArrayNat n.

(* 8.5 *)
Check(ArrayNat).

(* 8.6 *)
Parameter Array  : forall (X:Set) (n:nat), Set.
Parameter empty' : forall (X:Set), Array X 0.
Parameter add'   : forall (X:Set) (n:nat), X -> Array X n -> Array X (n + 1).
Parameter Zip'   : forall (X Y Z:Set) (n:nat), Array X n -> Array Y n -> (X->Y->Z) -> Array Z n.

(* 8.7 *)
Parameter ArrayBool : forall n:nat, Array bool n. 

End ArrayNat.

Section Ejercicio11.
Parameter AVLNat   : forall n : nat, Set.

(* 11.1 *)
Parameter emptyAVL : AVLNat 0.

(* 11.2 *)
Parameter addAVL1  : forall n : nat, nat -> AVLNat n -> AVLNat n -> AVLNat (n+1).
Parameter addAVL2  : forall n : nat, nat -> AVLNat (n+1) -> AVLNat n -> AVLNat (n+2).
Parameter addAVL3  : forall n : nat, nat -> AVLNat n -> AVLNat (n+1) -> AVLNat (n+2).

(* 11.3 *)
Check( addAVL1 1 4 (addAVL1 0 3 emptyAVL emptyAVL) (addAVL1 0 1 emptyAVL emptyAVL)).

(* 11.4 *)
Parameter AVL       : forall (X:Set) (n:nat), Set.
Parameter emptyAVL' : forall (X:Set), AVL X 0.
Parameter addAVL1'  : forall (X:Set) (n:nat), X -> AVL X n -> AVL X n -> AVL X (n+1).
Parameter addAVL2'  : forall (X:Set) (n:nat), X -> AVL X (n+1) -> AVL X n -> AVL X (n+2).
Parameter addAVL3'  : forall (X:Set) (n:nat), X -> AVL X n -> AVL X (n+1) -> AVL X (n+2).

End Ejercicio11.


Section Ejercicio13.
Variable A B C: Prop.

Lemma Ej313_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
  exact(g a).
Qed.

Lemma Ej313_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
  exact(H0 H).
Qed.

Lemma Ej313_3 : (A -> B -> C) -> A -> B -> C.
Proof.
  exact(fun f a b => f a b).
Qed.

Lemma Ej313_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact(H2 (H H1)).
Qed.

End Ejercicio13.


Section Ejercicio14.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej314_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
  exact(H x (H0 x)).
Qed.

Lemma Ej314_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact(H0 x H).
Qed.

Lemma Ej314_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  intros.
  exact(H x H0).
Qed.

Lemma Ej314_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact(fun f x => f x x).
Qed.

Lemma Ej314_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
  exact(fun f => f e).
Qed.

End Ejercicio14.
