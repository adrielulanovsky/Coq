(*Practica 4*)

Section Ejercicio1.

(*Ejercicio 1*)
(* 1.1 *)
Inductive list (A:Set) : Set :=
                nil : list A
              | cons : A -> list A -> list A.

Inductive bintree (A:Set) : Set :=
                nilB : bintree A
              | consB : A -> bintree A -> bintree A -> bintree A.

(* 1.2 *)
Inductive Array (A:Set) : nat -> Set :=
                nilA : Array A 0
              | consA : forall n:nat, A -> Array A n -> Array A (n+1).

Inductive Matrix (A:Set) : nat -> nat -> Set :=
   oneF : forall n:nat, Array A (n+1) -> Matrix A 1 (n+1)
 | consMf : forall (m n:nat), Array A n -> Matrix A m n -> Matrix A (m+1) n.

(* 1.3 *)
Inductive leq : nat -> nat -> Prop := 
   leqI : forall n:nat, leq n n
 | leqS : forall (m n:nat), leq m n -> leq m (S n).

(* 1.4 *)
Inductive eq_list (A:Set) (P:A->A->Prop) : list A -> list A -> Prop :=
   eqEmpty : eq_list A P (nil A) (nil A)
 | eqOther : forall (xs ys:list A) (x y: A), P x y -> eq_list A P xs ys
                        -> eq_list A P (cons A x xs) (cons A y ys).

(* 1.5 *)
Inductive sorted (A:Set) (R:A->A->Prop) : list A -> Prop :=
   sortEmpty : sorted A R (nil A)
 | sortOne : forall x:A, sorted A R (cons A x (nil A))
 | sortMore : forall (xs: list A) (x y:A), R x y -> sorted A R xs
                       -> sorted A R (cons A x (cons A y xs)).

(* 1.6 *)
Inductive mirror (A:Set) : bintree A -> bintree A -> Prop :=
   mirrNil : mirror A (nilB A) (nilB A)
 | mirrCons : forall (t1 t2 t3 t4 : bintree A) (x y : A),
                    mirror A t1 t4 -> mirror A t2 t3
                       -> mirror A (consB A x t1 t2) (consB A y t3 t4).

(* 1.7 *)
Inductive isomorfo (A B:Set) : bintree A -> bintree B -> Prop :=
   isoNil : isomorfo A B (nilB A) (nilB B)
 | isoCons : forall (t1 t2 : bintree A) (t3 t4 : bintree B) (x : A) (y : B),
                  isomorfo A B t1 t3 -> isomorfo A B t2 t4
                       -> isomorfo A B (consB A x t1 t2) (consB B y t3 t4).

(* 1.8 *)
Inductive Gtree (A B:Set) : Set :=
     node: A -> Gforest A B -> Gtree A B
   | hoja: B -> Gtree A B
with
  Gforest (A B:Set) : Set :=
             oneTree : Gtree A B -> Gforest A B
           | add_tree: Gtree A B -> Gforest A B -> Gforest A B.

End Ejercicio1.

Section Ejercicio2.

(* 2.1 *)
Fixpoint Or (a b: bool) : bool := match a with
                                        true => true
                                      | false => b
                                  end.

Fixpoint And (a b: bool) : bool := match a with
                                         true => b
                                       | false => false
                                   end.

Fixpoint Not (a: bool) : bool := match a with
                                       true => false
                                     | _ => true
                                 end.

Fixpoint Xor (a b: bool) : bool := match a with
                                         false => b
                                       | true => Not b
                                   end.

(* 2.2 *)

Fixpoint is_nil (A:Set) (xs : list A) : bool :=
  match xs with
        nil => true                                    
      | cons y ys => false
  end.

End Ejercicio2.

Section Ejercicio3.

Fixpoint Sum (a b :nat) {struct b} :nat :=
  match b with
        0   => a                                    
      | S k => S (Sum a k)
  end.

Fixpoint Prod (a b :nat) : nat :=
  match a with
        0   => 0                                   
      | S k => (Sum (Prod k b) b)
  end.

Fixpoint Pot (a b: nat) : nat :=
  match b with
        0   => 1
      | S k => Prod a (Pot a k)
  end.

Fixpoint leBool (a b : nat) : bool :=
  match a, b with
        0, _     => true
      | S k, 0   => false
      | S k, S j => leBool k j 
  end.

End Ejercicio3.

Section Ejercicio4.

Fixpoint length (A:Set) (xs : list A) : nat :=
  match xs with
        nil => 0
      | cons y ys => S (length A ys)
  end.

Fixpoint append (A:Set) (xs ys : list A) : list A :=
  match xs with
        nil => ys
      | cons z zs => cons A z (append A zs ys)
  end.

Fixpoint reverse (A:Set) (xs : list A) : list A :=
  match xs with
        nil => nil A
      | cons z zs => append A (reverse A zs) (cons A z (nil A))
  end.

Fixpoint filter (A:Set) (f : A -> bool) (xs : list A) : list A :=
  match xs with
        nil => nil A
      | cons z zs => match f z with
                           true => cons A z (filter A f zs)
                         | _    => filter A f zs
                     end
  end.

Fixpoint map (A B:Set) (f : A -> B) (xs : list A) : list B :=
  match xs with
        nil => nil B
      | cons z zs => cons B (f z) (map A B f zs)
  end.

Fixpoint exists_ (A:Set) (f : A -> bool) (xs : list A) : bool :=
  match xs with
        nil => false
      | cons z zs => match f z with
                           true  => true
                         | false => exists_ A f zs
                     end
  end.

End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Fixpoint inverse (A:Set) (t : bintree A) : bintree A := 
  match t with
        nilB => nilB A
      | consB x t1 t2 => consB A x (inverse A t2) (inverse A t1)
  end.

(* 5.2 *)
(* Funciones auxiliares *)
Fixpoint nodosInternosT (A B:Set) (t: Gtree A B) : nat := 
  match t with
        hoja x    => 0
      | node x ft => S (nodosInternosF A B ft)
  end
with
  nodosInternosF (A B:Set) (f: Gforest A B) : nat := 
    match f with
          oneTree t     => nodosInternosT A B t
        | add_tree t ft => (nodosInternosT A B t) + (nodosInternosF A B ft)
    end.

Fixpoint nodosExternosT (A B:Set) (t: Gtree A B) : nat := 
  match t with
        hoja x    => 1
      | node x ft => nodosExternosF A B ft
  end
with
  nodosExternosF (A B:Set) (f: Gforest A B) : nat := 
    match f with
          oneTree t     => nodosExternosT A B t
        | add_tree t ft => (nodosExternosT A B t) + (nodosExternosF A B ft)
    end.

(* Función pedida *)
Fixpoint moreInternal (A B:Set) (t : Gtree A B) : bool := 
  leBool (nodosExternosT A B t) (nodosInternosT A B t).

End Ejercicio5.


Section Ejercicio6.

Definition ListN : Set := list nat.

(*Función auxiliar*)
Fixpoint is_equal (x y:nat) : bool :=
  match x, y with
        0, 0 => true
      | 0, _ => false
      | _, 0 => false
      | S a, S b => is_equal a b
  end.

(*6.1*)
Fixpoint member (n:nat) (xs : ListN) : bool := 
  exists_ nat (is_equal n) xs.

(*6.2*)
Fixpoint delete (ls : ListN) (n : nat) : ListN :=
  match ls with
        nil => nil nat
      | cons x xs => match is_equal n x with
                           true  => delete xs n
                         | false => cons nat x (delete xs n)
                     end
  end.

(*6.3*)
Fixpoint insert (n:nat) (ls : ListN) : ListN :=
  match ls with
        nil => cons nat n (nil nat)
      | cons x xs => match leBool n x with
                           true  => cons nat n (cons nat x xs)
                         | false => cons nat x (insert n xs)
                     end
  end.

Fixpoint insert_sort (ls : ListN) : ListN :=
  match ls with
        nil => nil nat
      | cons x xs => insert x (insert_sort xs)
  end.



End Ejercicio6.


Section Ejercicio7.

Inductive Exp (A: Set) : Set :=
              atom     : A -> Exp A
            | SumExp   : Exp A -> Exp A -> Exp A
            | ProdExp  : Exp A -> Exp A -> Exp A
            | NegExp   : Exp A -> Exp A.

Fixpoint EvalExpNat (e : Exp nat) : nat :=
  match e with
        atom n        => n
      | SumExp e1 e2  => (EvalExpNat e1) + (EvalExpNat e2)
      | ProdExp e1 e2 => (EvalExpNat e1) * (EvalExpNat e2)
      | NegExp e1     => 0 - (EvalExpNat e1)
  end.

Fixpoint EvalExpBool (e : Exp bool) : bool :=
  match e with
        atom b        => b
      | SumExp e1 e2  => Or (EvalExpBool e1) (EvalExpBool e2)
      | ProdExp e1 e2 => And (EvalExpBool e1) (EvalExpBool e2)
      | NegExp e1     => Not (EvalExpBool e1)
  end.

End Ejercicio7.


Section Ejercicio8.

Lemma AsocAnd : forall a b c: bool, And (And a b) c = And a (And b c).
Proof.
  intros.
  case a, b, c; trivial.
Qed.

Lemma AsocOr : forall a b c: bool, Or (Or a b) c = Or a (Or b c).
Proof.
  case a, b, c; trivial.
Qed.

Lemma ConmutAnd : forall a b: bool, And a b = And b a.
Proof.
  case a, b; trivial.
Qed.

Lemma ConmutOr : forall a b: bool, Or a b = Or b a.
Proof.
  case a, b; trivial.
Qed.

Lemma LAnd : forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
  unfold iff.
  split; intro.
  split;trivial.
  induction a; trivial.
  induction b; trivial.
  elim H.
  case a; trivial.
  elim H; intros.
  rewrite -> H0.
  rewrite -> H1.
  trivial.
Qed.

Lemma LOr1 : forall a b : bool, Or a b = false <-> a = false /\ b = false.
Proof.
  unfold iff.
  split; intro.
  split.
  destruct a; trivial.
  destruct a. 
  discriminate.
  trivial.
  elim H; intros.
  rewrite -> H0.
  rewrite -> H1.
  trivial.
Qed.

Lemma LOr2 : forall a b : bool, Or a b = true <-> a = true \/ b = true.
Proof.
  unfold iff.
  split; intro.
  destruct a, b.
  left; trivial.
  left; trivial.
  right; trivial.
  right; trivial.
  elim H; intro; rewrite -> H0.
  trivial.
  case a; trivial.
Qed.

Lemma LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.
  unfold iff.
  split; unfold not; intros; destruct a; simpl.
  rewrite <- H0 in H; discriminate.
  rewrite <- H0 in H; discriminate.
  destruct b; simpl; [elim H|]; trivial.
  destruct b.
  trivial.
  elim H; trivial.
Qed.

Lemma LNot : forall b : bool, Not (Not b) = b.
Proof.
  destruct b; trivial.
Qed.


End Ejercicio8.

(*----------------------SE ENTREGA------------------------*)
(*Requiere Ej3 (Prod, Sum) *)
Section Ejercicio9.

(* 9.1 *)
Lemma SumO : forall n : nat, Sum n 0 = n.
Proof.
  constructor.
Qed.

(* 9.2 *)
Lemma SumS : forall n m : nat, Sum n (S m) = Sum (S n) m.
Proof.
  induction m; simpl.
  constructor.
  rewrite <- IHm.
  simpl.
  trivial.
Qed.

(* 9.3 *)
Lemma SumConm : forall n m : nat, Sum n m = Sum m n.
Proof.
  induction m; simpl.
  induction n; trivial.
  simpl.
  elim IHn.
  trivial.
  elim (SumS m n).
  simpl.
  elim IHm.
  trivial.
Qed.

(* 9.4 *)
Lemma SumAsoc : forall n m p : nat, Sum n (Sum m p) = Sum (Sum n m) p.
Proof.
  induction p; simpl.
  trivial.
  rewrite -> IHp.
  trivial.
Qed.

(* Lema Auxiliar *)
Lemma ProdS : forall n m : nat, Prod n (S m) = Sum (Prod n m) n.
Proof.
  intros.
  induction n; simpl.
  trivial.
  rewrite -> IHn.
  elim SumConm.
  apply f_equal.
  rewrite -> SumAsoc.
  replace (Sum m (Prod n m)) with (Sum (Prod n m) m).
  trivial.
  elim SumConm.
  trivial.
Qed.

(* 9.5 *)
Lemma ProdConm : forall n m : nat, Prod n m = Prod m n.
Proof.
  induction m; simpl.
  induction n; simpl.
  trivial.
  rewrite -> IHn.
  trivial.
  rewrite <- IHm.
  apply (ProdS n m).
Qed.

(* 9.7 *)
Lemma ProdDistr : forall n m p : nat, Prod n (Sum m p) = Sum (Prod n m) (Prod n p).
Proof.
  induction n; simpl.
  trivial.
  intros.
  rewrite -> IHn.
  rewrite -> SumAsoc.
  symmetry.
  rewrite -> SumAsoc.
  pattern (Sum (Sum (Prod n m) m) (Prod n p)).
  elim SumAsoc.
  pattern (Sum m (Prod n p)).
  elim SumConm.
  rewrite -> SumAsoc.
  trivial.
Qed.

(* 9.6 *)
Lemma ProdAsoc : forall n m p : nat, Prod n (Prod m p) = Prod (Prod n m) p.
Proof.
  intros. 
  induction n; simpl.
  trivial.
  rewrite -> IHn.
  symmetry.
  elim ProdConm.
  rewrite -> (ProdDistr p (Prod n m) m).
  elim ProdConm.
  rewrite -> (ProdConm p m).
  trivial.
Qed.

End Ejercicio9.
(*--------------------------------------------------------*)

(*----------------------SE ENTREGA------------------------*)
Section Ejercicio10.
(* 10.1 *)
(* 
Fixpoint append (A:Set) (xs ys : list A) : list A :=
  match xs with
        nil => ys
      | cons z zs => cons A z (append A zs ys)
  end.
*)

Lemma L1 : forall (A : Set) (l : list A), append A l (nil A) = l.
Proof.
  intros.
  induction l.
  trivial.
  simpl.
  rewrite -> IHl.
  trivial.
Qed.

(* 10.2 *)
Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A.
Proof.
  discriminate.
Qed.

(* 10.3 *)
Lemma L3 : forall (A : Set) (l m : list A) (a : A),
           cons A a (append A l m) = append A (cons A a l) m.
Proof.
  trivial.
Qed.

(* 10.4 *)
(*
Fixpoint length (A:Set) (xs : list A) : nat :=
  match xs with
        nil => 0
      | cons y ys => S (length A ys)
  end.
*)
Lemma L4 : forall (A : Set) (l m : list A),
           length A (append A l m) = Sum (length A l) (length A m).
Proof.
  intros.
  induction l.
  elim SumConm.
  simpl.
  trivial.
  simpl.
  rewrite -> IHl.
  elim SumS.
  simpl.
  trivial.
Qed.

(* 10.5 *)
Lemma L5 : forall (A : Set) (l : list A), length A (reverse A l) = length A l.
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite <- IHl.  
  rewrite -> L4.
  simpl.
  trivial.
Qed.

(* Lema auxiliar (Ojo, igual a L9) *)
Lemma L6Aux: forall (A : Set) (l m p: list A),
      append A l (append A m p) = append A (append A l m) p.
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite -> IHl.
  trivial.
Qed.

(* 10.6 *)
Lemma L6 : forall (A : Set) (l m : list A),
reverse A (append A l m) = append A (reverse A m) (reverse A l).
Proof.
  intros.
  induction l; simpl.
  rewrite -> L1.
  trivial.
  rewrite -> IHl.
  induction m; simpl.
  trivial.
  rewrite -> L6Aux.
  trivial.
Qed.

End Ejercicio10.
(*--------------------------------------------------------*)
(*----------------------SE ENTREGA------------------------*)
Section Ejercicio11.

(* 11.1 *)
Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
           map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite -> IHl.
  trivial.
Qed.

(* 11.2 *)
Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
           filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite -> IHl.
  case (P a); simpl; trivial.
Qed.

(* 11.3 *)
Lemma L9 : forall (A : Set) (l m n : list A),
                  append A l (append A m n) = append A (append A l m) n.
Proof.
  exact L6Aux.
Qed.

(* 11.4 *)
Lemma L10 : forall (A : Set) (l : list A), reverse A (reverse A l) = l.
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite -> L6.
  simpl.
  rewrite -> IHl.
  trivial.
Qed.

End Ejercicio11.
(*--------------------------------------------------------*)
(*----------------------SE ENTREGA------------------------*)
Section Ejercicio12.

Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)
         (l : list A) {struct l} : list B :=
         match l with
             | nil => nil B
             | cons a l1 => match P (f a) with
                                | true => cons B (f a) (filterMap A B P f l1)
                                | false => filterMap A B P f l1
                            end
         end.

Lemma FusionFilterMap :
      forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A),
      filter B P (map A B f l) = filterMap A B P f l.
Proof.
  intros.
  induction l; simpl.
  trivial.
  rewrite -> IHl.
  trivial.
Qed.

End Ejercicio12.
(*--------------------------------------------------------*)

Section Ejercicio13.

Lemma L11: forall (A : Set) (t : bintree A), mirror A t (inverse A t).
Proof.
  intros.
  induction t; simpl; constructor; assumption.
Qed.

End Ejercicio13.

Section Ejercicio14.

Print isomorfo.

Definition id_arbol (A : Set) (t : bintree A) : bintree A := t.

Lemma L12 : forall (A : Set) (t : bintree A), isomorfo A A (id_arbol A t) t.
Proof.
  intros.
  unfold id_arbol.
  induction t; constructor; assumption.
Qed.

Lemma isoReflexiva : forall (A : Set) (t : bintree A), isomorfo A A t t.
Proof.
  intros.
  replace (isomorfo A A t t) with (isomorfo A A (id_arbol A t) t).
  apply L12.
  unfold id_arbol.
  trivial.
Qed.

Lemma isoSimetrica : forall (A B : Set) (t1 : bintree A) (t2 : bintree B), 
                     isomorfo A B t1 t2 -> isomorfo B A t2 t1.
Proof.
  intros.
  elim H.
  constructor.
  intros.
  constructor; assumption.
Qed.

End Ejercicio14.

Section Ejercicio15.

Inductive Tree (A:Set) : Set :=
                nilT : A -> Tree A
              | consT : Tree A -> Tree A -> Tree A.

Fixpoint mapTree (A B:Set) (f : A -> B) (t : Tree A) : Tree B :=
  match t with
        nilT a => nilT B (f a)
      | consT t1 t2 => consT B (mapTree A B f t1) (mapTree A B f t2)
  end.

Fixpoint countTree (A : Set) (t : Tree A) : nat :=
  match t with
        nilT a => 1
      | consT t1 t2 => Sum (countTree A t1) (countTree A t2)
  end.

Lemma L13 : forall (A B: Set) (f : A -> B) (t : Tree A),
            countTree B (mapTree A B f t) = countTree A t.
Proof.
  intros.
  induction t; simpl.
  trivial.
  rewrite -> IHt1.
  rewrite -> IHt2.
  trivial.
Qed.

Fixpoint hojasTree (A : Set) (t: Tree A) : list A :=
  match t with
        nilT a => cons A a (nil A) 
      | consT t1 t2 => append A (hojasTree A t1) (hojasTree A t2)
  end.

Lemma L14 : forall (A : Set) (t : Tree A),
            length A (hojasTree A t) = countTree A t.
Proof.
  intros.
  induction t; simpl.
  trivial.
  rewrite -> L4.
  rewrite -> IHt1.
  rewrite -> IHt2.
  trivial.
Qed.

End Ejercicio15.


(*----------------------SE ENTREGA------------------------*)
Section Ejercicio16.

(* Set Implicit Arguments *)

Variable A : Set.

Inductive posfijo : list A -> list A -> Prop :=
   pos1 : forall (l : list A), posfijo l l
 | pos2 : forall (a:A) (l1 l2 : list A),
          posfijo l1 l2 -> posfijo l1 (cons A a l2).

Infix "<<" := posfijo (at level 2).
Infix "+++" := (append A) (at level 1).
(*
No puedo hacerla infija porque requiere 3 argumentos
Infix "++" :=  append.
Infix "<<" := posfijo (at level 93).
*)
Lemma L15 : forall (l1 l2 l3 : list A),
            l2 = l3 +++ l1 -> l1 << l2.
Proof.
  intros.
  rewrite H.
  clear H.         (* Si no pongo esto, me cambia la hipótesis inductiva *)
  induction l3; simpl.
  constructor.
  constructor.
  assumption.
Qed.

Lemma L16 : forall (l2 l1 : list A), posfijo l1 l2 -> 
            exists l3 : list A, l2 = append A l3 l1.
Proof.
  intros.
  induction H; simpl.
  exists (nil A).
  simpl.
  trivial.
  elim IHposfijo.
  intros.
  exists (cons A a x).
  simpl.
  rewrite <- H0.
  trivial.
Qed.

Fixpoint ultimo (l : list A) : list A :=
  match l with
        nil => nil A
      | cons a nil => cons A a (nil A)
      | cons a xs => ultimo xs
  end.

Lemma L17 : forall (l : list A), (ultimo l) << l.
Proof.
  intros.
  induction l.
  simpl.
  constructor.
  destruct l; constructor.
  assumption.
(*
  intros.
  induction l.
  simpl.
  constructor.
  destruct l.
  simpl.
  constructor.

  replace (ultimo (cons A a (cons A a0 l))) with (ultimo (cons A a0 l)).
  constructor.
  assumption.
  simpl.
  trivial. *)
Qed.

End Ejercicio16.
(*--------------------------------------------------------*)

Section Ejercicio17.

Inductive ABin (A B : Set) : Set :=
                nilAB  : B -> ABin A B
              | consAB : A -> ABin A B -> ABin A B -> ABin A B.

Fixpoint countExternal (A B : Set) (t : ABin A B) : nat :=
  match t with
        nilAB b => 1
      | consAB a t1 t2 => Sum (countExternal A B t1) (countExternal A B t2)
  end.

Fixpoint countInternal (A B : Set) (t : ABin A B) : nat :=
  match t with
        nilAB b => 0
      | consAB a t1 t2 => S (Sum (countInternal A B t1) (countInternal A B t2))
  end.

Lemma L18 : forall (A B : Set) (t : ABin A B), 
            countExternal A B t = 1 + countInternal A B t.
Proof.
  induction t; simpl.
  trivial.
  rewrite IHt1.
  rewrite IHt2.
  elim SumS.
  simpl.
  trivial.
Qed.

End Ejercicio17.


(*----------------------SE ENTREGA------------------------*)
Section Ejercicio18.

Variable A : Set.

Inductive Tree_ : Set :=
  | nullTT : Tree_
  | consTT : A -> Tree_ -> Tree_ -> Tree_ .

Inductive isSubtree : Tree_ -> Tree_ -> Prop :=
  | isSub1 : forall t : Tree_ , isSubtree t t
  | isSub2 : forall (a : A) (t1 t2 t3 : Tree_), 
             isSubtree t1 t2 -> isSubtree t1 (consTT a t2 t3)  
  | isSub3 : forall (a : A) (t1 t2 t3 : Tree_), 
             isSubtree t1 t3 -> isSubtree t1 (consTT a t2 t3).


Lemma L19 : forall t : Tree_, isSubtree t t.
Proof.
  constructor.
Qed.

Lemma L20 : forall t1 t2 t3 : Tree_,
            isSubtree t1 t2 /\ isSubtree t2 t3 -> isSubtree t1 t3.
Proof.
  intros.
  elim H; intros; clear H.
  induction H1.
  assumption.

  apply isSub2.
  apply IHisSubtree.
  assumption.

  apply isSub3.
  apply IHisSubtree.
  assumption.
Qed.

End Ejercicio18.
(*--------------------------------------------------------*)

(*----------------------SE ENTREGA------------------------*)
Section Ejercicio19.

Variable A : Set.

Inductive ACom : nat -> Set :=
  | hojaCom : A -> ACom 0
  | consCom : forall n : nat, A -> ACom n -> ACom n -> ACom (S n).

Fixpoint cantHojasACom (n:nat) (t : ACom n) : nat :=
  match t with
        hojaCom a => 1
      | consCom p a t1 t2 => 
          Sum (cantHojasACom p t1) (cantHojasACom p t2)
  end.

Parameter pot: nat -> nat -> nat.

(* n^0 = 1, n>0 *)
Axiom potO : forall n : nat, pot (S n) 0 = 1. 

(* 2^(m+1) = 2^m + 2^m *)
Axiom potS : forall m: nat, pot 2 (S m) = Sum (pot 2 m) (pot 2 m).

Lemma L21 : forall (n : nat) (t : ACom n), cantHojasACom n t = pot 2 n. 
Proof.
  induction t; simpl.
  rewrite -> potO.
  trivial.
  rewrite -> IHt1.
  rewrite -> IHt2.
  rewrite -> potS.
  trivial.
Qed.

End Ejercicio19.
(*--------------------------------------------------------*)

(*----------------------SE ENTREGA------------------------*)
Section Ejercicio20.


(* Funciones auxiliares *)
Fixpoint GeBool (m n : nat) {struct n} : bool :=
  match n with
    | O => true
    | S k => match m with
                 | O => false
                 | S k2 => GeBool k2 k
                   end
  end.

Fixpoint Max (m n : nat) : nat :=
  match GeBool m n with
    | true => m
    | false => n
  end.
(* ------------------- *)

Inductive AB (A:Set) : nat -> Set :=
                nullAB : AB A 0
              | constAB : forall (m n : nat), A -> AB A m -> AB A n -> AB A (S (Max m n)).

Fixpoint camino (A: Set) (n: nat) (t : AB A n) : list A :=
  match t with
        nullAB => nil A
      | constAB n1 n2 a t1 t2 => match (GeBool n1 n2) with
                                       true => cons A a (camino A n1 t1)
                                     | false => cons A a (camino A n2 t2)
                                 end
  end.

Lemma AuxIfLength : forall (c : bool) (A:Set) (l1 l2 : list A),
      length A (if c then l1 else l2) = if c then length A l1 else length A l2.
Proof.
  induction c; trivial.
Qed.

Lemma CaminoN : forall (A: Set) (n : nat) (t : AB A n), 
                length A (camino A n t) = n.
Proof.
  induction t; simpl.
  trivial.
  rewrite AuxIfLength.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  destruct m; destruct n; simpl; trivial.
  case (GeBool m n); trivial.
Qed.

End Ejercicio20.
(*--------------------------------------------------------*)
