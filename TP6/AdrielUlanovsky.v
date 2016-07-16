Extraction Language Haskell.

Section Ej3.

Definition Value := bool.
Inductive BoolExpr : Set :=
  | bbool : bool -> BoolExpr
  | or : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.
Inductive BEval : BoolExpr -> Value -> Prop :=
  | ebool : forall b : bool, BEval (bbool b) (b:Value)
  | eorl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval (or e1 e2) true
  | eorr : forall e1 e2 : BoolExpr, BEval e2 true -> BEval (or e1 e2) true
  | eorrl : forall e1 e2 : BoolExpr,
            BEval e1 false -> BEval e2 false -> BEval (or e1 e2) false
  | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
  | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval (e : BoolExpr) {struct e} : Value :=
  match e with
  | bbool b => b
  | or e1 e2 =>
    match beval e1, beval e2 with
        | false, false => false
        | _, _ => true
    end
  | bnot e1 => if beval e1 then false else true
  end.

Fixpoint sbeval (e : BoolExpr) {struct e} : Value :=
  match e with
  | bbool b => b
  | or e1 e2 => match sbeval e1 with
            | true => true
            | _ => sbeval e2
            end
  | bnot e1 => if sbeval e1 then false else true
  end.

Lemma bevalCorrect : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (beval e).
  induction e; simpl.
    
    constructor.

    case_eq (beval e1); intro.
      
      constructor.
      rewrite <- H.
      assumption.
  
      case_eq (beval e2); intro.

        apply eorr.
        rewrite <- H0.
        assumption.
        
        apply eorrl; [rewrite <- H | rewrite <- H0]; assumption.
    
    case_eq (beval e); intro; constructor; rewrite <- H; assumption.
Defined.

Lemma sbevalCorrect : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (sbeval e).
  induction e; simpl.
    
    constructor.

    case_eq (sbeval e1); intro.
      
      constructor.
      rewrite <- H.
      assumption.
  
      case_eq (sbeval e2); intro.

        apply eorr.
        rewrite <- H0.
        assumption.
        
        apply eorrl; [rewrite <- H | rewrite <- H0]; assumption.
    
    case_eq (sbeval e); intro; constructor; rewrite <- H; assumption.
Defined.

Hint Constructors BEval.

Lemma bevalCorrect2 : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (beval e).
  induction e; simpl.
    
    auto.

    case_eq (beval e1); intro.

      constructor.
      rewrite <- H.
      assumption.
  
      case_eq (beval e2); intro.

        apply eorr.
        rewrite <- H0.
        assumption.
        
        apply eorrl; [rewrite <- H | rewrite <- H0]; assumption.
    
    case_eq (beval e); intro; constructor; rewrite <- H; assumption.
Defined.

Lemma sbevalCorrect2 : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
  intro.
  exists (sbeval e).
  induction e; simpl.
    
    auto.

    case_eq (sbeval e1); intro.

      constructor.
      rewrite <- H.
      assumption.
  
      case_eq (sbeval e2); intro.

        apply eorr.
        rewrite <- H0.
        assumption.
        
        apply eorrl; [rewrite <- H | rewrite <- H0]; assumption.
    
    case_eq (sbeval e); intro; constructor; rewrite <- H; assumption.
Defined.

End Ej3.

Extraction "BEval1" sbevalCorrect bevalCorrect.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "BEval2" sbevalCorrect bevalCorrect.


Section list_perm.

Variable A:Set.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.

Fixpoint append (l1 l2 : list) {struct l1} : list :=
  match l1 with
      | nil => l2
      | cons a l => cons a (append l l2)
  end.

Inductive perm : list -> list ->Prop:=
  | perm_refl: forall l, perm l l
  | perm_cons: forall a l0 l1, perm l0 l1-> perm (cons a l0)(cons a l1)
  | perm_app: forall a l, perm (cons a l) (append l (cons a nil))
  | perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Hint Constructors perm.

Function reverse (xs : list) {struct xs} : list :=
  match xs with
        nil => nil
      | cons z zs => append (reverse zs) (cons z nil)
  end.

Lemma Ej6_4: forall l: list, {l2: list | perm l l2}.
Proof.
  intro.
  exists (reverse l).
  induction l; simpl.
  trivial.
  apply (perm_trans (cons a l) (cons a (reverse l)) (append (reverse l) (cons a nil))); auto.  
Defined.

End list_perm.


Section Ej5.

Inductive Le:nat->nat->Prop :=
| eqLe : forall n, Le 0 n
| SucLe  : forall n m, Le n m -> Le (S n) (S m).

Inductive Gt:nat->nat->Prop :=
| eqGt : forall n, Gt (S n) 0
| SucGt : forall n m, Gt n m -> Gt (S n) (S m).

Function leBool (n m : nat) {struct n} : bool :=
  match n with
        0 => true
      | S k1 => match m with
                      0 => false
                    | S k2 => leBool k1 k2
                end
  end.

Hint Constructors Le Gt.

Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
  intros.
  functional induction (leBool n m); [left | right | ]; trivial.
  elim IHb; intro; 
  [left | right];
  auto.
Qed.

Require Import Omega.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
  intros.
  functional induction (leBool n m); [left | right | ]; try omega.
  elim IHb; intro; 
  [left | right];
  omega.
Qed.

End Ej5.


Section Ej6.

Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
  match qr with
     (q,r) => (a = b*q + r) /\ r < b
  end.

Theorem nat_div_mod :
      forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
  intros.
  induction a.
  exists (0,0).
  simpl.
  omega.
  elim IHa.
  intros (q, r) H1.
  simpl in H1.
  case_eq b; intros.
  elim H; assumption.
  elim H1; intros; clear H1.
  rewrite H0 in H2.
  case_eq (leb (S r) n); intro.
  exists (q, S r).
  rewrite H2.
  simpl.
  split.
  omega.
  pose proof leb_complete (S r) n H1.
  apply le_lt_n_Sm.
  assumption.
  
  exists (S q, 0).
  rewrite H2.
  simpl.
  pose proof (not_eq b 0 H); clear H.
  inversion_clear H4.
  pose proof (lt_n_0 b).
  absurd (b < 0); assumption.
  split.
  rewrite H0 in H3.
  pose proof (leb_complete_conv n (S r) H1); clear H1.
  pose proof lt_n_Sm_le n r H4; clear H4.
  pose proof lt_n_Sm_le r n H3; clear H3.
  pose proof le_antisym n r H1 H4.
  rewrite <- H3.
  pose proof mult_succ_r n q.
  rewrite H5.
  omega.
  rewrite <- H0.
  assumption.
Defined.

End Ej6.

Extraction "nat_div_mod" nat_div_mod.


Section Ej7.

Inductive tree (A:Set) : Set :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
| tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
| tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
  unfold well_founded.
  induction a;
  constructor;
  intros;
  inversion_clear H;
  assumption.
Qed.

End Ej7.


Section Ej8.

Function size (e : BoolExpr) : nat :=
  match e with
        bbool b => 1
      | or e1 e2 => size e1 + size e2 + 1
      | bnot e1 => size e1 + 1
  end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.

Theorem well_founded_elt : well_founded elt.
Proof.
  apply (well_founded_lt_compat BoolExpr size elt).
  intros.
  unfold elt in *.
  assumption.
Qed.

End Ej8.