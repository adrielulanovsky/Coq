Section Ej5_3.

Variable A : Set.
Parameter equal : A -> A -> bool.

Axiom equal1 : forall x y : A, equal x y = true -> x = y.
Axiom equal2 : forall x : A, equal x x <> false.

Inductive List : Set :=
 | nullL : List
 | consL : A -> List -> List.

Inductive MemL (a : A) : List -> Prop :=
 | hereL : forall x : List, MemL a (consL a x)
 | thereL : forall x : List, MemL a x -> forall b : A, MemL a (consL b x).

Inductive isSet : List -> Prop := 
 | nullSet : isSet nullL
 | consSet : forall (xs : List) (a : A),
             isSet xs -> ~ (MemL a xs) -> isSet (consL a xs). 

Fixpoint deleteAll (a : A) (xs : List) : List :=
  match xs with
        nullL => nullL
      | consL k ks => match (equal a k) with
                            true => deleteAll a ks
                          | false => consL k (deleteAll a ks)
                      end
  end.

Theorem reflexividad: forall x: A, equal x x = true.
Proof.
  intros.
  case_eq (equal x x); intro.
  trivial.
  elim (equal2 x).
  assumption.
Qed.

Lemma DeleteAllNotMember : forall (l : List) (x : A),
 ~ MemL x (deleteAll x l).
Proof.
  induction l; unfold not; intros; inversion H; apply (IHl x).
  destruct (equal x a).
  rewrite <- H1.
  constructor.

  inversion H1.
  rewrite -> H2 in H.
  simpl in H.
  rewrite reflexividad in H.
  assumption.

  simpl in H.
  destruct (equal x a).
  assumption.
  inversion H0.
  rewrite <- H4.
  assumption.
Qed.

Fixpoint Delete (a : A) (xs : List) : List :=
  match xs with
        nullL => nullL
      | consL k ks => match (equal a k) with
                            true => ks
                          | false => consL k (Delete a ks)
                      end
  end.

Lemma DeleteNotMember : forall (l : List) (x : A), isSet l ->
                               ~ MemL x (Delete x l).
Proof.
  induction l; unfold not; intros.
 
  inversion H0.
  
  apply (IHl x).
    
    inversion H.
    assumption.

    inversion H.
    inversion H0.
    remember (equal x a) as p in H6.
    
    symmetry in Heqp.
    destruct p.
    pose proof (equal1 x a Heqp).
    pose proof (hereL x x0).
    rewrite H6 in H7.
    rewrite H5 in H7.
    absurd (MemL a l); assumption.
    
    inversion H6.
    elim (equal2 x).
    rewrite <- H7 in Heqp.
    assumption.

    remember (equal x a) as p in H5.
    symmetry in Heqp.
    destruct p.

    pose proof (equal1 x a Heqp).
    pose proof (thereL x x0 H6 b).
    rewrite H5 in H8.
    rewrite H7 in H8.
    absurd (MemL a l); assumption.

    inversion H5.
    rewrite H9 in H6.
    assumption.
Qed.

End Ej5_3. 


Section Ej5_4.

Variable A : Set.

Inductive AB: Set := null : AB
                     | cons: A -> AB -> AB -> AB.

Inductive Pertenece : A -> AB -> Prop :=
  is_root : forall (a:A) (t1 t2 : AB), Pertenece a (cons a t1 t2)
  | is_left : forall (a b : A) (t1 t2 : AB), Pertenece a t1 -> Pertenece a (cons b t1 t2)
  | is_right : forall (a b : A) (t1 t2 : AB), Pertenece a t2 -> Pertenece a (cons b t1 t2).

Parameter eqGen: A -> A -> bool.

Fixpoint Borrar (x : A) (ab : AB) : AB :=
  match ab with
        null => null
      | cons a t1 t2 => if (eqGen x a) 
                        then null 
                        else (cons a (Borrar x t1) (Borrar x t2))
  end.

Axiom eqGen1: forall (x:A), ~(eqGen x x) = false.

Lemma eqGen2: forall (x:A), (eqGen x x) = true.
Proof.
  intro.
  case_eq (eqGen x x); intro.
  reflexivity.
  elim (eqGen1 x).
  assumption.
Qed.

Lemma BorrarNoPertenece: forall (x : AB) (a:A), ~(Pertenece a (Borrar a x)).
Proof.
  induction x; unfold not; intros; inversion H.

  case_eq (eqGen a0 a); intro.
    rewrite H1 in H2.
    discriminate.

    rewrite H1 in H2.
    injection H2.
    intros.
    rewrite H5 in H1.
    elim (eqGen1 a).
    assumption.

  case_eq (eqGen a0 a); intro.
    rewrite H3 in H0.
    discriminate.

    rewrite H3 in H0.
    inversion H0.
    rewrite H6 in H2.
    elim (IHx1 a0).
    assumption.

  case_eq (eqGen a0 a); intro.
    rewrite H3 in H0.
    discriminate.

    rewrite H3 in H0.
    inversion H0.
    rewrite H7 in H2.
    elim (IHx2 a0).
    assumption.
Qed.

Inductive SinRepetidos : AB -> Prop :=
  sinNull : SinRepetidos null
| sinCons : forall (a : A) (t1 t2 : AB),
           (forall x:A, Pertenece x t1 -> ~Pertenece x t2)
           -> SinRepetidos t1 -> ~(Pertenece a t1)
           -> SinRepetidos t2 -> ~(Pertenece a t2)
                              -> SinRepetidos (cons a t1 t2).

End Ej5_4.


Section Ej5_5.

Definition Var := nat.

Inductive BoolExpr : Set :=
    VarBE  : Var -> BoolExpr
  | BoolBE : bool -> BoolExpr
  | OrBE   : BoolExpr -> BoolExpr -> BoolExpr
  | NotBE  : BoolExpr -> BoolExpr.

Definition Valor := bool.
Definition Memoria := Var -> Valor.

Definition lookup (m: Memoria) (v: Var) : Valor := m v.

Inductive BEval : BoolExpr -> Memoria -> Valor -> Prop :=
    evar   : forall (v:Var) (m:Memoria), BEval (VarBE v) m (lookup m v)
  | eboolt : forall (m:Memoria), BEval (BoolBE true) m true
  | eboolf : forall (m:Memoria), BEval (BoolBE false) m false
  | eorl   : forall (e1 e2:BoolExpr) (m:Memoria), BEval e1 m true -> BEval (OrBE e1 e2) m true
  | eorr   : forall (e1 e2:BoolExpr) (m:Memoria), BEval e2 m true -> BEval (OrBE e1 e2) m true
  | eorrl  : forall (e1 e2:BoolExpr) (m:Memoria), (BEval e1 m false) -> (BEval e2 m false) 
                    -> BEval (OrBE e1 e2) m false
  | enott  : forall (e:BoolExpr) (m:Memoria), BEval e m true -> BEval (NotBE e) m false
  | enotf  : forall (e:BoolExpr) (m:Memoria), BEval e m false -> BEval (NotBE e) m true.

Lemma notTrue : forall  (m : Memoria) (exp : BoolExpr), BEval exp m false -> ~BEval exp m true.
Proof.
  induction exp; unfold not; intros; inversion H; inversion H0.

    rewrite H7 in H4.
    discriminate.

    rewrite <- H4 in H2.
    discriminate.

    apply IHexp1; assumption.
   
    apply IHexp2; assumption.

    apply IHexp; assumption.
Qed.

Theorem ej5_3a : forall (d : Memoria), ~BEval (BoolBE true) d false.
Proof.
  unfold not; intros.
  inversion H.
Qed.

Theorem ej5_3b : forall (e1 e2 : BoolExpr) (d : Memoria) (w: Valor), 
                 BEval e1 d false /\ BEval e2 d w -> BEval (OrBE e1 e2) d w.
Proof.
  intros.
  elim H; intros; clear H.
  destruct w.
  apply eorr.
  assumption.
  apply eorrl; assumption.
Qed.

Theorem ej5_3c : forall (e : BoolExpr) (d : Memoria) (w1 w2 : Valor), 
                 BEval e d w1 /\ BEval e d w2 -> w1 = w2.
Proof.
  intros.
  elim H; intros; clear H.
  pose proof (notTrue d e) as H.
  destruct w1, w2; trivial;
  [pose proof (H H1) | pose proof (H H0)];
  absurd (BEval e d true); assumption.
Qed.

Theorem ej5_3d : forall (e1 e2 : BoolExpr) (d : Memoria), 
                 BEval e1 d true -> ~BEval (NotBE (OrBE e1 e2)) d true.
Proof.
  unfold not; intros.
  inversion H0.
  clear e m H1 H3.
  inversion H2.
  clear e0 e3 m H1 H3 H5.
  pose proof (notTrue d e1).
  apply H1; assumption.
Qed.

Fixpoint beval (m : Memoria) (e : BoolExpr) : Valor :=
  match e with
      | VarBE v => lookup m v 
      | BoolBE b => b
      | OrBE e1 e2 => match (beval m e1), (beval m e2) with
                            false, false => false
                          | _ , _ => true
                      end
      | NotBE e1 => negb (beval m e1)
  end.

Theorem ej5_5 : forall (e : BoolExpr) (d : Memoria), BEval e d (beval d e).
Proof.
  induction e; intro.

    constructor.
 
    simpl.
    destruct b; constructor.

    simpl.
    case_eq (beval d e1); intro.
      
      apply (eorl e1 e2 d).
      rewrite <- H.
      exact (IHe1 d).
    
      case_eq (beval d e2); intro.

        apply (eorr e1 e2 d).
        rewrite <- H0.
        exact (IHe2 d).

        apply (eorrl e1 e2 d).

          rewrite <- H.
          exact (IHe1 d).

          rewrite <- H0.
          exact (IHe2 d).

    simpl.
    case_eq (beval d e); intro; simpl; constructor; rewrite <- H; exact (IHe d).
Qed.

End Ej5_5.


Section Ejercicio6.

Inductive Instr : Set :=
    Skip   : Instr
  | Assign : Var -> BoolExpr -> Instr
  | ITE    : BoolExpr -> Instr -> Instr -> Instr
  | While  : BoolExpr -> Instr -> Instr
  | Begin  : LInstr -> Instr  
with
  LInstr : Set :=
    Null : LInstr
  | Seq  : Instr -> LInstr -> LInstr.

Infix ";" := Seq (at level 60, right associativity).

Definition PP (v1 v2 : Var) : Instr :=
  Begin (Assign v1 (BoolBE true) ; Assign v2 (NotBE (VarBE v1)) ; Null).

Definition swap (aux v1 v2 : Var) : Instr :=
  Begin (Assign aux (VarBE v1) ; Assign v1 (VarBE v2) ; Assign v2 (VarBE aux) ; Null).

Require Import Coq.Arith.EqNat.

Definition update (d : Memoria) (v : Var) (w : Valor) : Memoria :=
  fun x : Var => if (beq_nat x v) then w else d x.

End Ejercicio6.


Section Ejercicio7.

Infix ";" := Seq (at level 60, right associativity).

Inductive Execute : Instr -> Memoria -> Memoria -> Prop :=
    xAss : forall (e : BoolExpr) (d : Memoria) (v : Var) (w : Valor), 
                  BEval e d w -> Execute (Assign v e) d (update d v w)
  | xSkip : forall d : Memoria, Execute Skip d d
  | xIFthen : forall (c : BoolExpr) (d d1 : Memoria) (p1 p2 : Instr),
                     BEval c d true -> Execute p1 d d1 -> Execute (ITE c p1 p2) d d1
  | xIFelse : forall (c : BoolExpr) (d d2 : Memoria) (p1 p2 : Instr),
                     BEval c d false -> Execute p2 d d2 -> Execute (ITE c p1 p2) d d2
  | xWhileTrue : forall (c : BoolExpr) (d d1 d2 : Memoria) (p : Instr),
                        BEval c d true -> Execute p d d1 -> Execute (While c p) d1 d2
                        -> Execute (While c p) d d2
  | xWhileFalse : forall (c : BoolExpr) (d : Memoria) (p : Instr),
                         BEval c d false -> Execute (While c p) d d
  | xBeginEnd : forall (d d1 : Memoria) (p : LInstr),
                       ExecuteL p d d1 -> Execute (Begin p) d d1
with ExecuteL : LInstr -> Memoria -> Memoria -> Prop :=
    xEmptyblock : forall d : Memoria, ExecuteL Null d d
  | xNext : forall (d d1 d2 : Memoria) (i : Instr) (li : LInstr),
            Execute i d d1 -> ExecuteL li d1 d2 -> ExecuteL (i;li) d d2.

Theorem ej7_2 : forall (d d1 : Memoria) (e1 e2 : Instr),
                       Execute (ITE (NotBE (BoolBE true)) e1 e2) d d1 
                       -> Execute (ITE (BoolBE true) e2 e1) d d1.
Proof.
  intros.
  inversion_clear H;
  inversion_clear H0.

    inversion H.

    apply xIFthen; assumption.
Qed.

Theorem ej7_3 : forall (c : BoolExpr) (d d1 : Memoria) (e1 e2 : Instr),
                       Execute (ITE (NotBE c) e1 e2) d d1 
                       -> Execute (ITE c e2 e1) d d1.
Proof.
  intros.
  inversion_clear H;
  inversion_clear H0;
  [apply xIFelse | apply xIFthen];
  assumption.
Qed.


Theorem ej7_4 : forall (d d1 : Memoria) (p : Instr),
                       Execute (While (BoolBE false) p) d d1 -> d = d1.
Proof.
  intros.
  inversion_clear H;
  inversion_clear H0.
  trivial.
Qed.

Theorem ej7_5 : forall (c : BoolExpr) (d d1 : Memoria) (p : Instr),
                       Execute (Begin ((ITE c p Skip) ; (While c p) ; Null)) d d1
                       -> Execute (While c p) d d1.
Proof.
  intros.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion H2.
  rewrite H4 in H0.
  inversion_clear H.
  
    apply (xWhileTrue c d d2 d1 p); assumption.
    
    inversion H5.
    assumption.
Qed.

Theorem ej7_6 : forall (d : Memoria) (v1 v2 : Var), v1 <> v2 
             -> forall d1 : Memoria, Execute (PP v1 v2) d d1 
             -> lookup d1 v1 = true /\ lookup d1 v2 = false.
Proof.
  intros.
  unfold PP in *.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2.
  inversion H3. clear H3 H4 d0.
  inversion H0. clear H0 H2 H3 H4  e d0 v.
  inversion H7. clear H2 H7 m.
  rewrite <- H3 in H6. clear H3 w.
  inversion H1. clear H1 H0 H2 H3 e d0 v.
  rewrite H5 in *. clear H5 d3.
  elim (beq_nat_false_iff v1 v2); intros.
  pose proof H1 H. clear H1 H0 H.
  pose proof beq_nat_refl v1 as R1.
  pose proof beq_nat_refl v2 as R2.
  
  inversion H7; clear e m H H1 H7;
  inversion H0; clear v m H0 H1 H5;
  unfold lookup in *;
  rewrite <- H4; clear d1 H4;
  rewrite <- H6 in *; clear d2 H6; 
  unfold update in *;
  rewrite H2;
  rewrite <- R1;
  rewrite <- R2;
  rewrite <- H3;
  split; trivial.
Qed.

End Ejercicio7.