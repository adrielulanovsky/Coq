(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Load State.

(* Contexto global *)
Parameter contexto : context. 

(********************** Predicados útiles ******************************)
Definition trusted_os (o : os_ident) : Prop :=
  contexto.(ctxt_oss) o = true.

(* Esto es que la current page table del so mapee la va con ma. *)
Definition va_mapped_to_ma (s : State) (v: vadd) (m : madd) : Prop :=
  exists osi : os, s.(oss) s.(active_os) = Some osi
  /\ exists p_to_m : padd -> option madd,
     s.(hypervisor) s.(active_os) = Some p_to_m
  /\ exists m2 : madd, p_to_m osi.(curr_page) = Some m2
  /\ exists pg : page, s.(memory) m2 = Some pg
  /\ exists v_to_m : vadd -> option madd, 
     pg.(page_content) = (PT v_to_m)
  /\ v_to_m v = Some m.

Definition os_accessible (va : vadd) : Prop :=
  contexto.(ctxt_vadd_accessible) va = true.

Definition change_function (X Y : Set) (F : X -> option Y)
                           (G : forall m n : X, {m = n} + {m <> n})
                           (x:X) (y:Y) : X -> option Y :=
  fun (a : X) => if G a x then Some y
                          else F a.

Implicit Arguments change_function [X Y].


(*************** Acciones ***********************)
Inductive Action :=
| read : vadd -> Action
| write : vadd -> value -> Action
| chmod : Action.

(************** Pre y Post **********************)
Inductive Pre : State -> Action -> Prop :=
  PreRead : forall (s : State) (va : vadd),
            os_accessible va ->
            s.(aos_activity) = running 
            -> (exists ma : madd, va_mapped_to_ma s va ma 
                /\ exists pg : page, (s.(memory)) ma = Some pg
                /\ is_RW pg.(page_content))
            ->  Pre s (read va)
| PreWrite : forall (s : State) (va : vadd) (val : value),
            os_accessible va
            ->  s.(aos_activity) = running
            -> (exists ma : madd, va_mapped_to_ma s va ma 
            /\ exists pg : page, (s.(memory)) ma = Some pg
            /\ is_RW pg.(page_content)) 
            ->  Pre s (write va val)
| PreChmod : forall (s : State) (va : vadd),
             s.(aos_activity) = waiting
             -> (exists o:os, s.(oss) s.(active_os) = Some o
                 /\ o.(hcall) = None)
             -> Pre s (chmod).

Inductive Post : State -> Action -> State -> Prop :=
  PostRead : forall (s : State) (va : vadd),
             Post s (read va) s
| PostWrite : forall (s s2 : State) (va : vadd) (val : value),
              (exists ma : madd, va_mapped_to_ma s va ma 
              /\ s2.(memory) = 
              change_function (s.(memory)) madd_eq ma (Page (RW (Some val)) (Os (s.(active_os))))
              /\ differ_memory s ma s2)
              -> Post s (write va val) s2
| PostChmod : forall (s s2 : State),
              (trusted_os (s.(active_os)) 
                /\ s2 = St s.(active_os) svc running s.(oss) s.(hypervisor) s.(memory))
              \/ (~trusted_os (s.(active_os)) 
                /\ s2 = St s.(active_os) usr running s.(oss) s.(hypervisor) s.(memory))
              -> Post s chmod s2.

(************************* Valid State ******************************)
Definition valid_state_3 (s: State) : Prop :=
  ((s.(aos_activity) = running /\ trusted_os s.(active_os))  
  \/ s.(aos_activity) = waiting)
  -> s.(aos_exec_mode) = svc.

Definition valid_state_5 (s : State) : Prop :=
  forall (pa : padd) (osi : os_ident) (p_to_m : padd -> option madd),
          Some p_to_m = s.(hypervisor) osi
          -> exists ma : madd, p_to_m pa = Some ma
             /\ (exists pag : page, s.(memory) ma = Some pag
             /\ pag.(page_owned_by) = Os osi)
             /\ (forall pa2 : padd, pa <> pa2 
                -> exists ma2 : madd, p_to_m pa2 = Some ma2
                /\ ma <> ma2).

Definition valid_state_6 (s : State) : Prop :=
  forall (p : page) (osi : os_ident) (v_to_m : vadd -> option madd),
           p.(page_owned_by) = Os osi
           -> p.(page_content) = PT v_to_m
           -> (exists ma : madd,
              s.(memory) ma = Some p)
           -> forall va: vadd, (os_accessible va -> 
                                   (exists ma1 : madd, v_to_m va = Some ma1
                                 /\ exists pg1 : page, s.(memory) ma1 = Some pg1
                                 /\ pg1.(page_owned_by) = Os osi))
                            /\ (~os_accessible va -> 
                                    (exists ma1 : madd, v_to_m va = Some ma1
                                  /\ exists pg1 : page, s.(memory) ma1 = Some pg1
                                  /\ pg1.(page_owned_by) = Hyp)).

Inductive valid_state : State -> Prop :=
  v_st : forall (s: State),
         valid_state_3 s
         -> valid_state_5 s
         -> valid_state_6 s
         -> valid_state s.

Inductive OneStepExec : State -> Action -> State -> Prop :=
  OneStepExec_intro : forall (s s2 : State) (a : Action),
                      valid_state s
                      -> Pre s a
                      -> Post s a s2
                      -> OneStepExec s a s2.

(* Ej. 7.6 *)
Lemma valid_state_3_invariant : forall (s s2 : State) (a : Action),
              OneStepExec s a s2
              -> valid_state_3 s2.
Proof.
  intros.
  inversion_clear H.
  inversion_clear H0.
  destruct a.
    inversion H2.
    rewrite <- H5.
    assumption.

    inversion_clear H2.
    inversion_clear H0.
    inversion_clear H2.
    inversion_clear H5.
    inversion_clear H6.
    unfold valid_state_3 in *.
    rewrite H8.
    rewrite H5.
    rewrite H7.
    assumption.
    
    inversion_clear H2.
    unfold valid_state_3 in *.
    inversion_clear H0;
    inversion_clear H2;
    inversion_clear H5;
    simpl;
    intro.
      reflexivity.

      inversion_clear H2.
        inversion_clear H5.
        elim H0.
        assumption.
        
        discriminate.
Qed.

(* Ej. 7.7 *)
Lemma Read_Isolation : forall (s1 s2 : State) (va : vadd),
                       OneStepExec s1 (read va) s2
                       -> exists ma : madd, va_mapped_to_ma s1 va ma 
                       /\ exists pg : page, Some pg = s1.(memory) ma 
                       /\ pg.(page_owned_by) = Os s1.(active_os).
Proof.
  intros.
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H6.
  exists x.
  inversion_clear H1.
  split.
    assumption.
    
    (* Paso 1 *)
    clear H7.
    inversion_clear H6.
    inversion_clear H1.
    inversion_clear H7.
    inversion_clear H1.
    inversion_clear H8.
    inversion_clear H1.
    inversion_clear H9.
    inversion_clear H1.
    inversion_clear H10.
    inversion_clear H1.

    (* Paso 2 *)
    unfold valid_state_5 in *.
    pose proof (H3 x0.(curr_page) s1.(active_os) x1). clear H3.
    symmetry in H7.
    pose proof (H1 H7). clear H1.
    inversion_clear H3.
    inversion_clear H1.
    inversion_clear H12. clear H13.
    inversion_clear H1.
    inversion_clear H12.
    rewrite H8 in H3.
    inversion H3. clear H3.
    rewrite <- H14 in H1. clear H14 x5.
    rewrite H9 in H1.
    inversion H1. clear H1.
    rewrite <- H12 in H13. clear H12 x6.

    (* Paso 3 *)
    unfold valid_state_6 in *.
    pose proof (H4 x3 s1.(active_os) x4). clear H4.
    assert (exists ma: madd, memory s1 ma = Some x3).
    exists x2. assumption.
    pose proof (H1 H13 H10 H3 va). clear H1 H13 H10 H3.
    inversion_clear H4. clear H3.
    pose proof (H1 H0). clear H1 H0.
    inversion_clear H3.
    inversion_clear H0.
    inversion_clear H3.
    inversion_clear H0.
    rewrite H11 in H1.
    inversion H1. clear H1.
    rewrite <- H10 in *.
    exists x6.
    symmetry in H3.
    split; assumption.
Qed.