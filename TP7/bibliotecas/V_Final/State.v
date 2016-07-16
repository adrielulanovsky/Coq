(*******************************************************************
 * Este archivo especifica el estado.
 * Los mapping A B fueron cambiados a funciones f: A -> option B
 ******************************************************************)

Section State.

(** Identificadores de OSs e Hypercalls *)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.


(* Memoria y direcciones *)

(* Direcciones Virtuales. *)
Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(** Direcciones de Máquina. *)
Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(** Direcciones Físicas : 
Los sitemas operativos utilizan este tipo de direcciones para ver regiones de memoriea
contigua. Estos no ven direcciones de máquina. *)
Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(** Memory values. *)
Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


(* Environment *)
Record context : Set :=
  Context
    {(** una dirección virtual es accesible, i.e. no está reserveda 
         por el Hypervisor *)
       ctxt_vadd_accessible: vadd -> bool;
     (** guest Oss (Confiable/No Confiable) **)
       ctxt_oss : os_ident -> bool
    }.

(*******************************************************************
********************************************************************)

Record os :=
  OS
    {
       curr_page : padd;
       hcall : option Hyperv_call
    }.

Notation "A |-> B" := (A -> option B) (at level 60).

Inductive exec_mode :=
| usr : exec_mode 
| svc : exec_mode.

Inductive os_activity :=
| running : os_activity
| waiting : os_activity.

Inductive content : Set :=
| RW : option value -> content
| PT : (vadd |-> madd) -> content 
| Other : content.

Inductive page_owner : Set :=
| Hyp : page_owner
| Os : os_ident -> page_owner 
| No_Owner : page_owner.

Record page :=
  Page
    {
       page_content : content;
       page_owned_by : page_owner
    }.

Definition oss_map := os_ident |-> os.

Definition hypervisor_map := os_ident |-> (padd |-> madd).

Definition system_memory := madd |-> page.

Record State :=
  St
    {
       active_os : os_ident;
       aos_exec_mode : exec_mode;
       aos_activity : os_activity;
       oss : oss_map;
       hypervisor : hypervisor_map;
       memory : system_memory
    }.


(* Differ s valor s' 1 2 y 3 dicen que s' = s, excepto s'.(campo) = valor *)
Inductive differ_active_os : State -> os_ident -> State -> Prop :=
  differ1_intro : forall (s1 s2 : State) (o : os_ident), 
                  s2.(active_os) = o 
                  -> s2.(aos_exec_mode) = s1.(aos_exec_mode)
                  -> s2.(aos_activity) = s1.(aos_activity)
                  -> s2.(oss) = s1.(oss)
                  -> s2.(hypervisor) = s1.(hypervisor)
                  -> s2.(memory) = s1.(memory)
                  -> differ_active_os s1 o s2.

Inductive differ_aos_exec_mode : State -> exec_mode -> State -> Prop :=
  differ2_intro : forall (s1 s2 : State) (ex : exec_mode), 
                  s2.(active_os) = s1.(active_os) 
                  -> s2.(aos_exec_mode) = ex
                  -> s2.(aos_activity) = s1.(aos_activity)
                  -> s2.(oss) = s1.(oss)
                  -> s2.(hypervisor) = s1.(hypervisor)
                  -> s2.(memory) = s1.(memory)
                  -> differ_aos_exec_mode s1 ex s2.

Inductive differ_aos_activity : State -> os_activity -> State -> Prop :=
  differ3_intro : forall (s1 s2 : State) (act : os_activity), 
                  s2.(active_os) = s1.(active_os) 
                  -> s2.(aos_exec_mode) = s1.(aos_exec_mode)
                  -> s2.(aos_activity) = act
                  -> s2.(oss) = s1.(oss)
                  -> s2.(hypervisor) = s1.(hypervisor)
                  -> s2.(memory) = s1.(memory)
                  -> differ_aos_activity s1 act s2.

(* Differ 4 5 y 6 dicen que s' difiere de s solo en el valor del id del map
 respectivo *)

Inductive differ_oss : State -> os_ident -> State -> Prop :=
  differ4_intro : forall (s1 s2 : State) (id : os_ident), 
                  s2.(active_os) = s1.(active_os) 
                  -> s2.(aos_exec_mode) = s1.(aos_exec_mode)
                  -> s2.(aos_activity) = s1.(aos_activity)
                  -> (forall id2 : os_ident, id <> id2 ->
                  s2.(oss) id2 = s1.(oss) id2)
                  -> s2.(hypervisor) = s1.(hypervisor)
                  -> s2.(memory) = s1.(memory)
                  -> differ_oss s1 id s2.

Inductive differ_hypervisor : State -> os_ident -> State -> Prop :=
  differ5_intro : forall (s1 s2 : State) (id : os_ident), 
                  s2.(active_os) = s1.(active_os) 
                  -> s2.(aos_exec_mode) = s1.(aos_exec_mode)
                  -> s2.(aos_activity) = s1.(aos_activity)          
                  -> s2.(oss) = s1.(oss)
		  -> (forall id2 : os_ident, id <> id2 ->
                  s2.(hypervisor) id2 = s1.(hypervisor) id2)
                  -> s2.(memory) = s1.(memory)
                  -> differ_hypervisor s1 id s2.

Inductive differ_memory : State -> madd -> State -> Prop :=
  differ6_intro : forall (s1 s2 : State) (ma : madd), 
                  s2.(active_os) = s1.(active_os) 
                  -> s2.(aos_exec_mode) = s1.(aos_exec_mode)
                  -> s2.(aos_activity) = s1.(aos_activity)          
                  -> s2.(oss) = s1.(oss)
		  -> s2.(hypervisor) = s1.(hypervisor)
                  -> (forall ma2 : madd, ma <> ma2 ->
                  s2.(memory) ma2 = s1.(memory) ma2)
                  -> differ_memory s1 ma s2.

Inductive is_RW : content -> Prop :=
  is_RW_intro : forall (x : option value), is_RW (RW x).

End State.
