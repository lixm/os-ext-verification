
Require Import include_frm.
Require Import os_code_defs. 

(* Require Import ifun_spec. *)
Require Export os_inv.
Require Import List.

Require Import Maps. 

Require Import get_free_obj_idx.

(* Require Import obj_common. *)
(* Require Import obj_common_ext.  *)


Open Scope code_scope.
Local Open Scope Z_scope.
Open Scope int_scope.

Definition ObjArr_full_P objvl := 
  forall i vl1,
    (0 <= i /\ i < Z.of_nat (length objvl)) ->
    nth_vallist (nat_of_Z i) objvl = Some vl1 ->
    ~(V_ObjPtr vl1 = Some Vnull).

Definition nth_ObjArr_free_P i objvl :=
  exists vl1,
    0 <= i /\ i < Z.of_nat (length objvl) /\ 
      nth_vallist (nat_of_Z i) objvl = Some vl1 /\
      V_ObjPtr vl1 = Some Vnull.


(* pre *)

(* the pre-condition for the function **get_free_obj_idx** *) 
Definition getFreeObjIdxPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s objvl lg', 
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
    AObjArr objvl **
     A_isr_is_prop ** <||s||> **
    [|logicl = logic_llv objvl :: logic_code s :: lg'|] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg'). 

Open Scope int_scope.
Local Open Scope Z_scope.

(* the post-condition for the function **get_free_obj_idx** *) 
Definition getFreeObjIdxPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  (EX s objvl i lg',
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
      AObjArr objvl **
      A_isr_is_prop ** <||s||> **
      [| nth_ObjArr_free_P i objvl  |] **
      [| v = Some (V$ i)|] **
      [|logicl = logic_llv objvl :: logic_code s :: lg' |] ** p_local OSLInv ct (logic_val (V$1) :: lg')) \\// (*return i*)
    (EX s objvl lg',
      Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
        AObjArr objvl **
        A_isr_is_prop ** <||s||> **
        [| ObjArr_full_P objvl |] ** 
        [| v = Some (V$ 255)|] **
        [|logicl = logic_llv objvl :: logic_code s :: lg'|] ** p_local OSLInv ct (logic_val (V$1) :: lg')). (*return 255*) 


Close Scope list_scope.

(* modified/new in os_program.v *)

Definition new_internal_fun_list := 
  (get_free_obj_idx_impl :: nil)%list. 

Definition new_os_internal :=  convert_cfuns new_internal_fun_list. 
