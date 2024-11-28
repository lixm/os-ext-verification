Require Import os_program.
Require Import abs_op.
Require Import include_frm.
Require Import os_code_defs.

Local Open Scope list_scope.

Require Import service_obj_create_spec.
Require Import service_obj_delete_spec.
Require Import service_obj_oper_spec.
Require Import service_sema_oper_spec.


Definition api_spec_list : list (fid * osapi) := 
  (service_obj_create, sobjcreapi) ::
    (service_obj_delete, sobjdelapi) ::
    (service_obj_oper, sobjoperapi) :: 
    (service_sema_P, semwaitapi) :: 
    (service_sema_V, semsignalapi) :: 
    (OSTaskCreate, taskcreapi) ::
    (OSTaskDel, taskdelapi) ::
  nil.

Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.


Definition api_spec := convert_api_spec api_spec_list.

Definition int_spec_list : list (hid * int_code) := (OSTickISR, timetick)  ::  nil.  

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.


Definition int_spec := convert_int_spec int_spec_list. 

Definition os_spec : osspec := (api_spec, int_spec, GetHPrio).


