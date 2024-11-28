Require Import include_frm.
Require Import os_core.
(* Require Import os_q. *)
(* Require Import os_mbox. *)
(* Require Import os_time. *)
(* Require Import os_mutex. *)
(* Require Import os_sem. *)
Require Import get_free_obj_idx. 
Require Import kernel_obj_create. 
Require Import kernel_obj_delete.
Require Import kernel_obj_oper. 
Require Import service_obj_create. 
Require Import service_obj_delete.
Require Import service_obj_oper.

Require Import service_sema_oper. 
Require Import kernel_sema_oper.

Require Import os_cpu_a.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_task.


(* eta i, all the functions defined in 'os_core.v' are os internal functions. *)

Definition internal_fun_list := 
  (
    OSIntExit_impl :: 
      OS_Sched_impl ::
      OS_EventTaskRdy_impl :: 
      OS_EventTaskWait_impl ::
      OS_EventWaitListInit_impl :: 
      OS_EventRemove_impl ::
      OS_TCBInit_impl ::
      get_free_obj_idx_impl ::
      kernel_obj_create_impl ::
      kernel_obj_delete_impl ::
      kernel_obj_oper_impl ::
      OSSemPend_impl ::
      OSSemPost_impl :: 
      nil
  )%list. 

Definition os_internal :=   convert_cfuns internal_fun_list.

Definition api_fun_list :=
  (
    service_obj_create_impl ::
      service_obj_delete_impl ::
      service_obj_oper_impl :: 
      service_sema_P_impl ::
      service_sema_V_impl :: 
      OSTaskCreate_impl ::
      OSTaskDel_impl :: 
      nil
  )%list.

Definition os_api := convert_cfuns api_fun_list.   


(* theta*)


Definition interrupt_list := (OSTickISR_impl :: nil)%list.

Definition  os_interrupt := convert_ifuns interrupt_list.

Definition low_level_os_code := (os_api, os_internal, os_interrupt).


(*Definition getFunType fid : type :=
    match os_api fid with
    | Some (t, _ , _ , _) => t
    | None => Tnull
    end.

Definition getFunArgs fid : decllist :=
    match os_api fid with
    | Some (_, args , _ , _) => args
    | None => dnil
    end.

Definition getFunDecls fid : decllist :=
    match os_api fid with
    | Some (_ , _ , decls , _) => decls
    | None => dnil
    end.

Definition getFunBody fid : stmts :=
    match os_api fid with
    | Some (_ , _ , _ , body) => body
    | None => sskip None
    end. *)
