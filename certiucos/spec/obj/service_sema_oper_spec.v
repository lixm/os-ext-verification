
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import service_sema_oper.
(* Require Import kernel_sema_oper. *)
Require Import ifun_spec.
Require Import abs_op.

Require Import kernel_sema_oper_spec.

Open Scope list_scope.

(* (****************************** service_sema_P ************************************) *)  

Definition semwait_idx_err 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idxv, 
      vl = ((Vint32 idxv) :: nil) /\ 
        (Int.ltu idxv Int.zero = true \/
           Int.ltu (Int.repr MAX_OBJ_NUM) idxv = true \/ Int.eq idxv (Int.repr MAX_OBJ_NUM) = true) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        O_opt = Some O1
  end.

Definition semwait_kobj_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx objs,
     vl = (Vint32 idx) :: nil /\
     Int.ltu idx Int.zero = false /\
     Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
     get O1 absobjsid = Some (absobjs objs) /\
     ~ (exists ptr attr, get objs idx = Some (objid ptr, attr)) /\
      opv = Some (Vint32 (Int.mone)) /\
       O_opt = Some O1
  end.

Definition semwait_get_kobj
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx objs attr ptr vptr,
     vl = (Vint32 idx) :: (vptr) :: nil /\
     Int.ltu idx Int.zero = false /\
     Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
     get O1 absobjsid = Some (absobjs objs) /\
     get objs idx = Some (objid ptr, attr) /\
     opv = None /\
     (vptr = Vptr ptr /\ O_opt = Some O1
      \/ vptr <> Vptr ptr /\ O_opt = None)
  end.

Definition semwait_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr,
      vl = verr :: nil /\
        opv = Some verr /\
        O_opt = Some O1
  end.

Definition semwait (vl: vallist) :=
  match vl with
    vidx :: vptr :: verr :: nil => 
      (semwait_idx_err (|vidx :: nil|) ??
         semwait_kobj_err (|vidx :: nil|) ??
         (semwait_get_kobj (|vidx :: vptr :: nil|) ;;
          (spec_code_cons (sem_pend (vptr :: verr :: nil)) (semwait_ret (|verr :: nil|)))))
  | _ => spec_abort
  end.

Definition semwaitapi := (semwait, (Tint8, Tint32 :: nil)). 


(* (****************************** service_sema_V ************************************) *)

Definition semsignal_idx_err 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idxv,
      vl = ((Vint32 idxv) :: nil) /\
        (Int.ltu idxv Int.zero = true \/
           Int.ltu (Int.repr MAX_OBJ_NUM) idxv = true \/ Int.eq idxv (Int.repr MAX_OBJ_NUM) = true) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semsignal_kobj_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idx objs,
      vl = (Vint32 idx) :: nil /\
        Int.ltu idx Int.zero = false /\
        Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
        get O1 absobjsid = Some (absobjs objs) /\
        ~ (exists ptr attr, get objs idx = Some (objid ptr, attr)) /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semsignal_get_kobj
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idx objs attr ptr vptr, 
      vl = (Vint32 idx) :: (vptr) :: nil /\
        Int.ltu idx Int.zero = false /\
        Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
        get O1 absobjsid = Some (absobjs objs) /\
        get objs idx = Some (objid ptr, attr) /\
        opv = None /\
        (vptr = Vptr ptr /\ O_opt = Some O1
         \/ vptr <> Vptr ptr /\ O_opt = None)
  end.

Definition semsignal_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr,  
      vl = verr :: nil /\
        opv = Some verr /\
        O_opt = Some O1 
  end.

Definition semsignal (vl: vallist) := 
  match vl with
    v1 :: v2 :: v3 :: nil =>  
      (semsignal_idx_err (|v1 :: nil|) ??
         semsignal_kobj_err (|v1 :: nil|) ??
         semsignal_get_kobj (|v1 :: v2 :: nil|) ;; 
       ((spec_code_cons (sem_post (v2 :: v3 :: nil)) (semsignal_ret (| v3 :: nil |)))))
  | _ => spec_abort
  end.

Definition semsignalapi := (semsignal, (Tint8, Tint32::nil)).

