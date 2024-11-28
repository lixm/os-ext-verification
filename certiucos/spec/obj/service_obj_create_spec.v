
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import service_obj_create.
Require Import kernel_obj_create_spec.
Require Import get_free_obj_idx_spec.
(* Require Import ifun_spec. *)

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition sobjcre_get_idx_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists objs,
        opv =  Some (Vint32 (Int.mone)) /\ 
        get O1 absobjsid = Some (absobjs objs) /\
        (~(exists idx attr,  get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM) 
         /\ O_opt = Some O1)
  end.
            
Definition sobjcre_get_idx_ok
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vidx objs,
      vl = (vidx :: nil) /\
      opv = None /\
        get O1 absobjsid = Some (absobjs objs) /\
        (exists idx attr,
            get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM
            /\ (vidx = Vint32 idx /\ O_opt = Some (set O1 absobjsid (absobjs (set objs idx (objholder, attr))))
                \/ vidx <> Vint32 idx /\ O_opt = None
        ))
  end.
              
Definition sobjcre_create_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idx objs oid attr,
      vl = (Vint32 idx :: Vnull :: nil) /\
      Vint32 idx <> Vint32 (Int.repr 255) /\
      0 <= Int.unsigned idx < MAX_OBJ_NUM /\
      get O1 absobjsid = Some (absobjs objs) /\
      get objs idx = Some (oid, attr) /\
      opv = Some (Vint32 Int.mone) /\
      O_opt = Some (set O1 absobjsid (absobjs (set objs idx (objnull, attr))))
  end.

Definition sobjcre_create_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idx objs oid attr ptr satt,
      vl = (Vint32 idx :: Vptr ptr :: Vint32 satt :: nil) /\
      Vint32 idx <> Vint32 (Int.repr 255) /\
      0 <= Int.unsigned idx < MAX_OBJ_NUM /\
      get O1 absobjsid = Some (absobjs objs) /\
      get objs idx = Some (oid, attr) /\
      opv = Some (Vint32 idx) /\
      O_opt = Some (set O1 absobjsid (absobjs (set objs idx (objid ptr, satt))))
  end.

(* the abstract program for the function **service_obj_create**  *) 
Definition sobjcre (vl: vallist) :=
  match vl with
    vkatt :: vsatt :: vr_idx :: vr_cre :: nil =>
      sobjcre_get_idx_err (| nil |) ??
        ((sobjcre_get_idx_ok (| vr_idx :: nil |) ;;
          kobjcre (vkatt :: vr_cre :: nil) ;;
          (sobjcre_create_err (| vr_idx :: vr_cre :: nil |) ??
             sobjcre_create_succ (| vr_idx :: vr_cre :: vsatt :: nil |))))
  | _ => spec_abort
  end.

Local Open Scope code_scope.

Definition sobjcreapi := (sobjcre, (Tint32, Tint16 :: Tint32 :: nil)).

(* Require Import os_program. *)
(* Require Import abs_op. *)
(* Require Import include_frm. *)
(* Require Import os_code_defs. *)
(* Require Import os_spec. *)

(* Require Import os_inv. *)
(* Require Import inv_prop. *)

(* Require Import init_spec. *)

(* Local Open Scope list_scope. *)

(* Definition new_api_spec_list :=  *)
(*   (service_obj_create, sobjcreapi) :: nil. *)

(* Definition new_api_spec := convert_api_spec new_api_spec_list. *)

(* Definition new_os_spec := (new_api_spec, GetHPrio). *)


(* Local Open Scope list_scope. *)

(* Definition new_osq_spec_list_ext := *)
(*   (((kernel_obj_create, KObjCreate_spec) :: nil) *)
(*      ++ new_osq_spec_list). *)

(* Definition OS_spec_ext :=  convert_spec new_osq_spec_list_ext. *)
