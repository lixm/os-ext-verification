(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)

Require Import ucos_include.
Require Import OS_EventWaitListInit.
Require Import Lia.

Open Scope code_scope.

(* modified/new in os_program.v *)

(* Definition new_internal_fun_list :=  *)
(*   (OS_EventWaitListInit_impl :: nil)%list. *)

(* Definition new_os_internal :=   convert_cfuns new_internal_fun_list. *)

Lemma OSEventWaitListInit_proof:
    forall  vl p r ll tid, 
      Some p =
      BuildPreI os_internal OS_EventWaitListInit vl ll  OS_EventWaitListInitPre  tid->
      Some r =
      BuildRetI os_internal OS_EventWaitListInit vl ll OS_EventWaitListInitPost tid ->
      exists t d1 d2 s,
        os_internal OS_EventWaitListInit = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv,  I, r, Afalse|}|- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare unfold pre.
  apply vallist_destru in H0; simp join.
  hoare forward.
  hoare forward.
  simpl; auto.
  right. eexists. eauto.
  (* hoare forward. *)
  (* simpl; auto. *)
  (* right. eexists. eauto. *)
  simpl typelen.
  simpl Int.mul.
  erewrite Int.mul_zero.
  rewrite Int.add_zero.
  rewrite Int.add_zero.
  rewrite eq_1 in *.
  hoare forward;simpl; 
  try rewrite Zdiv_1_r in *;
  try rewrite <-Zminus_diag_reverse; eauto; try lia.
  hoare forward;simpl; 
  try rewrite Zdiv_1_r in *;
  try rewrite <-Zminus_diag_reverse; eauto; try lia.

(*   pure_auto. *)
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_2 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_3 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_4 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_5 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_6 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_7 in *.
  hoare forward.
  hoare forward; pure_auto.
  rewrite  Int.mul_one in *; unfold Int.one; rewrite eq_8 in *.
  hoare forward.
  hoare forward.
  sep auto.
  splits; simpl; auto.
Qed.
