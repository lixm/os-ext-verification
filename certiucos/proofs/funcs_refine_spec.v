
Require Import include_frm.
Require Import os_program.
Require Import os_spec.
Require Import Classical.
Require Import abs_op.
Require Import inv_prop.
Require Import os_code_defs.
Require Import ifun_spec.
Require Import base_tac.
Require Import oscorrectness.
Require Import auxdef.
Require Import List.

Require Import service_obj_create_proof.
Require Import service_obj_delete_proof.
Require Import service_obj_oper_proof.
Require Import service_sema_wait_proof.
Require Import service_sema_signal_proof.
Require Import OSTaskCreateProof.
Require Import OSTaskDelProof.

Require Import kernel_obj_create_proof.
Require Import kernel_obj_delete_proof.
Require Import kernel_obj_oper_proof.
Require Import kernel_sema_pend_proof.
Require Import kernel_sema_post_proof. 
Require Import get_free_obj_idx_proof. 
Require Import OSTCBInitProof.
Require Import OS_EventWaitListInit_proof.
Require Import OS_EventTaskWait_proof.
Require Import OSEventTaskRdy.
Require Import OSEventRemoveProof.

Require Import OSSchedProof.
Require Import OSIntExitProof.
Require Import TimeIntProof.

Require Import toptheorem. 

Definition Spec := OS_spec.

Ltac solve_good_decl_stmt hyp := 
  match type of hyp with
    (if ?e then ?e1 else ?e2) = Some _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee; [inverts hyp; splits; simpl; intuition auto | idtac] 
  end.

Lemma good_fun_api:
  forall (f : fid) (t : type) (d1 d2 : decllist) (s : stmts),
    os_api f = Some (t, d1, d2, s) ->
    good_decllist (revlcons d1 d2) = true /\ GoodStmt' s.
Proof.
  intros.
  unfolds in H.
  destruct f; simpl in H; tryfalse.
  repeat (solve_good_decl_stmt H).
  false. 
Qed.

Lemma good_fun_internal:
  forall (f : fid) (t : type) (d1 d2 : decllist) (s : stmts),
    os_internal f = Some (t, d1, d2, s) ->
    good_decllist (revlcons d1 d2) = true /\ GoodStmt' s.
Proof.
  intros.
  unfolds in H.
  destruct f; simpl in H; tryfalse.
  repeat (solve_good_decl_stmt H).
  false.
Qed.

Ltac solve_eqd_api := 
  match goal with 
    H: (if ?e then ?e1 else ?e2) = Some _ |- _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee; 
      [ inverts H; unfold api_spec; unfold api_spec_list; simpl; 
        apply Zeq_bool_eq in ee; 
        subst;
        eexists; simpl; eauto | idtac ]
  end.

Ltac solve_eqd_api' := 
  match goal with 
    H: (if ?e then ?e1 else ?e2) = Some _ |- _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee; 
      [ inverts H;
        unfold os_api; unfold api_fun_list; simpl; 
        apply Zeq_bool_eq in ee; 
        subst; simpl; eexists; simpl; eauto
      | idtac ]
  end.

Ltac solve_tl_vl_mt := 
  match goal with 
    H: (if ?e then ?e1 else ?e2) = Some _ |- _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee; 
      [ inverts H;
        apply Zeq_bool_eq in ee;
        subst;
        match goal with 
          H': Some _ = Some _ |- _ =>
            inverts H'
        end;
        simpl;
        splits; eauto
      | idtac ]
  end.

Lemma eqdomos_p: eqdomOS (os_api, os_internal, os_interrupt) (api_spec, int_spec, GetHPrio).
Proof.
  unfolds.
  splits;intros.
  split;intros.
  {
    simpljoin.
    unfolds in H.
    simpl in *; auto.
    repeat solve_eqd_api.
    false.
  }
  {
    simpljoin. 
    unfolds in H.
    simpl in *; auto.
    repeat solve_eqd_api'.
    false. 
  }
  {
    unfolds in H.
    unfolds in H0.
    simpl in *; auto.
    repeat solve_tl_vl_mt.
    false. 
  }
  {
    split;intros.
    simpljoin.
    destruct i.
    unfold int_spec.
    simpl;eauto.
    unfold os_interrupt in H.
    simpl in H.
    destruct i;tryfalse.
    unfold int_spec;simpl;eauto.
    simpljoin.
    unfolds in H.
    destruct i.
    simpl in H.
    unfold os_interrupt;simpl;eauto.
    simpl in H.
    destruct i.
    unfold os_interrupt.
    simpl;eauto.
    tryfalse.
    tryfalse.
  }
Qed.

Ltac solve_eqd_ifun := 
  match goal with 
    H: (if ?e then ?e1 else ?e2) = Some _ |- _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee; 
      [ inverts H; unfold osq_spec_list; simpl; 
        apply Zeq_bool_eq in ee; 
        inverts ee; 
        eexists; simpl; eauto | idtac ]
  end.

Ltac solve_eqd_ifun' := 
  match goal with 
    H: (if ?e then ?e1 else ?e2) = Some _ |- _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee; 
      [ inverts H; unfold internal_fun_list; simpl; 
        apply Zeq_bool_eq in ee; 
        inverts ee; 
        eexists; simpl; eauto | idtac ]
  end.

Lemma eqdom_internal_lh: EqDom os_internal Spec.
Proof.
  unfolds.
  intros.
  split; intros; simpljoin.
  {
    unfold os_internal in H.
    unfold Spec.
    unfold OS_spec.
    destruct f; simpl in H; tryfalse.    
    repeat solve_eqd_ifun.
    false.
  }
  {
    unfold os_internal.
    unfold Spec in H.
    unfold OS_spec in H.
    destruct f; simpl in H; tryfalse.
    repeat solve_eqd_ifun'.
    false. 
  }
Qed.

Definition ucos_init S O :=  
  initst S O I OSLInv init_lg /\ eqdomSO S O. 

Ltac get_fun := 
  match goal with
    H: (if ?e then ?e1 else ?e2) = Some _ |- _ =>
      let ee := fresh "E" in 
      destruct e eqn: ee;
      [inverts H;
       apply Zeq_bool_eq in ee; 
       inverts ee  | 
        idtac]
  end.

Ltac solve_ifun thm := 
  do 3 eexists; 
  splits; 
  [
    unfold os_internal; 
    simpl; 
    auto |
    simpl; auto | 
    intros;
    match goal with
      H1: Some _ = BuildPreI _ _ _ _ _ _,
        H2: Some _ = BuildRetI _ _ _ _ _ _ |- _ =>
        let hyp_ := fresh "H_" in 
        lets hyp_: thm H1 H2;  
        simpljoin;
        match goal with
          H: os_internal _ = Some (_, _, _, _) |- _ =>
            unfold os_internal in H; simpl in H; inverts H; auto
        end
    end
  ]. 

Theorem ucos_toprule: TopRule low_level_os_code os_spec ucos_init.
Proof.
  unfold low_level_os_code.
  unfold os_spec.
  lets Hos: eqdomos_p.
  eapply top_rule with (I:=I) (Spec:=OS_spec) (lasrt:=OSLInv);eauto.
  constructors;eauto.
  unfolds.
  unfolds in Hos.
  simpljoin; auto. 
  2: {
    constructors; eauto.
    unfolds in Hos.
    unfolds.
    simpljoin; auto.
    intros.
    destruct i; tryfalse.
    eapply timetickisr_proof;eauto.  (* tick_isr *) 
  }
  {
    intros.
    simpl in H.
    unfold api_spec in *.
    destruct f; simpl in H; tryfalse.

    get_fun.
    eapply service_obj_create_Proof; eauto.
    get_fun.
    eapply service_obj_delete_Proof; eauto.
    get_fun.
    eapply service_obj_oper_Proof; eauto.
    get_fun.
    eapply service_sema_wait_Proof; eauto.
    get_fun.
    eapply service_sema_signal_Proof; eauto.
    get_fun.
    eapply TaskCreateProof; eauto.
    get_fun.
    eapply TaskDeleteProof; eauto.
    false. 
  }
  {
    constructors.
    apply eqdom_internal_lh.
    intros.

    unfold OS_spec in H.
    simpl in H.

    get_fun.
    solve_ifun OSEventRemove_proof.
    get_fun.
    solve_ifun OSEventTaskRdy_proof.
    get_fun.
    solve_ifun OSEventTaskWait_proof. 
    get_fun.
    solve_ifun OSSched_proof.
    get_fun.
    solve_ifun OSIntExit_proof.
    get_fun.
    solve_ifun OSEventWaitListInit_proof.
    get_fun.
    solve_ifun OSTCBInit_proof.
    get_fun.
    solve_ifun kernel_obj_create_proof.
    get_fun.
    solve_ifun kernel_obj_delete_proof.
    get_fun.
    solve_ifun kernel_obj_oper_proof.
    get_fun.
    solve_ifun get_free_obj_idx_proof.
    get_fun. 
    solve_ifun kernel_sema_pend_proof.
    get_fun.
    solve_ifun kernel_sema_post_proof.
    false. 
  }
  {
    unfolds.
    split;auto.
    apply GoodI_I.    
  }
Qed.

Theorem all_funcs_correct:
  GOOD_OS low_level_os_code os_spec ucos_init.
Proof.
  apply Soundness.
  apply ucos_toprule.
Qed.
