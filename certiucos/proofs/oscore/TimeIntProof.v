
(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(*************** Proof of Interupt Handler OSTickISR *****************)
(**************************** Code:***********************************)
(*
OSTickISR ↝ 
{
1     EOI(0);ₛ
2     
3     OSIntExit(­);ₛ
4     IRET
}.
 *)

Require Import ucos_include.
(* Require Import OSTimeTickPure. *)
Require Import oscore_common.

(* Require Import OSQPostPure. *)
Require Import Lia.
Require Import FunctionalExtensionality. 

Require Import seplog_pattern_tacs.

Import DeprecatedTactic.
(* Require Import int_absop_rules. *)

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

Lemma ih_no_lvar:
  forall (aop : absop) (isrreg : isr) (si : is) (cs : cs) (ie : ie) ct lg,
    (<|| aop ||>  ** Aisr isrreg ** Ais si ** Acs cs ** Aie ie ** isr_inv ** OSInv ** A_dom_lenv nil) ** p_local OSLInv ct lg
      ==>
      <|| aop ||>  **
      Aisr isrreg ** Ais si ** Acs cs ** Aie ie **
      [|exists k,gettopis si = k /\ forall j, (0 <= j < k)%nat -> isrreg j = false|] **
      OSInv ** A_dom_lenv nil ** p_local OSLInv ct lg.
Proof.
  intros.
  sep normal in H.
  sep cancel 8%nat 8%nat.
  sep cancel 7%nat 7%nat.
  sep cancel 7%nat 7%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 3%nat 3%nat.
  sep cancel 3%nat 3%nat.
  unfold isr_inv in H.
  sep semiauto.
  destruct H.
  simpl in H.
  simpl.
  destruct H;auto.
  destruct H.
  destruct H0.
  exists x0.
  simpl in H0.
  destruct H0;split;auto.
  simpl in H1.
  simpl in H.
  destruct H.
  rewrite <- H in H1.
  destruct H1;auto.
Qed.

Lemma isrupd_true_false:
  forall ir i,
    isrupd (isrupd ir i true) i false = isrupd ir i false.
Proof.
  intros.
  unfold isrupd.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_nat i x);auto.
Qed.

Lemma timetickisr_proof:
  forall ir si p r ct lg,
    Some p = BuildintPre OSTickISR int_spec ir si I OSLInv ct lg->
    Some r = BuildintRet OSTickISR int_spec ir si I OSLInv ct lg->
    exists s,
      os_interrupt OSTickISR = Some s /\
      {| OS_spec , GetHPrio, OSLInv, I, retfalse, r|}|-ct {{p}} s {{Afalse}}.
Proof.
  intros.
  unfold BuildintPre in H.
  simpl in H.
  unfold ipreasrt' in H.
  inverts H.
  unfold  BuildintRet in H0.
  simpl in H0.
  unfold iretasrt' in H0.
  inverts H0.
  unfold os_interrupt.
  simpl.
  eexists.
  split.
  auto.
  unfold invlth_noisr.
  unfold starinv_noisr.
  simpl.
  
  eapply backward_rule1.
  eapply ih_no_lvar.
  pure intro.
  rename H0 into Hisrinv.
  eapply backward_rule1 with (<|| timetick ||>  **
     Aisr (isrupd ir OSTickISR true) **
     Ais (OSTickISR :: si) **
     Acs nil ** Aie false ** OSInv ** A_dom_lenv nil ** p_local OSLInv ct lg **
     [|exists lg', lg = logic_val ( (V$ 1)) :: lg' \/ lg = logic_val ( (V$ 0)) :: lg' |]). 
  intros.
  unfold p_local in H.
  sep cancel OSInv.
  sep semiauto.
  unfold LINV,OSLInv in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H6.
  exists (logic_val x0 :: logic_val x1 :: nil).
  destruct H8.
  unfolds in H8.
  destruct H8;subst;eauto.
  pure intro.
  rename x into lg'.
  destruct H;subst.
  eapply backward_rule1.
  intros.
  sep lifts (6::8::nil)%nat in H.
  apply inv_change in H.
  exact H.
  unfold OldOSInvWL.
  hoare unfold.

  eapply seq_rule.
  hoare_lifts_trms_pre (Aop, Aisr, Aie, Ais, Acs, A_isr_is_prop).
  (* hoare lifts (21::22::25::23::24::18::nil)%nat pre. *)
  eapply eoi_ieoff_rule'.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  instantiate (1:=0%nat).
  rewrite Int.unsigned_repr.
  
  simpl.
  auto.
  rewrite max_unsigned_val.
  lia.
  
  intros.
  sep_lifts_trms_in H1 (Aisr, Ais, A_isr_is_prop).
  (* sep lifts (1::3::5::nil)%nat in H1. *)
  apply a_isr_is_prop_split in H1.
  
  unfold OSTickISR in H1.
  sep_lifts_trms_in H1 (Aisr, Aie).
  (* sep lifts (1::3::nil)%nat in H1. *)
  exact H1.
  apply GoodI_I.  (*Good I*)
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  unfold AOSTime.
  unfold AOSTCBList.
  hoare unfold.
  unfold tcbdllseg at 1.
  hoare_assert_pure (isptr v'3).
  {
    sep_lifts_trms_in H6 dllseg.
    (* sep lift 2%nat in H6. *)

    eapply dllseg_head_isptr';eauto.
  }
  pure intro.
  unfold isptr in H6.
  destruct H6;tryfalse.
  destruct H6.

  
  (* hoare forward. *)
  (* sep cancel p_local. *)
  (* 7:auto. *)
  (* sep cancel Aisr. *)
  (* sep cancel Aie. *)
  (* sep cancel Acs. *)
  (* sep cancel Ais. *)
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel AOSRdyTblGrp. *)
  (* sep cancel AECBList. *)
  (* exact H7. *)
  (* unfolds;auto. *)
  (* eauto. *)
  (* eauto. *)
  (* eauto. *)
  (* auto. *)
  (* pauto. *)
  (* intros. *)
  (* sep auto. *)
  (* intros. *)
  (* sep auto. *)
  (* hoare unfold. *)

  (* lets Hz:xx H7. *)
  (* inverts H7. *)


  (* lets Hx:tickstep_exists' H. *)
  
  (* mytac. *)
  (* unfold timetick. *)


  (* hoare abscsq. *)
  (* apply noabs_oslinv. *)
  (* apply absimp_timetick;eauto. *)
  (* pauto. *)

  unfold timetick.
  rewrite isrupd_true_false.


  (* lets Hx:tcbls_rtbl_timetci_update_decompose H18;mytac. *)
  (* eapply backward_rule1. *)
  (* intros. *)
  (* sep_lifts_trms_in H7 tcbdllseg. *)
  (* sep lift 13%nat in H7. *)
  (* lets Hx:tcbls_rtbl_timetci_update_tls_split H13 H10 H7. *)
  (* exact Hx. *)

  (* lets Hx: tcbls_rtbl_timetci_update_rgrp_vint H18. *)
  (* mytac. *)
  (* lets Hx: timetick_update_prop H8 H9 H11 H12 H18;eauto. *)
  (* destruct H13. *)
  (* destruct a;subst. *)
  (* inverts e0. *)
  (* simpl in H15. *)
  (* subst. *)
  (* instantiate (1:=v'36). *)
  (* instantiate (2:=(Vptr v'24)). *)
  (* simpl app. *)
  (* apply TcbMod.join_emp_eq in H2;subst. *)
  (* eauto. *)
  (* eapply TCBList_merge_prop;eauto. *)
  (* mytac;subst. *)
  (* unfolds;auto. *)

  (* mytac. *)

  (* lets Hy:tcbld_rtbl_timetci_update_tcbdllflag H18. *)
  (* eapply backward_rule1 with ([| R_Prio_No_Dup v'36 |] **EX x8 : val, *)
  (*    tcbdllseg (Vptr v'24) Vnull x8 (Vptr v'46) x1 ** *)
  (*    tcbdllseg (Vptr v'46) x8 v'32 Vnull (x2 :: x3) ** *)
  (*     <|| END None;; (isched;; END None ?? END None) ||>  ** *)
  (*    HECBList x0 ** *)
  (*    HTCBList x ** *)
  (*    HTime (v'30 +ᵢ  Int.one) ** *)
  (*    HCurTCB v'46 ** *)
  (*    Aisr (isrupd ir 0%nat false) ** *)
  (*    Aie false ** *)
  (*    Ais (0%nat :: v'23) ** *)
  (*    Acs nil ** *)
  (*    GV OSTCBList @ os_ucos_h.OS_TCB ∗ |-> Vptr v'24 ** *)
  (*    GV OSEventList @ os_ucos_h.OS_EVENT ∗ |-> v'40 ** *)
  (*    evsllseg v'40 Vnull v'43 v'42 ** *)
  (*    GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-r-> Vptr v'46 ** *)
  (*    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'33 ** *)
  (*    GV OSRdyGrp @ Int8u |-> Vint32 x7 ** *)
  (*    GV OSTime @ Int32u |-> Vint32 (v'30 +ᵢ  Int.one) ** *)
  (*    p_local OSLInv v'46 (logic_val (V$ 1) :: nil) ** *)
  (*    AOSEventFreeList v' ** *)
  (*    AOSQFreeList v'0 ** *)
  (*    AOSQFreeBlk v'1 ** *)
  (*    AOSMapTbl ** *)
  (*    AOSUnMapTbl ** *)
  (*    AOSTCBPrioTbl v'4 v'28 v'36 v'15 ** *)
  (*    AOSIntNesting ** *)
  (*    AOSTCBFreeList v'16 v'17 ** *)
  (*    AGVars ** *)
  (*    tcbdllflag (Vptr v'24) (x1++x2::x3) ** A_dom_lenv nil). *)
  (* intros. *)
  
  (* unfold AOSTCBPrioTbl in H26. *)
  (* unfold R_PrioTbl_P in H26. *)
  (* sep auto. *)
  (* sep lift 3%nat. *)
  (* sep lift 3%nat in H26. *)
  (* eapply tcbdllflag_hold. *)
  (* eauto. *)
  (* eauto. *)
  (* destructs H31;auto. *)
  (* hoare_split_pure_all. *)
  (* rename H26 into Hnodup. *)

  (* lets Hx:timetick_tcblist_p H18 H3 H4 H6 Hnodup. *)
  (* eapply tcbls_rtbl_timetci_update_len_eq;eauto. *)
  (* clear -H13. *)
  (* destruct H13;mytac;subst. *)
  (* inverts H0;simpl;auto. *)
  (* unfolds. *)
  (* destruct v'25;tryfalse. *)
  (* unfolds in H1;auto. *)
  (* auto. *)
  
  (* mytac. *)

  unfold AOSIntNesting.

  (* hoare abscsq. *)
  (* eapply noabs_oslinv. *)
  (* eapply absinfer_seq_end;eauto. *)
  (* go. *)
  (* go. *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, oscurt, dllseg, tcbdllseg, Aisr, Aie, Ais, Acs).
  unfold AOSRdyTblGrp.
  unfold AOSRdyGrp.
  unfold AOSRdyTbl.
  hoare forward.
  instantiate (1:= A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel 1%nat 1%nat.
  apply disj_split.
  left.
  unfold invlth_isr'.
  assert (leb 1 0 = false) by auto.
  rewrite H12.  
  clear H12.
  
  sep normal.
  sep eexists.
  sep_lifts_trms (AOSTCBList', AOSTCBFreeList', p_local).
  (* sep lifts (9::10::20::nil)%nat. *)
  apply inv_change_aux.
  unfold AOSTCBList.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTime.
  unfold AOSIntNesting.
  unfold AECBList in *.
  unfold AOSTCBPrioTbl in *.
  unfold AOSIntNesting.
  sep pauto.
  sep cancel tcbdllflag.    
  sep auto.

  { auto. }
  { auto. }
  (* { auto. } *)
  { eauto. }
  { eauto. }
  { auto. }
  { auto. }

  (* eapply tickstep_rh_tcblist_ecblist_p;eauto. *)
  (* pauto. *)
  (* eapply tickstep_r_priotbl_p;eauto. *)
  (* eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p with (a:=(v'25 ++ v'26 :: v'27));eauto. *)
 
  (* destruct H13. *)
  (* destruct a;subst. *)
  (* inverts e0. *)
  (* simpl in H15. *)
  (* subst. *)
  (* instantiate (2:=Vptr v'24). *)
  (* simpl app. *)
  (* apply join_emp_eq in H2; rewrite H2 in H16. *)
  (* eauto. *)
  (* eapply TCBList_merge_prop;eauto. *)
  (* mytac;subst. *)
  (* unfolds;auto. *)
  (* eapply imp_rl_priotbl_p;eauto. *)

  (* destruct H13. *)
  (* destruct a;subst. *)
  (* inverts e0. *)
  (* simpl in H15. *)
  (* subst. *)
  (* instantiate (2:=Vptr v'24). *)
  (* simpl app. *)
  (* apply join_emp_eq in H2;subst. *)
  (* eauto. *)
  (* eapply TCBList_merge_prop;eauto. *)
  (* mytac;subst. *)
  (* unfolds;auto. *)
  (* eauto. *)
  (* eauto. *)
  (* auto. *)
  (* eapply tickstep_ecblist_p with (htls:=v'36) (ltls1:=v'25);eauto. *)
  (* unfolds. *)
  (* destruct v'25;eauto. *)
  (* destruct H13;mytac. *)
  (* inverts H35;auto. *)
  (* tryfalse. *)
  (* destruct H13;mytac;tryfalse. *)
  (* unfold V_OSTCBNext;auto. *)

  unfolds;eauto.
  split;unfold INUM;auto.
  intros.
  lia.
  clear -H5.
  unfold isr_is_prop in *.
  intros.
  apply H5 in H.
  unfold isrupd in *.
  destruct (beq_nat 0 x);auto.
  go.
  
  intros.
  get_hsat Hsat. 
  sep destruct Hsat.
  sep split in Hsat.
  destruct Hsat.
  sep auto.
  get_hsat Hsat. 
  sep split in Hsat.
  unfolds in Hsat;tryfalse.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  intros.
  get_hsat Hsat. 
  apply disj_split in Hsat.
  destruct Hsat.
  exact H6.
  get_hsat Hsat.
  sep normal in Hsat.
  sep split in Hsat.
  simpl in Hsat;tryfalse.
  hoare unfold.
  inverts H4.
  unfold OSTickISR.
  inverts H7.
  eapply iret_rule'.
  intros.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat Adisj.
  (* sep lift 6%nat in H27. *)
  apply disj_split in Hsat.
  destruct Hsat.
  unfold IRINV.
  sep normal.
  sep_lifts_trms Adisj.
  (* sep lift 5%nat. *)
  apply disj_split.
  right.
  unfold iret_ieoff.
  sep normal.
  get_hsat Hsat. 
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  exists (0%nat :: v'26) (0%nat). 
  eapply xxx;eauto.
  apply xxxx;auto.
  unfold invlth_isr.
  unfold starinv_isr.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold I.
  unfold getinv.
  sep normal.
  exists (isrupd v'24 0%nat false). 
  apply disj_split.
  right.
  sep normal.
  apply xxxxx;auto.
  assert (s |= OSInv ** p_local OSLInv ct (logic_val (V$ 1) :: v'29) ** Aemp).
  {
    unfold OSInv.
    unfold A_isr_is_prop.
    unfold invlth_isr' in Hsat.
    assert (leb 1 0 = false) by auto.
    rewrite H17 in Hsat.
    sep normal in Hsat;sep destruct Hsat;sep split in Hsat.
    sep normal.
    sep eexists.
    sep split.
    sep cancel p_local.
    apply astar_r_aemp_intro in Hsat.
    sep normal in Hsat.
    exact Hsat.
    eauto.
    eauto.
    auto.
    auto.
  }
  sep split;auto.
  sep cancel OSInv.
  sep auto.
  get_hsat Hsat. 
  sep split in Hsat.
  tryfalse. 

  
  (*****************current task dead***********************)
  hoare unfold.
  unfold AOSTCBList'.
  hoare_lifts_trms_pre Adisj.
  (* hoare lift 9%nat pre. *)
  eapply backward_rule1.
  intros.
  apply disj_split in H0.
  destruct H0.
  unfold p_local in H0.
  unfold CurTid in H0.
  sep normal in H0.
  sep destruct H0.
  unfold tcbdllseg in H0.
  unfold tcbdllflag in H0.
  sep_lifts_skp_in H0 ((OSTCBCur, _N_ 1), (OSTCBCur, _N_ 0)).
  (* sep lifts (4::1::nil)%nat in H0. *)
  sep split in H0.
  destruct H1;subst.
  eapply read_only_merge_vptr in H0.
  destruct H0;subst v'13.
  sep_lifts_skp_in H0 ((dllseg, _N_ 0), (dllseg, _N_ 1), dllsegflag, OSLInv).
  (* sep lifts (3::4::5::23::nil)%nat in H0. *)
  apply task_del_noexists in H0.
  unfolds in H0;false.
  exact H0.
  hoare_assert_pure (v'13=ct).
  {
    unfold p_local in H0.
    unfold CurTid in H0.

    sep normal in H0.
    sep destruct H0.
    sep split in H0.
    destruct H1;subst.
    sep_lifts_skp_in H0 ((OSTCBCur, _N_ 0), (OSTCBCur, _N_ 1)). 
    (* sep lifts (1::3::nil)%nat in H0. *) 
    eapply read_only_merge_vptr in H0. 
    destruct H0;subst v'13.
    auto.
  }
  hoare_lifts_trms_pre (Aop, Aisr, Aie, Ais, Acs, A_isr_is_prop).
  (* hoare lifts (20::21::24::22::23::19::nil)%nat pre. *)
  eapply seq_rule.
  eapply eoi_ieoff_rule'.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  instantiate (1:=0%nat).
  rewrite Int.unsigned_repr.
  simpl.
  auto.
  rewrite max_unsigned_val.
  lia.
  intros.
  sep_lifts_trms_in H0 (Aisr, Ais, A_isr_is_prop). 
  (* sep lifts (1::3::5::nil)%nat in H0. *)
  apply a_isr_is_prop_split in H0.  
  unfold OSTickISR in H0.
  sep_lifts_trms_in H0 (Aisr, Aie).
  (* sep lifts (1::3::nil)%nat in H0. *)
  exact H0.
  apply GoodI_I.  (*Good I*)
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  unfold tcblist.
  go.
  
  unfold AOSTime.
  unfold tcblist.
  hoare unfold.
  unfold tcbdllseg at 1.
  hoare_assert_pure (isptr v'3).
  {
    sep lift 3%nat in H2.
    eapply dllseg_head_isptr;eauto.
  }
  pure intro.
  unfold isptr in H2.
  destruct H2;tryfalse.
  destruct H2.
  eapply backward_rule1.
  intros.
  (* sep lift 3%nat  in H3. *)
  (* eapply tcbdllseg_split. *)
  (* unfold tcbdllseg. *)
  subst v'3.
  eauto.
  hoare unfold.
  (* lets Hx: OSQPostPure.TCBList_P_Split H0. *)
  (* mytac. *)
  (* assert (x0= Vptr v'15). *)
  (* unfolds in H2. *)
  (* destruct v'7. *)
  (* inverts H2;auto. *)
  (* destruct H3;mytac;tryfalse;auto. *)
  (* destruct H3;mytac;tryfalse;auto. *)
  (* unfolds in H2. *)
  (* rewrite H2 in H8;inverts H8;auto. *)
  (* subst x0. *)
  (* clear H0. *)
  (* hoare forward. *)
  (* sep cancel p_local. *)
  (* sep cancel Aisr. *)
  (* sep cancel Aie. *)
  (* sep cancel Acs. *)
  (* sep cancel Ais. *)
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel AECBList. *)
  (* sep cancel AOSRdyTblGrp. *)
  (* exact H0. *)
  (* unfolds;auto. *)
  (* eauto. *)
  (* eauto. *)
  (* eauto. *)
  (* auto. *)
  (* unfold TCB_Not_In,tcbdllflag. *)
  (* go. *)
  (* apply GoodFrm_dllsegflag. *)
  (* intros. *)
  (* sep auto. *)
  (* sep auto. *)
  (* hoare unfold. *)
  (* inverts H0. *)

  (* lets Hx:tickstep_exists' H. *)
  
  (* mytac. *)
  (* unfold timetick. *)

  (* hoare abscsq. *)
  (* apply noabs_oslinv. *)
  (* apply absimp_timetick;eauto. *)
  (* pauto. *)
  rewrite isrupd_true_false.

  (* lets Hx:tcbls_rtbl_timetci_update_decompose H18;mytac. *)
  (* eapply backward_rule1. *)
  (* intros. *)
  (* sep lift 13%nat in H10. *)

  (* lets Hx:tcbls_rtbl_timetci_update_tls_split H13 H22 H10. *)
  (* exact Hx. *)
  (* lets Hx: tcbls_rtbl_timetci_update_rgrp_vint H18. *)
  (* mytac. *)
  (* lets Hx: timetick_update_prop H8 H9 H11 H12 H18;eauto. *)
  (* destruct H13. *)
  (* destruct a;subst. *)
  (* inverts e0. *)
  (* simpl in H15. *)
  (* subst. *)
  (* instantiate (3:=Vptr v'21). *)
  (* simpl app. *)
  (* apply TcbMod.join_emp_eq in H5; rewrite H5 in H16. *)
  (* eauto. *)
  (* eapply TCBList_merge_prop;eauto. *)
  (* mytac;subst. *)
  (* unfolds;auto. *)
  (* mytac. *)
  (* lets Hy:tcbld_rtbl_timetci_update_tcbdllflag H18. *)

  (* eapply backward_rule1 with ([| R_Prio_No_Dup v'33 |] **EX x8 : val, *)
  (*    tcbdllseg (Vptr v'21) Vnull x8 (Vptr v'43) x1 ** *)
  (*    tcbdllseg (Vptr v'43) x8 v'29 Vnull (x2 :: x3) ** *)
  (*     <|| END None;; (isched;; END None ?? END None) ||>  ** *)
  (*    HECBList x0 ** *)
  (*    HTCBList x ** *)
  (*    HTime (v'27 +ᵢ  Int.one) ** *)
  (*    HCurTCB ct ** *)
  (*    Aisr (isrupd ir 0%nat false) ** *)
  (*    Aie false ** *)
  (*    Ais (0%nat :: v'20) ** *)
  (*    Acs nil ** *)
  (*    GV OSTCBList @ os_ucos_h.OS_TCB ∗ |-> Vptr v'21 ** *)
  (*    GV OSEventList @ os_ucos_h.OS_EVENT ∗ |-> v'37 ** *)
  (*    evsllseg v'37 Vnull v'40 v'39 ** *)
  (*    GV OSTCBCur @ os_ucos_h.OS_TCB ∗ |-r-> Vptr ct ** *)
  (*    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'30 ** *)
  (*    GV OSRdyGrp @ Int8u |-> Vint32 x7 ** *)
  (*    GV OSTime @ Int32u |-> Vint32 (v'27 +ᵢ  Int.one) ** *)
  (*    p_local OSLInv ct (logic_val (V$ 0) :: nil) ** *)
  (*    TCB_Not_In (Vptr ct) (Vptr v'21) (v'22 ++ v'23 :: v'24) ** *)
  (*    AOSEventFreeList v' ** *)
  (*    AOSQFreeList v'0 ** *)
  (*    AOSQFreeBlk v'1 ** *)
  (*    AOSMapTbl ** *)
  (*    AOSUnMapTbl ** *)
  (*    AOSTCBPrioTbl v'4 v'25 v'33 v'16 ** *)
  (*    AOSIntNesting ** *)
  (*    AOSTCBFreeList' (Vptr ct) v'18 ct v'33 ** AGVars **  *)
  (*    tcbdllflag (Vptr v'21) (x1++x2::x3) ** A_dom_lenv nil). *)
  (* intros. *)
  
  (* unfold AOSTCBPrioTbl in H27. *)
  (* unfold R_PrioTbl_P in H27. *)
  (* sep auto. *)
  (* sep lift 3%nat. *)
  (* sep lift 3%nat in H27. *)
  (* eapply tcbdllflag_hold. *)
  (* eauto. *)
  (* eauto. *)
  (* destructs H32;auto. *)
  (* hoare_split_pure_all. *)
  (* rename H27 into Hnodup. *)
  (* lets Hx:timetick_tcblist_p H18 H15 H16 H0 Hnodup. *)
  (* eapply tcbls_rtbl_timetci_update_len_eq;eauto. *)
  (* auto. *)
  (* auto. *)
  (* mytac. *)
  unfold AOSIntNesting.

  (* hoare abscsq. *)
  (* eapply noabs_oslinv. *)
  (* eapply absinfer_seq_end;eauto. *)
  (* go. *)
  (* go. *)

  unfold timetick.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, ostmid, oscurt,
                         Aisr, Aie, Ais, Acs).
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  hoare forward.
  instantiate (1:= A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel 1%nat 1%nat.
  apply disj_split.
  left.
  unfold invlth_isr'.
  assert (leb 1 0 = false) by auto.
  rewrite H10.
  clear H10.
  instantiate (1:=lg').
  instantiate (1:=V$ 0).
  unfold AOSTCBList'.
  sep normal.
  sep eexists.
  sep_lifts_trms Adisj.
  (* sep lift 9%nat. *)
  apply disj_split.
  right.
  unfold AOSTCBFreeList'.
  sep normal.
  sep eexists.
  sep_lifts_trms Adisj.
  (* sep lift 17%nat. *)
  apply disj_split.
  right.
  get_hsat Hsat. 
  unfold AOSTCBFreeList' in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat Adisj.
  (* sep lift 24%nat in H30. *)
  apply disj_split in Hsat.
  destruct Hsat.
  get_hsat Hsat.
  unfold TCBFree_Not_Eq in Hsat.
  sep normal in Hsat.
  sep split in Hsat.
  tryfalse.
  instantiate (8:=v'8).
  unfold tcblist.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTime.
  unfold AOSIntNesting.
  unfold AECBList in *.
  unfold AOSTCBPrioTbl in *.
  unfold TCB_Not_In in *.
  sep pauto.
  
  split; eauto.

  (* eapply tcbfree_eq_tick_hold;eauto. *)
  (* sep cancel 1%nat 1%nat. *)
  (* eapply inv_prop.tcbdllseg_compose;eauto. *)
  (* eapply tickstep_rh_tcblist_ecblist_p;eauto. *)
  (* pauto. *)
  (* eapply tickstep_r_priotbl_p;eauto. *)
  (* eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p with (a:=(v'22 ++ v'23 :: v'24));eauto. *)
 
  (* destruct H13. *)
  (* destruct a;subst. *)
  (* inverts e0. *)
  (* simpl in H15. *)
  (* subst. *)
  (* instantiate (2:=Vptr v'21). *)
  (* simpl app. *)
  (* apply TcbMod.join_emp_eq in H14; rewrite H14 in H16. *)
  (* eauto. *)
  (* eapply TCBList_merge_prop;eauto. *)
  (* mytac;subst. *)
  (* unfolds;auto. *)
  (* eapply imp_rl_priotbl_p;eauto. *)

  (* destruct H13. *)
  (* destruct a;subst. *)
  (* inverts e0. *)
  (* simpl in H15. *)
  (* subst. *)
  (* instantiate (2:=Vptr v'21). *)
  (* simpl app. *)
  (* apply TcbMod.join_emp_eq in H5; rewrite H5 in H16. *)
  (* eauto. *)
  (* eapply TCBList_merge_prop;eauto. *)
  (* mytac;subst. *)
  (* unfolds;auto. *)
  (* split;try eexists;eauto. *)

  (* eapply not_in_tcblist_tick_hold;eauto. *)

  (* eapply OSQPostPure.TCBList_P_Combine;eauto. *)

  (* eapply get_lasr_tcb_ptr_tick_hold;eauto. *)
  
  (* eapply tickstep_ecblist_p with (htls:=v'33) (ltls1:=v'22);eauto. *)
  unfolds;auto.
  split.
  unfold INUM;auto.
  intros.
  lia.
  clear -H4.
  unfold isr_is_prop in *.
  intros.
  apply H4 in H.
  unfold isrupd in *.
  destruct (beq_nat 0 x);auto. 
  go.
  intros.
  get_hsat Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  destruct Hsat.
  sep auto.
  get_hsat Hsat.
  sep split in Hsat.
  simpl in Hsat;tryfalse.
  intros.
  sep auto.
  hoare unfold.
  inverts H2.
  eapply backward_rule1.
  intros.
  get_hsat Hsat.
  apply disj_split in Hsat.
  destruct Hsat.
  exact H2.
  get_hsat Hsat.
  sep normal in Hsat.
  sep split in Hsat.
  unfolds in Hsat;tryfalse.
  eapply iret_rule'.
  intros.
  get_hsat Hsat.
  sep normal in Hsat.
  sep lift 8%nat in Hsat.
  apply disj_split in Hsat.
  destruct Hsat.
  unfold IRINV.
  sep normal.
  sep_lifts_trms Adisj.
  apply disj_split.
  right.
  unfold iret_ieoff.
  sep normal.
  get_hsat Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  exists (0%nat :: v'21) (0%nat). 
  eapply xxx;eauto.
  apply xxxx;auto.
  unfold invlth_isr.
  unfold starinv_isr.
  rewrite NPeano.Nat.sub_0_r in *.
  unfold I.
  unfold getinv.
  sep normal.
  exists (isrupd v'13 0%nat false).
  apply disj_split.
  right.
  sep normal.
  apply xxxxx;auto.
  assert (s |= OSInv ** p_local OSLInv ct (logic_val (V$ 0) :: v'24) ** Aemp).
  {
    unfold OSInv.
    unfold A_isr_is_prop.
    unfold invlth_isr' in Hsat.
    assert (leb 1 0 = false) by auto.
    rewrite H15 in Hsat.
    sep normal in Hsat;sep destruct Hsat;sep split in Hsat.
    sep normal.
    sep eexists.
    sep split.
    sep cancel p_local.
    apply astar_r_aemp_intro in Hsat.
    sep normal in Hsat.
    exact Hsat.
    eauto.
    eauto.
    auto.
    auto.
  }
  sep split;auto.
  sep cancel OSInv.
  sep auto.
  sep split in H2.
  tryfalse.
Qed.

