Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import taskcreate_pure.
Require Import protect.
Require Import Lia.
Require Import os_task.

Require Import obj_common. 

Require Import seplog_tactics. 
Require Import seplog_pattern_tacs.

Require Import objauxvar_lemmas.
Require Import objaux_pure.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 

Theorem cast_rv_tptr :
  forall s e v t1 t2,
    s |= Rv e @ (Tptr t1) == v ->
    rule_type_val_match (Tptr t1) v = true ->
    s |= Rv (ecast e (Tptr t2)) @ (Tptr t2) == v.
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  simpl.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Theorem addrof_gvar_rv :
  forall s x t l P,
    s |= A_notin_lenv x ** G& x @ t == l ** P ->
    s |= Rv (eaddrof (evar x)) @ Tptr t == Vptr l.
Proof.
  intros.
  destruct s as [[]].
  destruct t0 as [[[[[]]]]].
  simpl in *; seplog_tactics.DeprecatedTactic.mytac.
  unfold get in *; simpl in *.
  lets H100 : EnvMod.nindom_get H3.
  rewrite H100.
  rewrite H8.
  destruct l.
  simpl in H10.
  inverts H10.
  rewrite <- Int.unsigned_zero in H1.
  apply unsigned_inj in H1.

  subst.
  auto.
  lets H100 : EnvMod.nindom_get H3.
  unfold get in *; simpl in *.
  rewrite H100.
  rewrite H8.
  auto.
  intro.
  inverts H.
Qed.

Lemma R_PrioTbl_P_update_vhold :
  forall i v'5 v'14 v'17,
    Int.unsigned i < 64 ->
    R_PrioTbl_P v'5 v'14 v'17 ->
    nth_val' (Z.to_nat (Int.unsigned i)) v'5 = Vnull ->
    R_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned i)) v'5 (Vptr v'17)) v'14 v'17.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  mytac.
  splits.
  {
    intros.

    assert ((Z.to_nat (Int.unsigned i)) =  ∘(Int.unsigned prio) \/
              (Z.to_nat (Int.unsigned i)) <>  ∘(Int.unsigned prio)) by tauto.

    elim H7; intros.
    rewrite H8 in H5.
    eapply nth_upd_eq in H5.
    tryfalse.

    apply H0; auto.   
    eapply nth_upd_neq in H5; eauto.
  }
  {
    intros.
    
    lets aaa: H2 H4.
    mytac; auto.
    
    assert ((Z.to_nat (Int.unsigned i)) =  ∘(Int.unsigned prio) \/
              (Z.to_nat (Int.unsigned i)) <>  ∘(Int.unsigned prio)) by tauto.
    elim H7; intros.
    rewrite H8 in H1.
    apply nth_val_nth_val'_some_eq in H5.
    rewrite H1 in H5.
    inversion H5.
    split; auto.
    eapply nth_upd_neqrev.
    eauto.
    eauto.
  }
  auto.
Qed.

Lemma RL_RTbl_PrioTbl_P_update_vhold :
  forall i v'5 v'11 v'17,
    Int.unsigned i < 64 ->
    RL_RTbl_PrioTbl_P v'11 v'5 v'17 ->
    nth_val' (Z.to_nat (Int.unsigned i)) v'5 = Vnull ->
    RL_RTbl_PrioTbl_P v'11
      (update_nth_val (Z.to_nat (Int.unsigned i)) v'5 (Vptr v'17)) v'17. 
Proof.
  intros.
  unfold RL_RTbl_PrioTbl_P in *.
  intros.

  lets aa : H0 H2 H3.
  mytac.
  eexists; splits; eauto.
  assert ((Z.to_nat (Int.unsigned i)) =  ∘(Int.unsigned p) \/ (Z.to_nat (Int.unsigned i)) <>  ∘(Int.unsigned p)) by tauto.
  elim H7; intros.
  rewrite H8 in H1.
  apply nth_val_nth_val'_some_eq in H5.
  unfold nat_of_Z in H1.
  rewrite H1 in H5.
  inversion H5.

  eapply nth_upd_neqrev.
  eauto.
  eauto.
Qed.


Theorem TaskCreateProof:
  forall  vl p r tid, 
    Some p =
      BuildPreA' os_api OSTaskCreate taskcreapi vl  OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api OSTaskCreate taskcreapi vl  OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSTaskCreate = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  destruct v'.
  2: { hoare_lifts_trms_pre Aop. apply absabort_rule. } 
  hoare unfold. 
  hoare forward.
  math simpls.
  destruct ( Int.ltu ($ OS_LOWEST_PRIO) i); simpl; intro; tryfalse.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskcre_prio_invalid.
  go.
  unfold OS_LOWEST_PRIO in *.
  int auto.
  
  hoare forward.
  hoare forward.
  hoare unfold.
  hoare forward prim.
  hoare normal pre.
  hoare unfold.
  assert (Int.unsigned i < 64).
  {
    clear -H.
    unfold OS_LOWEST_PRIO in *.
    int auto.
    destruct H; simpl in H; tryfalse.
  }
  clear H. 
  assert (rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'3) = true). 
  {
    apply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
    rewrite H8.
    clear -H9; mauto.
    auto.
  } 
  assert (Hisptr: isptr (nth_val' (Z.to_nat (Int.unsigned i)) v'3)).
  {
    simpl in H5. unfold isptr.
    destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'3) eqn: eq1; tryfalse;
      eauto.
  }
  hoare forward.
  math simpls.
  auto.
  unfolds in H.
  destruct ( nth_val' (Z.to_nat (Int.unsigned i)) v'3); tryfalse.
  simpl.
  intro; tryfalse.
  
  simpl.
  destruct a.
  intro; tryfalse.
  instantiate (1 := Afalse).
  
  2: { 
    (* error path *)
    hoare forward.
    hoare unfold.
    hoare abscsq.
    apply noabs_oslinv.

    eapply absimp_taskcre_prio_already_exists.
    go.
    hoare forward prim.
    unfold AOSTCBPrioTbl.
    sep pauto.
    go.
    hoare forward.
  }
    
  (* right path *)
  hoare unfold.
  hoare_assert_pure ( array_type_vallist_match Int8u v'9/\ length v'9 = ∘ OS_RDY_TBL_SIZE ) .
  unfold AOSRdyTblGrp in H13.
  unfold AOSRdyTbl in H13.
  sep normal in H13.
  sep split in H13.
  auto.
  hoare_split_pure_all.
  rename H13 into somehyp.
  protect somehyp.
  
  assert ((nth_val' (Z.to_nat (Int.unsigned i)) v'3) = Vnull).
  {
    remember (nth_val' (Z.to_nat (Int.unsigned i)) v'3).
    
    destruct H.

    auto.
    simpljoin.
    rewrite H in *.
    simpl in *.
    destruct x; simpl in *.
    tryfalse.
  }
  do 3 (mttac val_inj ltac: (fun H => clear H)).
  (* clear H10 H11 H12. *)
  hoare unfold.
  unfold AOSTCBList.
  hoare unfold.
  hoare forward.
  math simpls.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel AOSTCBFreeList.
  sep cancel Aop.
  sep cancel AOSRdyTblGrp.
  sep cancel OSPlaceHolder.
  sep cancel 3%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel p_local.
  eauto.
  { (* RL_RTbl_PrioTbl_P v'9 v'3 v'14 *)
    eauto.
  }
  
  go.
  (* go. *)
  {
    math simpl.
    clear -H9 l.
    unfold OS_LOWEST_PRIO in l.
    int auto.
  }
  go.
  apply retpost_tcbinitpost.

  math simpl.
  clear -H1 H15.
  change Byte.max_unsigned with 255 in H15.
  lia.


  repeat intro.

  get_hsat Hs.
  sep normal in Hs.
  sep destruct Hs.
  sep_lifts_trms_in Hs Adisj.
  (* sep lift 6%nat in H15. *)

  rewrite disj_split in Hs. 
  apply DisjPropE in Hs; destruct Hs. 

  get_hsat Hs.
  sep normal in Hs.
  sep destruct Hs.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  get_hsat Hs.
  sep normal in Hs.
  sep destruct Hs.
  sep eexists.
  sep cancel p_local.
  simpl; auto.

  linv_solver.
  
  hoare unfold.
  hoare_lifts_trms_pre Adisj.
  (* hoare lift 6%nat pre. *)
  eapply backward_rule1.
  intro.
  intros.
  get_hsat Hs.
  eapply disj_star_elim_disj in Hs.
  eauto.
  hoare forward.
  hoare unfold.
  inverts H18. (* logic_val ... = ... *)

  (* no more tcb *)
  hoare forward.
  hoare unfold.
  false.
  change (Int.eq ($ OS_NO_MORE_TCB) ($ OS_NO_ERR)) with false in *.
  simpl in *.
  apply H18; auto.
  hoare unfold.
  
  hoare abscsq.
  apply noabs_oslinv.

  eapply absimp_taskcre_no_more_tcb.
  go.
  
  
  instantiate (1 :=    <|| END Some (V$ OS_NO_MORE_TCB) ||>  **
                               Aisr empisr **
                               Aie true **
                               Ais nil ** Acs nil ** p_local OSLInv tid init_lg **
                               A_dom_lenv
                               ((prio, Int8u)
                                  :: (os_code_defs.pdata, (Void) ∗)
                                  :: (task, (Void) ∗) :: (err, Int8u) :: nil) **
                               LV err @ Int8u |-> (V$ OS_NO_MORE_TCB)  ** LV prio @ Int8u |-> Vint32 i **
                               LV os_code_defs.pdata @ (Void) ∗ |-> x0 ** LV task @ (Void) ∗ |-> x1
              ).
  
  hoare forward prim.
  sep cancel tcbdllflag.
  
  sep cancel A_dom_lenv.
  sep pauto.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  sep pauto.
  sep cancel 3%nat 1%nat.
  
  sep cancel 3%nat 1%nat.
  sep cancel 2%nat 1%nat.
  
  sep cancel AOBJ.
  assumption.
  go.
  go.
  go.
  go.
  go.
  go.

  hoare forward.
  hoare_split_pure_all.
  false.
  clear -H18.
  simpljoin.
  change (Int.eq ($ OS_NO_MORE_TCB) ($ OS_NO_ERR)) with false in *.
  simpl in *.
  apply H; auto.

  (* right path *)
  hoare forward.

  hoare unfold.
  inverts H19.

  hoare forward.
  
  hoare unfold.
  
  2: { 
    hoare unfold.
    false.
    clear -H17.
    change (Int.eq ($ OS_NO_ERR) ($ OS_NO_ERR)) with true in H17.
    simpl in H17; destruct H17; tryfalse.
  }

  hoare abscsq.
  apply noabs_oslinv.
  apply absimp_taskcre_succ.
  go.

  
  hoare_assert_pure (GoodLInvAsrt OSLInv).
  get_hsat Hs.
  unfold p_local in Hs.
  unfold LINV in Hs.
  sep normal in Hs.
  sep split in Hs.
  auto.
  instantiate (1 :=
                 EX x, (
                         POST [OS_SchedPost, nil, x,
                             logic_code (END Some (V$ NO_ERR)) :: logic_val (V$ __Loc_normal) :: logic_val Vnull :: nil, tid] **
                           LV err @ Int8u |-> (V$ OS_NO_ERR) **
                           LV prio @ Int8u |-> Vint32 v'43 **
                           LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
                           LV task @ (Void) ∗ |-> x1 **
                           A_dom_lenv
                           ((prio, Int8u)
                              :: (os_code_defs.pdata, (Void) ∗)
                              :: (task, (Void) ∗) :: (err, Int8u) :: nil)
              )).

  hoare_assert_pure(exists new_tcbmod, TcbJoin v'35 (v'43, rdy) v'12 new_tcbmod).
  {
    unfold TcbJoin.
    eexists.
    eapply map_join_comm.
    
    unfold join; simpl.
    eapply TcbMod.join_sig_set.
    auto.
    intro.
    eapply (join_in_or H11) in H24.
    destruct H23.
    simpljoin.
    unfolds in H27.
    inverts H27.
    destruct H24.
    gen H23.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 16%nat 1%nat.
    eauto.
    eauto.

    gen H23.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 18%nat 1%nat.
    eauto.
    eapply  tcblist_p_hold_for_upd_1.
    eauto.


    simpljoin.
    unfolds in H26. (* tcbls_change_prev_ptr *) 
    inverts H26.

    destruct v'36.
    inverts H28.
    inverts H28.

    destruct H24.
    gen H24.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 16%nat 1%nat.
    eauto.
    eapply  tcblist_p_hold_for_upd_1.
    eauto.

    gen H24.
    eapply sometcblist_lemma.
    instantiate ( 8:= s0).
    sep cancel 13%nat 1%nat.
    sep cancel 18%nat 1%nat.
    eauto.
    eauto.
  }
  
  hoare_split_pure_all.
  simpljoin.

  eapply backward_rule1.
  intro.
  Set Printing Depth 999.
  intros.
 
  instantiate (1 :=
    (<||
       scrt (x1 :: x0 :: Vint32 v'43 :: nil);;
       isched;; END Some (V$ NO_ERR) 
       ||>  ** 
       (
       HECBList v'11 **
       HTime v'13 **
       AOSTCBFreeList v'25 v'26 **
       AOSMapTbl **
       GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
       (update_nth_val (Z.to_nat (Int.unsigned v'43)) v'29 (Vptr v'35)) **
       G& OSPlaceHolder @ Int8u == v'44 **
       PV v'44 @ Int8u |-> v'46 **
       GV OSTCBList @ OS_TCB ∗ |-> Vptr v'35 **
       node (Vptr v'35) v'40 OS_TCB_flag **
       PV get_off_addr v'35 ($ 24) @ Int8u |-r-> (V$ 1) **
       PV get_off_addr v'35 ($ 25) @ char_t |-r-> (V$ os_code_defs.__Loc_normal) **
       PV get_off_addr v'35 ($ 26) @ OS_EVENT ∗ |-r-> Vnull **       
       tcbdllseg v'31 (Vptr v'35) v'33 (Vptr tid) v'37 **
       GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
       tcbdllseg (Vptr tid) v'33 v'34 Vnull v'39 **
       AOSRdyTblGrp
       (update_nth_val (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'27
                       (val_inj
                          (or
                             (nth_val' (Z.to_nat (Int.unsigned (v'43 >>ᵢ $ 3))) v'27)
                             (nth_val' (Z.to_nat (Int.unsigned (v'43&ᵢ$ 7)))
                                       OSMapVallist)))) v'42 **
       p_local OSLInv tid init_lg **
       
       LV err @ Int8u |-> (V$ OS_NO_ERR) **
       AOBJ v'18 v'19 v'11 v'44 v'31 (v'36 ++ v'7 :: v'8) v'17 v' **
       AOSEventFreeList v'17 v' **
       (* AOSQFreeList v'1 ** *)
       (* AOSQFreeBlk v'2 ** *)
       AECBList v'2 v'1 v'11 v'12 **
       AOSUnMapTbl **
       AOSIntNesting **
       AOSTime (Vint32 v'13) **
       AGVars **
       tcbdllflag v'31 (v'36 ++ v'7 :: v'8) **
       atoy_inv' **
       LV prio @ Int8u |-> Vint32 v'43 **
       LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
       LV task @ (Void) ∗ |-> x1 **
       A_dom_lenv
       ((prio, Int8u)
          :: (os_code_defs.pdata, (Void) ∗)
          :: (task, (Void) ∗) :: (err, Int8u) :: nil)
       ) **
       OSLInv v'35 init_lg **
       HTCBList v'12  **
       HCurTCB tid ** 
       OS [ empisr, false, nil, (true::nil)]  
    )).
  match goal with
    H: _ |- _ |= Aop _ ** (?R) ** _ => remember R
  end.
  (* remember ( *)
  (*      HECBList v'13 ** *)
  (*      HTime v'15 ** *)
  (*      AOSTCBFreeList v'24 v'25 ** *)
  (*      AOSMapTbl ** *)
  (*      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) *)
  (*        (update_nth_val (Z.to_nat (Int.unsigned v'42)) v'28 (Vptr v'34)) ** *)
  (*      G& OSPlaceHolder @ Int8u == v'43 ** *)
  (*      PV v'43 @ Int8u |-> v'45 ** *)
  (*      GV OSTCBList @ OS_TCB ∗ |-> Vptr v'34 ** *)
  (*      node (Vptr v'34) v'39 OS_TCB_flag ** *)
  (*      PV get_off_addr v'34 ($ 24) @ Int8u |-r-> (V$ 1) ** *)
  (*      tcbdllseg v'30 (Vptr v'34) v'32 (Vptr tid) v'36 ** *)
  (*      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid ** *)
  (*      tcbdllseg (Vptr tid) v'32 v'33 Vnull v'38 ** *)
  (*      AOSRdyTblGrp *)
  (*        (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26 *)
  (*           (val_inj *)
  (*              (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26) *)
  (*                 (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) *)
  (*                    OSMapVallist)))) v'41 ** *)
  (*      p_local OSLInv tid init_lg ** *)
  (*      LV err @ Int8u |-> (V$ OS_NO_ERR) ** *)
  (*      AOSEventFreeList v'0 ** *)
  (*      AOSQFreeList v'1 ** *)
  (*      AOSQFreeBlk v'2 ** *)
  (*      AECBList v'4 v'3 v'13 v'14 ** *)
  (*      AOSUnMapTbl ** *)
  (*      AOSIntNesting ** *)
  (*      AOSTime (Vint32 v'15) ** *)
  (*      AGVars ** *)
  (*      tcbdllflag v'30 (v'35 ++ v'9 :: v'10) ** *)
  (*      atoy_inv' ** *)
  (*      LV prio @ Int8u |-> Vint32 v'42 ** *)
  (*      LV os_code_defs.pdata @ (Void) ∗ |-> x0 ** *)
  (*      LV task @ (Void) ∗ |-> x1 ** *)
  (*      A_dom_lenv *)
  (*        ((prio, Int8u) *)
  (*         :: (os_code_defs.pdata, (Void) ∗) *)
  (*         :: (task, (Void) ∗) :: (err, Int8u) :: nil)). *)

  sep_lifts_trms (Aisr, Ais).
  (* sep lifts (6::8:: nil)%nat. *)
  eapply elim_a_isr_is_prop.

  sep pauto.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel A_isr_is_prop.
  sep cancel Aop.
  sep_lifts_trms_in H26 (Aabsdata curtid).
  (* sep cancel (Aabsdata abstcblsid). *)
  sep cancel (Aabsdata absecblsid).
  (* sep cancel (Aabsdata curtid). *)
  do 8 sep cancel 3%nat 1%nat. 
  repeat sep cancel 6%nat 4%nat.
  sep_lifts_trms_in H26 (flag_off, loc_off, ptr_off, Aabsdata abstcblsid).
  (* repeat sep cancel 6%nat 4%nat. *)
  sep cancel 1%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 3%nat 1%nat.
  unfold OSLInv.
  sep pauto.
  unfold init_lg.
  go.
  unfolds. left; auto.
  unfolds. left; auto.
  unfolds. left; auto.
  
  unfold scrt.
  
  eapply seq_rule.
  
  
   
  eapply cre_rule.
  assumption.
  go.
  (* { *)
  (* unfold p_local. *)
  (* go. *)
  (* unfold CurTid. *)
  (* go. *)
  (* unfold LINV. *)
  (* go. *)
  (* unfold OSLInv. *)
  (* go. *)
  (* } *)
  exact H21.
  {
    clear -H4.
    unfolds in H4.
    simpljoin.
    unfolds.
    eauto.
  }
  {
    intro.
    intros.
    split.
    sep get rv.
    clear -H3.
    pauto.
    split.
    sep get rv.
    clear -H2.
    pauto.
    split.
    sep get rv.
    math simpls.
    apply len_lt_update_get_eq.
    rewrite H8.
    bsimplr.
    assumption.
    unfold CurLINV.
    unfold p_local in H26.
    sep pauto.
    sep cancel LINV.
    simpl; auto.
  } 
  eapply backward_rule1.
  intro; intros.
  get_hsat Hs.
  match type of Hs with
    _ |= Aop _ ** (?R) ** _ => remember R
  end.
  (* remember ( *)
  (*      HECBList v'13 ** *)
  (*      HTime v'15 ** *)
  (*      AOSTCBFreeList v'24 v'25 ** *)
  (*      AOSMapTbl ** *)
  (*      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) *)
  (*        (update_nth_val (Z.to_nat (Int.unsigned v'42)) v'28 (Vptr v'34)) ** *)
  (*      G& OSPlaceHolder @ Int8u == v'43 ** *)
  (*      PV v'43 @ Int8u |-> v'45 ** *)
  (*      GV OSTCBList @ OS_TCB ∗ |-> Vptr v'34 ** *)
  (*      node (Vptr v'34) v'39 OS_TCB_flag ** *)
  (*      PV get_off_addr v'34 ($ 24) @ Int8u |-r-> (V$ 1) ** *)
  (*      tcbdllseg v'30 (Vptr v'34) v'32 (Vptr tid) v'36 ** *)
  (*      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid ** *)
  (*      tcbdllseg (Vptr tid) v'32 v'33 Vnull v'38 ** *)
  (*      AOSRdyTblGrp *)
  (*        (update_nth_val (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26 *)
  (*           (val_inj *)
  (*              (or (nth_val' (Z.to_nat (Int.unsigned (v'42 >>ᵢ $ 3))) v'26) *)
  (*                 (nth_val' (Z.to_nat (Int.unsigned (v'42&ᵢ$ 7))) *)
  (*                    OSMapVallist)))) v'41 ** *)
  (*      p_local OSLInv tid init_lg ** *)
  (*      LV err @ Int8u |-> (V$ OS_NO_ERR) ** *)
  (*      AOSEventFreeList v'0 ** *)
  (*      AOSQFreeList v'1 ** *)
  (*      AOSQFreeBlk v'2 ** *)
  (*      AECBList v'4 v'3 v'13 v'14 ** *)
  (*      AOSUnMapTbl ** *)
  (*      AOSIntNesting ** *)
  (*      AOSTime (Vint32 v'15) ** *)
  (*      AGVars ** *)
  (*      tcbdllflag v'30 (v'35 ++ v'9 :: v'10) ** *)
  (*      atoy_inv' ** *)
  (*      LV prio @ Int8u |-> Vint32 v'42 ** *)
  (*      LV os_code_defs.pdata @ (Void) ∗ |-> x0 ** *)
  (*      LV task @ (Void) ∗ |-> x1 ** *)
  (*      A_dom_lenv *)
  (*        ((prio, Int8u) *)
  (*         :: (os_code_defs.pdata, (Void) ∗) *)
  (*         :: (task, (Void) ∗) :: (err, Int8u) :: nil)). *)

  sep_lifts_trms_in Hs (Aisr, Ais).
  (* sep lifts (5::7::nil)%nat in H26. *)  
  eapply add_a_isr_is_prop in Hs. 
  subst a.
  eauto.
  

  (***** two part ******)
  destruct H23. (*_ \/ _ *)
  {
    (* part 1 of destruct H23 *)
    (* v'36 = nil /\ *)
    (*     v'37 = v'36 /\ tcbls_change_prev_ptr (v'7 :: v'8) (Vptr v'35) = Some v'39 *)
      simpljoin.

      unfold tcbls_change_prev_ptr in H27.
      inverts H27.

      
      hoare forward prim.
      unfold AOSTCBPrioTbl.
      unfold AOSTCBList.
      sep pauto.
      sep cancel OSPlaceHolder.
      (* sep cancel 1%nat 5%nat. *)
      sep cancel 1%nat 3%nat.
      instantiate (1 :=  (LV err @ Int8u |-> (V$ OS_NO_ERR) **
                            LV prio @ Int8u |-> Vint32 v'43 **
                            LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
                            LV task @ (Void) ∗ |-> x1 **
                            A_dom_lenv
                            ((prio, Int8u)
                               :: (os_code_defs.pdata, (Void) ∗)
                               :: (task, (Void) ∗) :: (err, Int8u) :: nil))).
      sep pauto.
      sep cancel A_dom_lenv.
      10: {
        hoare forward.
        unfold init_lg in H23.
        sep cancel p_local.
        sep cancel Aie.
        sep cancel Ais.
        sep cancel Aisr.
        sep cancel Acs.
        sep cancel Aop.
        eauto.
        unfolds; auto.
        go.
        linv_solver.
        linv_solver.
      }

      sep cancel p_local.
      unfold AECBList in *.
      sep pauto.
      sep cancel 1%nat 1%nat.
      assert (Hpe: v'31 = Vptr tid).
      {
        sep_lifts_trms_in H23 tcbdllseg.
        unfold tcbdllseg at 1 in H23.
        unfold dllseg in H23.
        sep normal in H23.
        sep split in H23.
        auto.
      }
      subst v'31.
      sep cancel 6%nat 2%nat.
      instantiate (1 := (v'40 ::nil ) ++ nil).
      eapply inv_prop.tcbdllseg_compose.
      sep cancel 5%nat 2%nat.
      change (  (((v'40 :: nil) ++ nil) ++ update_nth_val 1 v'7 (Vptr v'35) :: v'8) ) with (v'40 :: update_nth_val 1 v'7 (Vptr v'35) :: v'8) .
      unfold tcbdllseg.
      unfold dllseg.
      instantiate (1:=v'19).
      instantiate (1:=v'18).
      unfold AOBJ.
      unfold AOBJ in H23.
      sep pauto.
      unfold tcbllsegobjaux.
      remember (update_nth_val 1 v'7 (Vptr v'35) :: v'8).
      unfold1 llsegobjaux.
      unfold tcbllsegobjaux in H23. 
      unfold objaux_node.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      sep pauto.
      sep cancel flag_off.
      sep cancel loc_off.
      sep cancel ptr_off.
      instantiate (1:=x3).
      instantiate (1:=x2).
      
      2: {
        change (nil ++ v'7::v'8) with (v'7::v'8) in H23.
        lets H__: llseg_not_indom2 H12 H14 H11 H21 H23; eauto.
        destruct H__ as (_ & Hnin).
        unfolds.
        eapply join_comm.
        eapply join_sig_set'.
        auto.
      }
      2: {
        change (nil ++ v'7::v'8) with (v'7::v'8) in H23.
        lets H__: llseg_not_indom2 H12 H14 H11 H21 H23; eauto.
        destruct H__ as (Hnin & _).
        unfolds.
        eapply join_comm.
        eapply join_sig_set'.
        auto.
      }      
      10: {
        change (nil ++ v'7::v'8) with (v'7::v'8) in H23.
        unfold tcbllsegobjaux in H23.
        sep_lifts_trms_in H23 (llsegobjaux, tcbdllflag).
        lets H__: llseg_not_indom2 H12 H14 H11 H21 H23; eauto.
        destruct H__.
        eapply obj_aux_p_tsk_cre_preserve; eauto.
      }
      
      2: { (* rule_type_val_match OS_EVENT ∗ Vnull = true *) 
        go.
      }
      2: { (* rule_type_val_match char_t (V$ os_code_defs.__Loc_normal) = true *)
        go.
      }
      
      sep_lifts_trms (llsegobjaux).
      instantiate (2:=Vptr tid).
      instantiate (1:=Vptr tid).
      unfold llsegobjaux; fold llsegobjaux.
      change (nil ++ v'7 :: v'8) with (v'7 :: v'8) in H23.
      unfold llsegobjaux in H23; fold llsegobjaux in H23.
      sep normal. exists tid. 
      sep normal in H23.
      sep destruct H23.
      sep split in H23. 
      match goal with H: Vptr tid = Vptr _ |- _ => inverts H end.
      sep pauto.
      sep cancel objaux_node.
      sep cancel llsegobjaux.
      2: eauto.
      2: eauto.
      
      unfold tcbdllflag in H23.
      unfold dllsegflag in *.
      sep destruct H23.
      
      sep pauto.
      {
        unfolds.
        eapply nth_upd_neqrev.
        lia.
        auto.
      }
      {
        unfolds.
        eapply nth_upd_neqrev.
        lia.
        auto.        
      }
      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      }
      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.        
      }
      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      }
      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      }
      {
        mttac objdel_nodup ltac: (fun H => lets H__: objdel_nodup_set_normal_loc_preserve H; eauto).
        lets H_: objdel_nodup_set_null_preserve H__; eauto.
      }
      {
        mttac objcre_nodup ltac: (fun H => lets H__: objcre_nodup_set_normal_loc_preserve H; eauto). 
        lets H_: objcre_nodup_set_null_preserve H__; eauto.        
      }
      
      eapply ecblist_hold_for_add_tcb; eauto.
      
      assert (v'44 <> v'35).
      {
        unfold node in H23.
        sep normal in H23.
        sep destruct H23.
        sep split in H23.
        simpljoin.
        inverts H27.
        intro.
        eapply struct_pv_overlap.
(* ** ac:         Show. *)
(* ** ac:         Show. *)
        rewrite H27 in H23.
        sep lift 4%nat in H23.
        sep lift 2%nat in H23.
        exact H23.
      }
      eapply r_priotbl_p_hold_for_add_tcb; eauto.
      assumption.
(* ** ac:       Print TCBList_P. *)
      instantiate (1:= v'24).
      eapply tcblist_p_hold_for_add_tcb.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.

      clear -somehyp.
      unprotect somehyp.
      tauto.
      
      assumption.
      
      { (* ~ (exists id t, get v'24 id = Some (v'43, t)) *)
        clear -H7 H13 H11.
        unfolds in H7.
        simpljoin.
        intro.
        simpljoin.
        assert (get v'12 x = Some (v'43, x0)).
        {
          unfold get,join in *; simpl in *.
          go.
        }
        
        lets bb: H0 H3.
        simpljoin.
        eapply nth_val_nth_val'_some_eq in H4.
        unfold nat_of_Z in H4.
        rewrite H4 in H13.
        inverts H13.
      }
  
      (* TCBList_P *) 
      instantiate (1:= (sig v'35 (v'43, rdy))). 
      eapply tcblist_p_hold_for_add_tcb''.
      clear -H9.
      int auto.
      clear -somehyp .
      unprotect somehyp.
      tauto.
      clear -somehyp .
      unprotect somehyp.
      tauto.
      {
        instantiate (1 := v'23).
        intro.
        simpljoin.
        assert (get v'12 x = Some (v'43, x2)).
        {
          get_hsat Hs. clear Hs.
          unfold get,join,sig in *; simpl in *.
          go.
        }
        eapply not_in_priotbl_no_priotcb; eauto.
      }
      eauto.
      auto.

      {
        eapply TCBList_P_nil_empty in H12.
        subst v'23.
        clear.
        join auto.
      }

      {
        simpl in H12.
        subst v'23.
        assert (v'24 = v'12).
        {
          clear -H11.
          join auto.
        }
        subst v'12.
        assumption.
      }
      
      { (* RH_CurTCB *) 
        unfolds.
        unfolds in H4.
        simpljoin.
        clear -H4 H21.
        do 2 eexists.
        unfold get in *; simpl in *.
        eapply TcbMod.join_get_get_r.
        exact H21.
        eauto.
      }

      { (* RH_TCBList_ECBList_P v'11 v'3 tid *) 
        eapply rh_t_e_p_hold_for_add_tcb.
        eauto.
        eauto.
      }
      go.

  }

  { (* part 2 of "destruct H23" *)
    (* v'36 <> nil /\ *)
    (*     tcbls_change_prev_ptr v'36 (Vptr v'35) = Some v'37 /\ *)
    (*     v'7 :: v'8 = v'39 /\ v'32 = v'33 *)
      assert (exists t, join (sig v'35 (v'43, rdy)) v'23 t).
      {
        clear -H21 H11.
        unfold TcbJoin in H21.
        join auto.
      } 
      simpljoin.

      unfold tcbls_change_prev_ptr in H27.
      destruct v'36.
      clear -H23; tryfalse.
      inverts H27.

      (* EXIT_CRITICAL;ₛ
         OS_Sched (­) *)
      hoare forward prim.
      instantiate (3:=v'8).
      instantiate (3:=v'7).
      instantiate (3:=(v'40::nil) ++ (update_nth_val 1 v (Vptr v'35) :: v'36)). 
      unfold AOSTCBPrioTbl.
      unfold AOSTCBList.
      sep pauto.
      sep cancel 1%nat 6%nat.
      sep cancel 1%nat 3%nat.

      instantiate (1 :=  (LV err @ Int8u |-> (V$ OS_NO_ERR) **
                            LV prio @ Int8u |-> Vint32 v'43 **
                            LV os_code_defs.pdata @ (Void) ∗ |-> x0 **
                            LV task @ (Void) ∗ |-> x1 **
                            A_dom_lenv
                            ((prio, Int8u)
                               :: (os_code_defs.pdata, (Void) ∗)
                               :: (task, (Void) ∗) :: (err, Int8u) :: nil))).
      sep pauto.
      sep cancel A_dom_lenv.
      10 : { 
        hoare forward.
        sep cancel p_local.
        sep cancel Aie.
        sep cancel Ais.
        sep cancel Aisr.
        sep cancel Acs.
        sep cancel Aop.
        eauto.
        unfolds; auto.
        go.
        linv_solver.
        linv_solver.
      }

      assert (Htp_: TCBList_P v'31 ((v :: v'36) ++ (v'7 :: v'8)) v'27 v'12).
      {
        eapply TCBList_merge_prop; eauto.
        sep_lifts_trms_in H27 tcbdllseg.
        lets H__: new_inv.tcbdllseg_last_next_ptr_tcbdllseg H27.
        casetac v'36 (nil: list vallist) Htt Hff.
        -
          subst v'36.
          simpl.
          simpl in H__.
          unfolds.
          rewrite <- H__.
          destruct v.
          simpl in H__; false.
          simpl; auto.
        -
          assert (Hnxte:
                   V_OSTCBNext (last (update_nth_val 1 v (Vptr v'35) :: v'36) nil) = Some (Vptr tid)).
          {
            eapply tcbdllseg_last_nextptr; eauto.  
          }
          rewrite last_remain; auto.
          rewrite last_remain in Hnxte; auto.
      }
      unfold AOBJ.
      unfold AOBJ in H27.
      sep normal.
      sep normal in H27.
      sep destruct H27.
      sep split in H27.
      exists (set x2 v'35 (V$ os_code_defs.__Loc_normal)).
      exists (set x3 v'35 Vnull).
      sep split.
      sep cancel (absobjsid).
      sep cancel AObjs.
      sep cancel p_local.
      change (((v'40 :: nil) ++ update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8) with
        (v'40 :: (update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8) at 1. 
      unfold tcbllsegobjaux.
      unfold llsegobjaux; fold llsegobjaux.
      unfold tcbllsegobjaux in H27.
      sep pauto.
      unfold objaux_node.
      sep normal.
      sep split.
      sep cancel loc_off.
      sep cancel ptr_off.
      sep remember (1%nat::nil).
      instantiate (1:=x3).
      instantiate (1:=x2).
      subst H28.

      2: { (* rule_type_val_match OS_EVENT ∗ Vnull = true *)
        go.
      }
      2: { (* rule_type_val_match char_t (V$ os_code_defs.__Loc_normal) = true *)
        go.
      }
      2: {
        get_hsat Hs.
        lets H__: llseg_not_indom Htp_ H21 Hs.
        unfolds.
        apply join_comm.
        simpljoin.
        eapply lmachLib.mem_join_sig_r; eauto.
      }
      2: {
        get_hsat Hs.
        lets H__: llseg_not_indom Htp_ H21 Hs.
        unfolds.
        apply join_comm.
        simpljoin.
        eapply lmachLib.mem_join_sig_r; eauto.
      }

      sep remember (1%nat :: nil).
      instantiate (1:=v'31).
      subst H28.
      change ((update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8) with
        (update_nth_val 1 v (Vptr v'35) :: (v'36 ++ v'7 :: v'8)).
      change ((v :: v'36) ++ v'7 :: v'8) with (v :: (v'36 ++ v'7 :: v'8)) in H27.
      unfold llsegobjaux; fold llsegobjaux.
      unfold llsegobjaux in H27; fold llsegobjaux in H27.
      sep pauto.
      sep cancel llsegobjaux.
      sep cancel objaux_node.
      2: eauto.
      2: eauto.

      unfold AECBList in *.
      sep pauto.
      sep cancel 1%nat 1%nat.
      sep cancel 4%nat 2%nat.
      eapply inv_prop.tcbdllseg_compose.
      sep cancel 3%nat 2%nat.
      unfold tcbdllseg.
      unfold dllseg.
      sep pauto.
      unfold tcbdllflag.
      change ((v'40 :: nil) ++ update_nth_val 1 v (Vptr v'35) :: v'36) with (v'40 :: update_nth_val 1 v (Vptr v'35) :: v'36) .
      change (((v'40 :: update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8)) with
        (v'40 :: ((update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8)). 
      remember ((update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8). 

      unfold1 dllsegflag.
      sep pauto.
      sep cancel 1%nat 1%nat.
      change  ((update_nth_val 1 v (Vptr v'35) :: v'36) ++ v'7 :: v'8) with  (update_nth_val 1 v (Vptr v'35) :: v'36 ++ v'7::v'8).
      change ((v :: v'36) ++ v'7 :: v'8) with (v :: v'36 ++ v'7 :: v'8) in H27. 
      unfold tcbdllflag in H27.
      unfold dllsegflag in *.
      sep destruct H27.
      
      sep pauto.
      unfolds.
      eapply nth_upd_neqrev.
      lia.
      auto.
      { eauto. }

      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      }

      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      }

      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      } 
      
      eapply ecblist_hold_for_add_tcb; eauto.

      {
        unfolds. eapply nth_upd_neqrev; eauto.
      }

      {
        clear -H18.
        unfolds in H18.
        simpljoin; auto.
      }

      { eauto. }

      {
        mttac objdel_nodup ltac: (fun H => lets H__: objdel_nodup_set_normal_loc_preserve H; eauto).
        lets H_: objdel_nodup_set_null_preserve H__; eauto.  
      }

      {
        mttac objcre_nodup ltac: (fun H => lets H__: objcre_nodup_set_normal_loc_preserve H; eauto). 
        lets H_: objcre_nodup_set_null_preserve H__; eauto.  
      }

      { (* OBJ_AUX_P *)
        unfold tcbllsegobjaux in H27.
        sep_lifts_trms_in H27 (llsegobjaux).
        lets H__: llseg_not_indom Htp_ H21 H27; eauto.
        destruct H__.
        eapply obj_aux_p_tsk_cre_preserve; eauto.        
      }

      { (* v'44 = vhold_addr *)
        auto.
      }
      
      eapply r_priotbl_p_hold_for_add_tcb; eauto.
      {
        unfold node in H27.
        sep normal in H27.
        sep destruct H27.
        sep split in H27.
        simpljoin.
        inverts H29.
        intro.
        eapply struct_pv_overlap.
        rewrite H29 in H27.
        sep lift 4%nat in H27.
        sep lift 2%nat in H27.
        exact H27.
      }
      assumption.
      instantiate (1:= v'24).
      
      assert (exists x, nth_val 1 v'7 = Some x).
      {
        clear -H14.
        unfold1 TCBList_P in H14.
        simpljoin.
        unfolds in H2.
        destruct x2; destruct p.
        simpljoin.
        unfolds in H2.
        destruct v'7.
        inverts H2.
        destruct v'7.
        inverts H2.
        eexists.
        simpl.
        eauto.
      }
      simpljoin.
      erewrite (update_eq v'7).
      
      eapply tcblist_p_hold_for_add_tcb.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      assumption.
      {
        clear -H7 H13 H11.
        unfolds in H7.
        simpljoin.
        intro.
        simpljoin.
        assert (get v'12 x = Some (v'43, x0)).
        {
          unfold get,join in *; simpl in *.
          go.
        }
        
        lets bb: H0 H3.
        simpljoin.
        eapply nth_val_nth_val'_some_eq in H4.
        unfold nat_of_Z in H4.
        rewrite H4 in H13.
        inverts H13.
      }

      eauto.

      
      instantiate (1 := x). 
      eapply tcblist_p_hold_for_add_tcb''.
      clear -H9.
      int auto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      clear -somehyp.
      unprotect somehyp.
      tauto.
      {
        instantiate (1 := v'23).
        intro.
        simpljoin.
        assert (get v'12 x2 = Some (v'43, x3)).
        {
          get_hsat Hs. clear Hs.
          unfold get,join,sig in *; simpl in *.
          go.
        }
        eapply not_in_priotbl_no_priotcb; eauto.
      }
      
      eapply tcblist_p_hold_for_upd_1.
      eauto.
      eauto.
      go.
      clear -H21 H26 H11.
      unfold TcbJoin in H21.
      join auto.
      unfolds.
      unfolds in H4.
      simpljoin.
      clear -H4 H21.
      do 2 eexists.
      unfold get in *; simpl in *.
      eapply TcbMod.join_get_get_r.
      exact H21.
      eauto.

      {
        eapply rh_t_e_p_hold_for_add_tcb.
        eauto.
        eauto.
      }
      go.
  }
  
  (* RETURN err ′ *) 
  hoare forward.
  hoare unfold.
  unfold OS_SchedPost .
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare unfold.
  hoare forward.
  inverts H21.
  eauto.
  inverts H21; eauto.
  
  hoare_split_pure_all.
  false.
  clear -H17.
  int auto.
  destruct H17; tryfalse.

  Grab Existential Variables.
  exact (Afalse).
  exact (Afalse).

Qed.
