
Require Import sem_common.
(* Require Import OSTimeTickPure. *)
(* Require Import OSTimeDlyPure. (* new add *) *)
(* Require Import OSQPostPure. *)
(* Require Import Mbox_common. *)

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

(* new add *)
Lemma struct_type_vallist_match_os_tcb_flag_imp :
  forall vl, struct_type_vallist_match OS_TCB_flag vl ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, 
            vl = v1 :: v2 :: v3 :: v4 :: Vint32 v5 :: Vint32 v6 :: Vint32 v7 :: Vint32 v8 :: Vint32 v9 :: Vint32 v10 :: Vint32 v11 :: nil
             /\ isptr v1 /\ isptr v2 /\ isptr v3 /\ isptr v4
             /\ Int.unsigned v5 <= 65535 /\ Int.unsigned v6 <= 255 /\ Int.unsigned v7 <= 255 /\ Int.unsigned v8 <= 255
             /\ Int.unsigned v9 <= 255 /\ Int.unsigned v10 <= 255 /\ Int.unsigned v11 <= 255.
Proof.
  intros.
  unfold OS_TCB_flag in H.
  struct_type_vallist_match_elim.
  repeat eexists; eauto.
Qed.

Lemma struct_type_vallist_match_os_tcb_flag_getdly :
  forall vl, struct_type_vallist_match OS_TCB_flag vl ->
              exists time, V_OSTCBDly vl = Some (Vint32 time) /\ Int.unsigned time <= 65535.
Proof.
  intros.
  apply struct_type_vallist_match_os_tcb_flag_imp in H.
  do 11 destruct H. destruct H. subst vl. destruct H0 as (_ & _ & _ & _ & Ht & _).
  unfold V_OSTCBDly. simpl. eexists. split; auto.
Qed.

Lemma TCBListP_head_in_tcb':
  forall tcbls tcur tcurl tcblist rtbl prio,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
     exists st, TcbMod.get tcbls tcur = Some (prio, st).
Proof.
  intros.
  funfold H.
  fold TCBList_P in H4.
  inverts H.
  funfold H3.
  destruct x2.
  mytac.
  unfold V_OSTCBPrio, V_OSTCBMsg in *.
  rewrite H in H6. inverts H6.
  unfold TcbJoin in H2.
  unfold join in H2; unfold sig in H2; simpl in H2.
  eexists.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Lemma low_stat_impl_high_stat_sem:
  forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    TcbMod.get tcbls tcur = Some (prio, wait sid).
Proof.
  introv Ht Hp Hvp Hvt Hvs Hvn.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  mytac.
  apply tcbjoin_get_a in H1.
  destruct H2 as (_ & _ & Hrts & _).
  funfold Hrts.
  funfold Hrts.
  unfold WaitTCBblk in Hrts.
  unfold V_OSTCBPrio, V_OSTCBDly, V_OSTCBStat, V_OSTCBEventPtr in Hrts.
  rewrite H7, H5, H4 in Hrts.
  rewrite H1.
  assert ((p, t) = (prio, wait sid)).
  {
    eapply Hrts; try auto.
  }
  inverts H.
  eauto.
Qed.

Lemma low_stat_impl_high_stat_sem':
  forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) (tcbls : TcbMod.map) prio wt sid st,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBEventPtr tcurl = Some (Vptr sid) ->
    TcbMod.get tcbls tcur = Some (prio, st) -> 
    st = wait sid. 
Proof.
  intros.
  lets Hget : low_stat_impl_high_stat_sem H H0 H1 H2 H3.
  lets Hget': Hget H4.
  clear Hget. 
  rewrite H5 in Hget'.
  inverts Hget'.
  auto.
Qed.

Lemma low_stat_impl_high_stat_neq_sem :
  forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) (tcbls : TcbMod.map) st prio, 
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    V_OSTCBStat tcurl <> Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    TcbMod.get tcbls tcur = Some (prio, st) ->
    ~(exists sid, st =wait sid).  
Proof.
  introv Ht.
  pure_auto.
  apply H.
  simpl in Ht.
  mytac.
  inverts H3.
  funfold H6.
  destruct x3.
  mytac.
  apply tcbjoin_get_a in H5.
  rewrite H5 in *.
  destruct H6 as (_ & _ & _ & Hrts).
  funfold Hrts.
  funfold Hrts.
  inverts H1.
  specialize Hrts with (prio0 := prio).
  specialize Hrts with (eid := x).
  pauto.
Qed.

Lemma TCBList_P_rtbl_add_lemma_1a:
  forall ma mb mab mc ma' ma'' p s tid, 
    TcbMod.join ma mb mab ->
    TcbMod.join mc ma' ma ->
    TcbJoin tid (p, s) ma'' ma' ->
    TcbMod.get mb tid = None.
Proof.
  introv Fj1 Fj2 Fs1.
  assert (Hl0: TcbMod.indom ma' tid).
    eapply TcbMod.get_indom.
    apply TcbMod.join_sig_get in Fs1.
    eauto.
  assert (Hl1: TcbMod.indom ma tid).
    eapply TcbMod.indom_sub_indom; eauto.
    TcbMod.solve_map.
  assert (Hl2: TcbMod.disj ma mb).
    TcbMod.solve_map.
  assert (Hl3: ~ TcbMod.indom mb tid).
    eapply TcbMod.disj_indom; eauto.
    TcbMod.solve_map.
  eapply TcbMod.nindom_get; trivial.
Qed.  

Lemma low_stat_impl_high_stat_neq_sem' :
  forall tcur tcurl tcblist2 rtbl tls1 tls2 tcbls st prio,
    TcbMod.join tls1 tls2 tcbls ->
    TCBList_P (Vptr tcur) (tcurl :: tcblist2) rtbl tls2 ->
    V_OSTCBStat tcurl <> Some (Vint32 ($ OS_STAT_SEM)) ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    TcbMod.get tcbls tcur = Some (prio, st) -> 
    ~(exists sid, st =wait sid).
Proof.
  intros.
  lets Hget: TCBListP_head_in_tcb'.
  specializes Hget; eauto.
  destruct Hget as [st'].  
  lets Hget : low_stat_impl_high_stat_neq_sem.
  specializes Hget; eauto. 
  pure_auto.
  apply Hget.
  funfold H0.
  fold TCBList_P in H9.
  inverts H0.
  assert (TcbMod.get tls1 x0 = None).
  {
    destruct x3.
    eapply TCBList_P_rtbl_add_lemma_1a.
    eapply TcbMod.join_comm. eauto.
    2: eauto.
    eapply TcbMod.join_comm.
    apply TcbMod.map_join_emp.
  }
  lets He: TcbMod.map_join_get_none.
  specializes He; eauto.
  rewrite He in *.
  rewrite H3 in H4.
  inverts H4.
  eauto.
Qed.

Lemma neg_priointbl_prionotintbl:
  forall p tbl,
    Int.unsigned p < 64 ->
     array_type_vallist_match Int8u tbl ->
     length tbl = ∘OS_RDY_TBL_SIZE ->
    ~ prio_in_tbl p tbl -> prio_not_in_tbl p tbl.
Proof.
  intros.
  lets Hxxa : prio_rtbl_dec p H0 H1.
  clear - H.
  mauto.
  destruct Hxxa; auto.
  tryfalse.
Qed.

Lemma prio_in_tbl_imp :
  forall p rtbl,
    0 <= Int.unsigned p < 64 ->
    array_type_vallist_match char_t rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    prio_in_tbl p rtbl -> 
    ~(prio_not_in_tbl p rtbl).
Proof.
  introv Hr Harr Hlen Hp.
  unfold prio_in_tbl, prio_not_in_tbl in *.
  lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru p ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  assert (Himp: forall P Q:Prop, (P /\ ~Q) -> ~(P -> Q) ).
  tauto.
  eapply Classical_Pred_Type.ex_not_not_all; exists (p&ᵢ$ 7).
  eapply Classical_Pred_Type.ex_not_not_all; exists (p >>ᵢ $ 3).
  eapply Classical_Pred_Type.ex_not_not_all; exists v.
  eapply Himp.
  split; try auto.
  eapply Himp.
  split; try auto.
  eapply Himp.
  split; try auto.
  assert (v&ᵢ($ 1<<ᵢ(p&ᵢ$ 7)) = $ 1<<ᵢ(p&ᵢ$ 7)).
  eapply Hp; try eauto.
  rewrite H1.
  eapply math_prop_neq_zero2.
  eauto.
Qed.

Lemma prio_not_in_tbl_imp :
  forall p rtbl,
    0 <= Int.unsigned p < 64 ->
    array_type_vallist_match char_t rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    prio_not_in_tbl p rtbl -> 
    ~(prio_in_tbl p rtbl).
Proof.
  introv Hr Harr Hlen Hp.
  unfold prio_in_tbl, prio_not_in_tbl in *.
  lets Hex :   int_usigned_tcb_range Hr.
  destruct Hex as (He1 & He2).
  simpl in Hlen.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0<=Z.to_nat(Int.unsigned (Int.shru p ($ 3))) <8)%nat.
  eapply int8_range_nat; auto.
  lets Hes : n07_arr_len_ex H Harr Hlen.
  destruct Hes as (v & Hes & Hneq).
  assert ( 0 <=Int.unsigned v <256).
  clear -Hneq.
  int auto.
  lets Hea: prio_int_disj H0 He1.
  assert (Himp: forall P Q:Prop, (P /\ ~Q) -> ~(P -> Q) ).
  tauto.
  eapply Classical_Pred_Type.ex_not_not_all; exists (p&ᵢ$ 7).
  eapply Classical_Pred_Type.ex_not_not_all; exists (p >>ᵢ $ 3).
  eapply Classical_Pred_Type.ex_not_not_all; exists v.
  eapply Himp.
  split; try auto.
  eapply Himp.
  split; try auto.
  eapply Himp.
  split; try auto.
  assert (v&ᵢ($ 1<<ᵢ(p&ᵢ$ 7)) = $ 0).
  eapply Hp; try eauto.
  rewrite H1.
  apply not_eq_comm.
  eapply math_prop_neq_zero2.
  eauto.
Qed.

Lemma low_stat_impl_high_stat_wait :
  forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) (tcbls : TcbMod.map) prio wt,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    prio_not_in_tbl prio rtbl ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    False. 
Proof.
  introv Ht Hp Hvp Hvt Hvs Hmt Hlen.
  simpl in Ht.
  mytac.
  inverts H.
  funfold H2.
  destruct x2.
  mytac.
  apply tcbjoin_get_a in H1.
  unfolds in H2.

  destruct H2 as (Hlhrdy & Hhlrdy & Hlhwt & Hhlwt).
  destruct t.
  - unfolds in Hhlrdy.
    specializes Hhlrdy; eauto.
    destruct Hhlrdy as (Hrb & Hvstat).
    unfolds in Hrb.
    simpljoin.
    unfolds in H0. simpljoin.
    lets H__: prio_in_tbl_imp H8; eauto.
    rewrite H in H0. inverts H0.
    auto.
    unfolds in H.
    rewrite H in H6. inverts H6.
    false. 
  - unfolds in Hhlwt.
    unfolds in Hhlwt.
    specializes Hhlwt; eauto.
    simpljoin.
    unfolds in H9.
    rewrite H4 in H9.
    false. 
Qed.

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 

Lemma low_stat_rdy_impl_high_stat :
  forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) (tcbls : TcbMod.map) prio wt,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) ->
    (* (exists msg, TcbMod.get tcbls tcur = Some (prio, wait os_stat_time wt, msg)) \/ *)
    TcbMod.get tcbls tcur = Some (prio, rdy).
Proof.
  introv Ht Ha Hl Hvp Hvt Hvs.
  assert (Hpt: prio_in_tbl prio rtbl \/ prio_not_in_tbl prio rtbl).
  {
    eapply prio_rtbl_dec.
    simpl in Ht.
    mytac.
    inverts H.
    funfold H2.
    destruct x2.
    mytac.
    mttac RL_TCBblk_P ltac: (fun H=> funfold H).
    rewrite H9 in H6.
    inverts H6.
    eauto.
    auto.
    auto.
  }
  destruct Hpt.
  2 : { false. eapply low_stat_impl_high_stat_wait; eauto. }
  simpl in Ht.
  mytac.
  inverts H0.
  funfold H3.
  destruct x2.
  mytac.
  apply tcbjoin_get_a in H2.
  rewrite H2.
  mttac R_TCB_Status_P ltac:(fun H=> destruct H as (Hrts & _ & _ & _)).
  funfold Hrts.
  unfold RdyTCBblk in Hrts.
  unfold V_OSTCBPrio in Hrts.
  rewrite H7 in Hrts.
  assert ((p, t) = (prio, rdy)).
  {
    eapply Hrts; try auto.
  }
  inverts H0.
  eauto.
Qed.

Lemma low_stat_rdy_impl_high_stat' :
  forall (tcur : addrval) (tcurl : vallist) (tcblist : list vallist)
         (rtbl : vallist) (tcbls : TcbMod.map) prio wt st,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    V_OSTCBPrio tcurl = Some (Vint32 prio) ->
    V_OSTCBDly tcurl = Some (Vint32 wt) ->
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) ->
    TcbMod.get tcbls tcur = Some (prio, st) ->
    st = rdy.
Proof.
  intros.
  lets He: low_stat_rdy_impl_high_stat H H0 H1 H2 H3.
  lets He': He H4.
  clear He.
  rewrite H5 in He'.
  inverts He'.
  auto.
Qed.

Ltac l_rew21 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H2 in H1; inverts H1
  end.

Ltac l_rew12 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H1 in H2; inverts H2
  end.

Lemma get_tcb_stat_rdy:
  forall tcur tcurl tcblist rtbl tcbls prio st,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    TcbMod.get tcbls tcur = Some (prio, st) ->
    st = rdy ->
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_RDY)) /\
      V_OSTCBEventPtr tcurl = Some Vnull.
Proof.
  intros.
  funfold H.
  fold TCBList_P in H5.
  inverts H.
  (* destruct x2.  *)
  lets Hget: tcbjoin_get_a H3.
  rewrite H0 in Hget.
  inverts Hget.
  funfold H4.
  funfold H2.
  funfold H2.
  specializes H2; eauto.
  simpljoin.
  split; auto.
  funfold H1.
  l_rew12 (nth_val 5 tcurl).
  specializes H22; eauto.
  subst.
  unfolds. auto.
Qed.   

Lemma get_tcb_stat_sem:
  forall tcur tcurl tcblist rtbl tcbls prio st sid,
    TCBList_P (Vptr tcur) (tcurl :: tcblist) rtbl tcbls ->
    TcbMod.get tcbls tcur = Some (prio, st) ->
    st = wait sid -> 
    V_OSTCBStat tcurl = Some (Vint32 ($ OS_STAT_SEM)) /\
      V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
      prio_not_in_tbl prio rtbl.
Proof.
  intros.
  funfold H.
  fold TCBList_P in H5.
  inverts H.
  destruct x2. 
  lets Hget: tcbjoin_get_a H3.
  rewrite H0 in Hget.
  inverts Hget.  
  funfold H4.
  funfold H2.
  funfold H8.
  funfold  H8.
  assert (Ht: WaitTCBblk tcurl rtbl p /\
                V_OSTCBEventPtr tcurl = Some (Vptr sid) /\
                V_OSTCBStat tcurl = Some (V$ OS_STAT_SEM)) by (eapply H8; eauto).
  unfold WaitTCBblk in *.
  pauto.
Qed.

Lemma RL_TCBblk_P_hold_for_update :
  forall tcurl,
    RL_TCBblk_P tcurl ->
    RL_TCBblk_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)).
Proof.
  intros.
  funfold H.
  unfold RL_TCBblk_P.
  unfold V_OSTCBX,V_OSTCBPrio,V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSTCBStat,V_OSTCBEventPtr in *.
  repeat eexists; 
    try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto);
    try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try eauto.
Qed.

Lemma RdyTCBblk_hold_update :
  forall tcurl rtbl abstcb,
    RdyTCBblk tcurl rtbl abstcb ->
    RdyTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb.
Proof.
  unfold RdyTCBblk.
  unfold V_OSTCBPrio.
  intros.
  splits; 
    try (eapply nth_upd_neqrev; try pauto);
    try (eapply nth_upd_neqrev; try pauto); try pauto.
Qed.

Lemma RdyTCBblk_hold_update':
  forall tcurl rtbl abstcb,
    RdyTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb ->
    RdyTCBblk tcurl rtbl abstcb.
Proof.
  unfold RdyTCBblk.
  unfold V_OSTCBPrio.
  intros.
  destruct H.
  splits; try auto;
    eapply nth_upd_neq; try eapply nth_upd_neq.
  3 : { eauto. } pauto. pauto.
Qed.

Lemma RLH_rdyI_P_hold_update:
  forall tcurl rtbl abstcb,
    RLH_RdyI_P tcurl rtbl abstcb ->
    RLH_RdyI_P  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb.
Proof.
  unfold RLH_RdyI_P.
  unfold V_OSTCBStat,V_OSTCBDly.
  intros.
  apply RdyTCBblk_hold_update' in H0.
  eapply H in H0.
  splits; 
    try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto);
    try (eapply update_nth); try (eapply nth_upd_neqrev; try pauto); try pauto.
Qed.

Lemma RHL_rdyI_P_hold_update:
  forall tcurl rtbl abstcb,
    RHL_RdyI_P tcurl rtbl abstcb ->
    RHL_RdyI_P  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl abstcb.
Proof.
  unfold RHL_RdyI_P.
  unfold V_OSTCBStat,V_OSTCBDly.
  intros.
  eapply H in H0.
  splits; try apply RdyTCBblk_hold_update; 
    try eapply update_nth;
    try eapply nth_upd_neqrev;
    try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma WaitTCBblk_hold_update:
  forall tcurl rtbl prio,
    WaitTCBblk tcurl rtbl prio ->
    WaitTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl prio. 
Proof.
  unfold WaitTCBblk.
  unfold V_OSTCBPrio,V_OSTCBDly.
  intros.
  splits; 
    try (eapply nth_upd_neqrev; try pauto);
    try (eapply nth_upd_neqrev; try pauto); try pauto.
Qed.

Lemma WaitTCBblk_hold_update':
  forall tcurl rtbl prio,
    WaitTCBblk  (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) rtbl prio ->
    WaitTCBblk tcurl rtbl prio. 
Proof.
  unfold WaitTCBblk.
  unfold V_OSTCBPrio,V_OSTCBDly.
  intros.
  destruct H as (H1 & H2).
  splits; try auto;
    eapply nth_upd_neq; try eapply nth_upd_neq.
  3 : { eauto. } pauto. pauto.
Qed.

(* Lemma TCBList_P_hold_for_update_wait : *)
(*   forall tcbls tcur tcurl tcblist rtbl time prio st msg, *)
(*     TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls -> *)
(*     0 <= Int.unsigned prio < 64 -> *)
(*     array_type_vallist_match char_t rtbl -> *)
(*     length rtbl = ∘ OS_RDY_TBL_SIZE -> *)
(*     V_OSTCBDly tcurl = Some (Vint32 time) -> *)
(*     Int.ltu Int.zero time = true -> *)
(*     TcbMod.get tcbls tcur = Some (prio, st, msg) -> *)
(*     TCBList_P (Vptr tcur)  *)
(*       ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist)  *)
(*       rtbl *)
(*       (TcbMod.set tcbls tcur (prio, wait os_stat_time time, msg)). *)
(* Proof. *)
(*   simpl TCBList_P. *)
(*   intros. *)
(*   destruct H as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis'). *)
(*   destruct asbs'. *)
(*   destruct p. *)
(*   exists td' vv' tcblss' (prio, wait os_stat_time time, msg). *)
(*   inverts Hveq'. *)
(*   assert (Hseq: forall td' p t m, sig td' (p,t,m) = TcbMod.sig td' (p,t,m)). *)
(*   unfold sig. unfold TcbMod.sig. *)
(*   pauto. *)
(*   erewrite Hseq in *. *)
(*   assert (Heq1: (prio, st, msg) = (p, t, m)). *)
(*   eapply TcbMod.map_get_unique. *)
(*   eauto. *)
(*   eapply TcbMod.join_sig_get. eauto. *)
(*   inverts Heq1. *)
(*   splits; try auto. *)
(*   unfold V_OSTCBNext in *; *)
(*     try (eapply nth_upd_neqrev; try pauto); *)
(*     try (eapply nth_upd_neqrev; try pauto). *)
(*   unfold TcbMod.join in *. *)
(*   intros. *)
(*   specialize Htcj' with (a:= a). *)
(*   erewrite TcbMod.sig_sem in *. *)
(*   rewrite TcbMod.set_sem in *. *)
(*   pure_auto. *)
(*   (*TCBNode_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY)) *)
(*   rtbl (p, wait os_stat_time time, m) *) *)
(*   destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl'). *)
(*   unfold TCBNode_P. *)
(*   unfold V_OSTCBMsg,V_OSTCBPrio in *. *)
(*   splits; *)
(*     try (eapply nth_upd_neqrev; try pauto); *)
(*     try (eapply nth_upd_neqrev; try pauto). *)
(*   apply RL_TCBblk_P_hold_for_update; auto. *)
(*   lets Hp: prio_rtbl_dec H0 H1 H2. *)
(*   funfold Hrtsl'. *)
(*   unfold R_TCB_Status_P. *)
(*   splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *. *)
(*   unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *. *)
(*   intros. *)
(*   assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto. *)
(*   destruct Hneq1 as (nq1 & nq2 & nq3 & nq4). *)
(*   destruct H3. *)
(*   lets Heq1: nth_upd_neq nq1 H3. *)
(*   lets Heq2: nth_upd_neq nq2 Heq1. *)
(*   assert (nth_val 5 tcurl = Some (V$ OS_STAT_RDY) /\ *)
(*             nth_val 4 tcurl = Some (V$ 0) /\ (exists m0, (p, t, m) = (prio, rdy, m0))). *)
(*   eauto. *)
(*   destruct H13. destruct H14. *)
(*   rewrite H11 in H14. *)
(*   inverts H14. *)
(*   tryfalse. *)
(*   unfold RHL_RdyI_P in *. unfold RdyTCBblk in *. *)
(*   unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *. *)
(*   intros. *)
(*   tryfalse. *)
(*   funfold H8. *)
(*   rename H15 into Hpostq1. (* new add *) *)
(*   unfold RLH_TCB_Status_Wait_P. *)
(*   splits; *)
(*     try (unfold RLH_WaitS_P,RLH_WaitQ_P,RLH_WaitMB_P,RLH_WaitMS_P,RLH_WaitPostQ_P in *; (* new add *) *)
(*          intros; *)
(*          unfold V_OSTCBStat in *; *)
(*          apply nth_upd_eq in H16; *)
(*          tryfalse). *)
(*   unfold RLH_Wait_P in *. *)
(*   intros. eapply WaitTCBblk_hold_update' in H15. *)
(*   funfold H15. *)
(*   rewrite H19 in H11. *)
(*   inverts H11. *)
(*   rewrite H18 in Hvp. *)
(*   inverts Hvp. *)
(*   splits; eauto. *)
(*   funfold H9. *)
(*   rename H15 into Hpostq2. (* new add *) *)
(*   unfold RHL_TCB_Status_Wait_P. *)
(*   splits; *)
(*     try (unfold RHL_WaitS_P,RHL_WaitQ_P,RHL_WaitMB_P,RHL_WaitMS_P,RHL_WaitPostQ_P in *; (* new add *) *)
(*          intros; inverts H15). *)
(*   unfold RHL_Wait_P in *. *)
(*   intros. *)
(*   inverts H15. *)
(*   splits. *)
(*   eapply WaitTCBblk_hold_update. *)
(*   unfold WaitTCBblk. *)
(*   destruct Hp. *)
(*   unfold RLH_RdyI_P in *. *)
(*   unfold RdyTCBblk in *. *)
(*   assert (V_OSTCBStat tcurl = Some (V$ OS_STAT_RDY) /\ *)
(*             V_OSTCBDly tcurl = Some (V$ 0) /\ *)
(*             (exists m, (prio, t, m0) = (prio, rdy, m))). *)
(*   eapply H6. *)
(*   unfold V_OSTCBPrio. eauto. *)
(*   destruct H16. destruct H17. *)
(*   unfold V_OSTCBDly in H17. *)
(*   rewrite H11 in H17. *)
(*   inverts H17. tryfalse. *)
(*   unfold V_OSTCBPrio,V_OSTCBDly. splits; auto. auto. *)
(*   funfold Hrsl'. *)
(*   unfold V_OSTCBStat in *. *)
(*   eapply update_nth; eapply nth_upd_neqrev; try pauto. *)
(* Qed. *)

Lemma TCBList_P_hold_for_update_rdy :
  forall tcbls tcur tcurl tcblist rtbl prio st,
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    0 <= Int.unsigned prio < 64 ->
    array_type_vallist_match char_t rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    True -> 
    (* V_OSTCBDly tcurl = Some (Vint32 Int.zero) -> *) 
    (* isptr (val_inj (V_OSTCBEventPtr tcurl)) -> *)
    prio_in_tbl prio rtbl ->
    TcbMod.get tcbls tcur = Some (prio, st) ->
    TCBList_P (Vptr tcur) 
      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
      rtbl
      (TcbMod.set tcbls tcur (prio, rdy)).
Proof.
  simpl TCBList_P.
  intros.
  destruct H as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  exists td' vv' tcblss' (prio, rdy).
  inverts Hveq'.
  unfold sig in *. unfold TcbMap in *.
  assert (Heq1: (prio, st) = (p, t)).
  {
    eapply TcbMod.map_get_unique.
    eauto.
    eapply TcbMod.join_sig_get. eauto.
  }
  inverts Heq1.
  splits; try auto.
  unfold V_OSTCBNext in *;
    try (eapply nth_upd_neqrev; try pauto);
    try (eapply nth_upd_neqrev; try pauto).
  unfold TcbMod.join in *.
  intros.
  specialize Htcj' with (a:= a).
  erewrite TcbMod.sig_sem in *.
  rewrite TcbMod.set_sem in *.
  pure_auto.
  (*TCBNode_P (update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))
  rtbl (p, rdy, m) *)
  assert (Hwt: ~(WaitTCBblk tcurl rtbl p)).
  {
    unfold WaitTCBblk.
    lets Hnp: prio_in_tbl_imp H0 H1 H2 H4.
    pauto.
  }
  destruct Htp' as (Hvm & Hvp & Hrsl' & Hrtsl').
  unfold TCBNode_P.
  unfold V_OSTCBMsg,V_OSTCBPrio in *.
  splits;
    try (eapply nth_upd_neqrev; try pauto);
    try (eapply nth_upd_neqrev; try pauto).
  apply RL_TCBblk_P_hold_for_update; auto.
  funfold Hrtsl'.
  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  
  destruct H.
  lets Heq1: nth_upd_neq nq1 H.
  lets Heq2: nth_upd_neq nq2 Heq1.
  assert (Hrl: nth_val 5 tcurl = Some (V$ OS_STAT_RDY) /\ (p, t) = (prio, rdy))
    by eauto.
  destruct Hrl as (Hrl1 & H13). inverts H13.
  splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.

  unfold RHL_RdyI_P,RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H.
  assert (Heq: nth_val 5 tcurl = Some (V$ OS_STAT_RDY) /\ (prio, t) = (prio, rdy)).   
  { eapply Hrsl'. eauto. }
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.

  unfold RLH_TCB_Status_Wait_P. 
  unfold RLH_WaitS_P.
  intros. eapply WaitTCBblk_hold_update' in H;
    unfold WaitTCBblk in H.
  destruct H.
  unfold V_OSTCBPrio in H. 
  rewrite H in Hvm; inverts Hvm.
  assert (Hnp: ~(prio_not_in_tbl p rtbl)) by (eapply prio_in_tbl_imp; eauto).
  pauto.
  
  unfold RHL_TCB_Status_Wait_P.
  unfold RHL_WaitS_P.
  intros. false.
Qed.

Lemma TCBList_P_rtbl_add_lemma_2:
  forall prio px py bitx grp rtbl vl vptr tcbls,
    0 <= Int.unsigned prio < 64 ->
    py = Int.shru prio ($ 3) ->
    px = prio &ᵢ$ 7 ->
    bitx = $ 1<<ᵢpx  ->
    Int.unsigned py <= 7 ->
    Int.unsigned px <= 7 ->
    
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    TCBList_P vptr vl
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio &ᵢ$ 7)))))
              tcbls
    ->
    TCBList_P vptr vl
              (update_nth_val (Z.to_nat (Int.unsigned py)) rtbl
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned py)) rtbl) (Vint32 bitx))))
              tcbls.
Proof.
  intros.
  remember (val_inj
           (or (nth_val' (Z.to_nat (Int.unsigned py)) rtbl) (Vint32 bitx))) as Hv.
  subst py.
  apply nth_val_nth_val'_some_eq in H5.
  unfold nat_of_Z in H5.
  rewrite H5 in HeqHv.
  unfold or in HeqHv.
  simpl in HeqHv.
  subst.
  auto.
Qed.

Require Import tcblist_setnode_lemmas.

Lemma join_join_merge :
  forall (m1 m2 m3 m4 m5: TcbMod.map),
    join m1 m2 m3 -> join m4 m5 m1 -> join m4 (merge m5 m2) m3.
Proof.
  intros.
  unfolds; intros.
  unfold TcbMap.
  unfolds; intros.
  pose proof H a.
  pose proof H0 a.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get m1 a);
  destruct(TcbMod.get m2 a);
  destruct(TcbMod.get m3 a);
  destruct(TcbMod.get m4 a);
  destruct(TcbMod.get m5 a);
  tryfalse; substs; auto.
Qed.

Lemma get_get_neq:
  forall m tid v1 v2 tid',
    TcbMod.get m tid = v1 ->
    TcbMod.get m tid' = v2 ->
    v1 <> v2 ->
    tid <> tid'.
Proof.
  introv Fg1 Fg2 Fneq.
  assert (Fdes: tid = tid' \/ tid <> tid').
    tauto.
  destruct Fdes eqn: Fdes'.
  subst.
  tryfalse.
  trivial.
Qed.

Lemma TCBList_P_rtbl_add_lemma_1:
  forall ma mb mab' mab mc ma' ma'' prio st tid,
    TcbMod.join ma mb mab ->
    TcbMod.join mc ma' ma ->
    TcbJoin tid (prio, st) ma'' ma' ->
    TcbJoin tid (prio, st) mab' mab ->
    R_Prio_No_Dup mab ->
    (forall tid' p s,
        TcbMod.get mb tid' = Some (p, s) -> p <> prio).
Proof.
  introv Fj1 Fj2 Fs1 Fs2 Fnodup.
  introv Fget.
  assert (Hl1: TcbMod.get mab tid = Some (prio, st)).
  {
    eapply TcbMod.join_sig_get.
    unfolds in Fs2.
    unfold join, sig in Fs2; simpl in Fs2; eauto.
  }
  assert (Hl2: TcbMod.get mb tid = None).
  {
    eapply TCBList_P_rtbl_add_lemma_1a; eauto.
  }
  assert (Hl3: tid <> tid').
  {
    eapply get_get_neq; eauto.
  }
  intro; tryfalse.
  assert (Hl4: TcbMod.sub mb mab).
  {
    TcbMod.solve_map.
  }
  unfold R_Prio_No_Dup in Fnodup.
  lets HF1': Fnodup Hl3.
  unfold get in HF1'; simpl in HF1'.
  lets HF1: HF1' Hl1.
  lets Hl5: TcbMod.get_sub_get Fget Hl4. 
  eapply neq_comm.
  eapply HF1; eauto.
  auto.
Qed.

Lemma prio_notin_tbl_orself :
  forall prio v'37 vx,
    Int.unsigned prio < 64 ->
    nth_val (Z.to_nat(Int.unsigned (Int.shru prio ($ 3)))) v'37 = Some (Vint32 vx) ->
    ~ prio_not_in_tbl prio
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                      (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Hr Hx  Hf.
  unfolds in Hf.
  assert (nth_val ∘(Int.unsigned (Int.shru prio ($ 3)))
                  (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                                  (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth; eauto.
  lets Hzds : Hf H; eauto.
  rewrite Int.and_commut in Hzds.
  rewrite Int.or_commut in Hzds.
  rewrite Int.and_or_absorb in Hzds.
  gen Hzds.
  clear - Hr.
  mauto.
Qed.

Lemma TCBList_P_hold_for_update_rdy' :
  forall tcbls tcur tcurl tcblist rtbl prio st ptbl tcbls' tcbls'' head tcblist' vhold,
    0 <= Int.unsigned prio < 64 ->
    array_type_vallist_match char_t rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    True ->
    (* V_OSTCBDly tcurl = Some (Vint32 Int.zero) -> *)
    TcbMod.get tcbls tcur = Some (prio, st) ->
    R_PrioTbl_P ptbl tcbls'' vhold ->
    TcbMod.join tcbls' tcbls tcbls'' ->
    TCBList_P head tcblist' rtbl tcbls' ->
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    TCBList_P (Vptr tcur) 
      ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
         (val_inj
            (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (Vint32 ($ 1<<ᵢ(prio &ᵢ$ 7))))))
      (TcbMod.set tcbls tcur (prio, rdy)).
Proof.
  simpl TCBList_P.
  intros.
  destruct H7 as (td' & vv' & tcblss' & asbs' & Hveq' & Hnes' & Htcj' & Htp' & Htlis').
  destruct asbs'.
  exists td' vv' tcblss' (prio, rdy).
  inverts Hveq'.
  unfold sig in *. unfold TcbMap in *.
  assert (Heq1: (prio, st) = (p, t)).
  {
    eapply TcbMod.map_get_unique.
    eauto.
    eapply TcbMod.join_sig_get. eauto.
  }
  inverts Heq1.
  lets Hex : int_usigned_tcb_range H.
  destruct Hex as (He1 & He2).
  assert (He1': 0 <= Int.unsigned (p >>ᵢ $ 3) <= 7) by auto with zarith.
  lets Hgrp: array_type_match_get_value He1' H0 H1.
  destruct Hgrp as [grp]. rename H7 into Hgrp.
  splits; try auto.
  unfold V_OSTCBNext in *;
    try (eapply nth_upd_neqrev; try pauto);
    try (eapply nth_upd_neqrev; try pauto).
  unfold TcbMod.join in *.
  intros.
  specialize Htcj' with (a:= a).
  erewrite TcbMod.sig_sem in *.
  rewrite TcbMod.set_sem in *.
  pure_auto.
  2: {
    eapply TCBList_P_rtbl_add_lemma_2; try pauto.
    auto with zarith.
    fold nat_of_Z.
    eapply TCBList_P_rtbl_add_simpl_version; try eauto.
    lets Hget: TcbMod.join_get_r H5 H3.
    lets Hjs: TcbMod.map_join_get_sig Hget.
    destruct Hjs as [x'].
    apply TcbMod.map_join_comm in H5.
    apply TcbMod.map_join_comm in Htcj'.
    lets Hjoin: join_join_merge H5 Htcj'.
    apply TcbMod.map_join_comm in Hjoin.
    eapply TCBList_P_rtbl_add_lemma_1.
    eauto.
    apply TcbMod.map_join_comm.
    apply TcbMod.join_merge_disj.
    eapply TcbMod.join_join_disj_r. eauto. eauto.
    unfold TcbJoin.
    auto with jdb. 
    unfold TcbJoin.
    unfold join. unfold sig. unfold TcbMap. eauto.
    funfold H4. auto.
  }
  destruct Htp' as (Hvp & Hrsl' & Hrtsl').
  unfold TCBNode_P.
  unfold V_OSTCBMsg,V_OSTCBPrio in *.
  splits;
    try (eapply nth_upd_neqrev; try pauto);
    try (eapply nth_upd_neqrev; try pauto).
  apply RL_TCBblk_P_hold_for_update; auto.

  funfold Hrtsl'.
  lets Hgrp': nth_val_nth_val'_some_eq Hgrp.
  rewrite Hgrp'.
  unfold or. simpl val_inj.

  unfold R_TCB_Status_P.
  splits. unfold RLH_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat /\ 4%nat <> 5%nat /\ 4%nat <> 2%nat) by pauto.
  destruct Hneq1 as (nq1 & nq2 & nq3 & nq4).
  destruct H2.
  lets Heq1: nth_upd_neq nq1 H2.
  lets Heq2: nth_upd_neq nq2 Heq1.
  rewrite Heq2 in Hvp.
  inverts Hvp.  funfold Hrsl'.
  splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.

  unfold RHL_RdyI_P in *. unfold RdyTCBblk in *.
  unfold V_OSTCBPrio,V_OSTCBStat,V_OSTCBDly in *.
  intros.
  inverts H2.
  funfold Hrsl'.
  splits; try splits; try eapply update_nth; try eapply nth_upd_neqrev; try eapply nth_upd_neqrev; try pauto.
  eapply prio_in_tbl_orself.

  lets Hnotp: prio_notin_tbl_orself H17 Hgrp.
  unfold RLH_TCB_Status_Wait_P.
  unfold RLH_WaitS_P. 
  intros; 
    unfold WaitTCBblk in H2;
    destruct H2 as (Hvp' & Hw1);
    assert (Hneq1: 6%nat <> 5%nat /\ 6%nat <> 2%nat) by pauto;
    destruct Hneq1 as (nq1 & nq2);
    lets Heq1: nth_upd_neq nq1 Hvp';
    lets Heq2: nth_upd_neq nq2 Heq1;
    rewrite Heq2 in Hvp; inverts Hvp; tryfalse.
  
  unfold RHL_TCB_Status_Wait_P.
  unfold RHL_WaitS_P. 
  intros; inverts H2.
Qed.

Lemma TCBList_P_hold_for_update_eventto :
  forall tcbls tcur tcurl tcblist rtbl prio st ptbl tcbls' tcbls'' head tcblist' vhold,
    0 <= Int.unsigned prio < 64 ->
    array_type_vallist_match char_t rtbl ->
    length rtbl = ∘ OS_RDY_TBL_SIZE ->
    (* V_OSTCBDly tcurl = Some (Vint32 time) -> *)
    TcbMod.get tcbls tcur = Some (prio, st) ->
    R_PrioTbl_P ptbl tcbls'' vhold ->
    TcbMod.join tcbls' tcbls tcbls'' ->
    TCBList_P head tcblist' rtbl tcbls' ->
    TCBList_P (Vptr tcur) (tcurl::tcblist) rtbl tcbls ->
    ((* TCBList_P (Vptr tcur)  *)
      (*   ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist)  *)
      (*   rtbl *)
      (*   (TcbMod.set tcbls tcur (prio, wait os_stat_time time, msg)) *)
      (* \/  *)
      TCBList_P (Vptr tcur) 
        ((update_nth_val 5 (update_nth_val 2 tcurl Vnull) (V$ OS_STAT_RDY))::tcblist) 
        (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
           (val_inj
              (or (nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl) (Vint32 ($ 1<<ᵢ(prio &ᵢ$ 7)))))
        )
        (TcbMod.set tcbls tcur (prio, rdy))).
Proof.
  intros.
  eapply TCBList_P_hold_for_update_rdy'; try eauto.
Qed.

(* Lemma RH_TCBList_ECBList_P_hold_for_sem_to_wait: forall tcbls ct p qid wt msg ecbls n wls, *)
(*   TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg) -> *)
(*   EcbMod.get ecbls qid = Some (abssem n, wls) -> *)
(*   In ct wls -> *)
(*   RH_TCBList_ECBList_P ecbls tcbls ct -> *)
(*   RH_TCBList_ECBList_P (EcbMod.set ecbls qid (abssem n, remove_tid ct wls))  *)
(*                                                     (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg)) ct. *)
(* Proof. *)
(* introv Htg Heg Hi Hrte. *)
(* destruct Hrte as (Hr1 & Hr2 & Hr3 & Hr4). *)
(* unfolds; *)
(* splits; *)
(* unfolds; *)
(* [ funfold Hr1; *)
(*   rename H0 into Hpostq1; rename H1 into H0; rename H2 into Hpostq2 *)
(*  | funfold Hr2 | funfold Hr3 | funfold Hr4; rename H2 into Hownp]; *)
(* try splits; *)
(* intros; *)
(* try (assert (eid = qid \/ eid <> qid) by tauto; *)
(*  rewrite EcbMod.set_sem in H1; *)
(* destruct H2; *)
(* try (subst; *)
(* rewrite EcbMod.beq_refl in H1; *)
(* destruct H1; *)
(* inverts H1); *)
(* try (rewrite tidspec.neq_beq_false in H1; try auto; *)
(* try eapply H in H1; *)
(* try eapply Hpostq1 in H1; *)
(* (* simpljoin; *) *)
(* do 3 destruct H1; *)
(* rewrite TcbMod.set_sem; *)
(* assert (tid = ct \/ tid <> ct) by tauto; *)
(* destruct H3; *)
(* try (subst; *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Htg in H1; *)
(* inverts H1); *)
(* rewrite tidspec.neq_beq_false; try eauto)). *)
(* 2 : { (* new add about postq *) *)
(* rewrite TcbMod.set_sem in *; *)
(* rewrite EcbMod.set_sem; *)
(* assert (ct = tid \/ ct <> tid) by tauto; *)
(* destruct H2; *)
(* try(subst; *)
(* rewrite TcbMod.beq_refl in *; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false in H1; try auto; *)
(* try (eapply Hpostq2 in H1; *)
(* do 4 destruct H1; *)
(*  assert (eid = qid \/ eid <> qid) by tauto; *)
(* destruct H3; *)
(* try (subst; *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Heg in H1; *)
(* destruct H1; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false; try eauto). *)
(* } *)
(* Focus 5. *)
(* { *)
(*   assert (eid = qid \/ eid <> qid) by tauto; *)
(*  rewrite EcbMod.set_sem in H2; *)
(* destruct H3; *)
(* try (subst; *)
(* rewrite EcbMod.beq_refl in H2; *)
(* destruct H2; *)
(* inverts H2); *)
(* try (rewrite tidspec.neq_beq_false in H2; try auto; *)
(* eapply H in H2; *)
(* do 3 destruct H2; *)
(* rewrite TcbMod.set_sem; *)
(* assert (tid = ct \/ tid <> ct) by tauto; *)
(* destruct H4; *)
(* try (subst; *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Htg in H2; *)
(* inverts H2); *)
(* rewrite tidspec.neq_beq_false; try eauto). *)
(* } *)
(* Unfocus. *)
(* Focus 2. *)
(* { *)
(*   rewrite TcbMod.set_sem. *)
(*   assert (ct = tid \/ ct <> tid) by tauto. *)
(*   destruct H1. *)
(*   subst. eapply in_remove_tid_false in H2. tryfalse. *)
(*   rewrite tidspec.neq_beq_false; try auto. *)
(*   eapply H. *)
(*   split; try eauto. *)
(*   eapply tidneq_inwt_in with (x1:= wls) in H1. *)
(*   rewrite H1 in H2. auto. *)
(* } *)
(* Unfocus. *)
(* { *)
(* rewrite TcbMod.set_sem in *; *)
(* rewrite EcbMod.set_sem; *)
(* assert (ct = tid \/ ct <> tid) by tauto; *)
(* destruct H2; *)
(* try(subst; *)
(* rewrite TcbMod.beq_refl in *; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false in H1; try auto; *)
(* try (eapply H0 in H1; *)
(* do 4 destruct H1; *)
(*  assert (eid = qid \/ eid <> qid) by tauto; *)
(* destruct H3; *)
(* try (subst; *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Heg in H1; *)
(* destruct H1; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false; try eauto). *)
(* } *)
(* { *)
(* rewrite TcbMod.set_sem in *; *)
(* rewrite EcbMod.set_sem; *)
(* assert (ct = tid \/ ct <> tid) by tauto; *)
(* destruct H2; *)
(* try(subst; *)
(* rewrite TcbMod.beq_refl in *; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false in H1; try auto. *)
(* eapply H0 in H1. *)
(* do 2 destruct H1. *)
(*  assert (eid = qid \/ eid <> qid) by tauto. *)
(* destruct H3. *)
(* subst. *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Heg in H1. *)
(* destruct H1; inverts H1. *)
(* rewrite EcbMod.beq_refl. *)
(* exists x (remove_tid ct x0). *)
(* split; auto. *)
(* eapply tidneq_inwt_in with (x1:= x0) in H2. *)
(* rewrite <- H2 in H3. auto. *)
(* rewrite tidspec.neq_beq_false; try eauto. *)
(* } *)
(* { *)
(* rewrite TcbMod.set_sem in *; *)
(* rewrite EcbMod.set_sem; *)
(* assert (ct = tid \/ ct <> tid) by tauto; *)
(* destruct H2; *)
(* try(subst; *)
(* rewrite TcbMod.beq_refl in *; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false in H1; try auto; *)
(* try (eapply H0 in H1; *)
(* do 2 destruct H1; *)
(*  assert (eid = qid \/ eid <> qid) by tauto; *)
(* destruct H3; *)
(* try (subst; *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Heg in H1; *)
(* destruct H1; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false; try eauto). *)
(* } *)
(* { *)
(* rewrite TcbMod.set_sem in *; *)
(* rewrite EcbMod.set_sem; *)
(* assert (ct = tid \/ ct <> tid) by tauto; *)
(* destruct H3; *)
(* try(subst; *)
(* rewrite TcbMod.beq_refl in *; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false in H2; try auto; *)
(* try (eapply H0 in H2; *)
(* do 3 destruct H2; *)
(*  assert (eid = qid \/ eid <> qid) by tauto; *)
(* destruct H4; *)
(* try (subst; *)
(* unfold get in *; unfold TcbMap,EcbMap in *; *)
(* rewrite Heg in H2; *)
(* destruct H2; *)
(* tryfalse); *)
(* rewrite tidspec.neq_beq_false; try eauto). *)
(* } *)
(* eapply rh_tcblist_ecblist_mutex_owner_set'; eauto. *)
(* apply Mutex_owner_hold_for_set_tcb; auto. *)
(* (* new add about RH_TCBList_ECBList_MUTEX_OWNER_P *) *)
(*     eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_ecb; *)
(*     try eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto. *)
(*     intro Hf. *)
(*     destruct Hf as (vpip & vo & Hf). *)
(*     inverts Hf. *)
(* Qed. *)

(* new add *)
(* Lemma R_ECB_PETbl_P_high_tcb_block_hold': *)
(*   forall  l vl etbl petbl vl' etbl' petbl' tcbls prio st ptcb m', *)
(*   ~( V_OSEventType vl = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))) -> *)
(*   ~( V_OSEventType vl' = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q))) -> *)
(*   R_ECB_PETbl_P l (vl, etbl, petbl) tcbls -> *)
(*   ~(exists qid time, st = wait (os_stat_postq qid) time) -> *)
(*   R_ECB_PETbl_P l (vl', etbl', petbl') (TcbMod.set tcbls ptcb (prio, st, m')). *)
(* Proof. *)
(* introv Hneq. intros. *)
(* funfold H0. *)
(* unfolds; splits; unfolds; intros. *)
(* rewrite H4 in H; tryfalse. *)
(* unfold get in *; unfold TcbMap in *. *)
(* assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto. *)
(* destruct Hc. *)
(* subst. *)
(* rewrite TcbMod.map_get_set in H3. *)
(* inverts H3. *)
(* false. eapply H1; eauto. *)
(* rewrite TcbMod.map_get_set' in H3; auto. *)
(* eapply H2 in H3. *)
(* destruct H3 as (H3 & Hf). *)
(* rewrite Hf in Hneq; tryfalse. *)
(* Qed. *)

(* Lemma R_ECB_PETbl_P_high_tcb_block_hold'': *)
(*   forall  l vl etbl petbl etbl' tcbls prio st ptcb m' p st0 m0, *)
(*   TcbMod.get tcbls ptcb = Some (p, st0, m0) -> *)
(*   ~(exists qid time, st0 = wait (os_stat_postq qid) time) -> *)
(*   R_ECB_PETbl_P l (vl, etbl, petbl) tcbls -> *)
(*   ~(exists qid time, st = wait (os_stat_postq qid) time) -> *)
(*   R_ECB_PETbl_P l (vl, etbl', petbl) (TcbMod.set tcbls ptcb (prio, st, m')). *)
(* Proof. *)
(* introv Hget. intros. *)
(* funfold H0. *)
(* unfolds; splits; unfolds; intros. *)
(* eapply H0 in H4; eauto. *)
(* simpljoin. *)
(* assert (Hc: ptcb = x \/ ptcb <> x) by tauto. *)
(* destruct Hc. *)
(* subst. *)
(* unfold get in *; unfold TcbMap in *. *)
(* rewrite Hget in H4; inverts H4. *)
(* false. eapply H; eauto. *)
(* repeat eexists. *)
(* eapply TcbMod.map_get_set' in H5; eauto. *)
(* rewrite H5; eauto. *)
(* unfold get in *; unfold TcbMap in *. *)
(* assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto. *)
(* destruct Hc. *)
(* subst. *)
(* rewrite TcbMod.map_get_set in H3. *)
(* inverts H3. *)
(* false. eapply H1; eauto. *)
(* rewrite TcbMod.map_get_set' in H3; auto. *)
(* eapply H2 in H3. *)
(* destruct H3 as (H3 & Hf). *)
(* split; auto. *)
(* Qed. *)

(* Lemma ECBList_P_high_tcb_block_hold_sem_to_wait: *)
(*   forall  ectrl head tail msgql ecbls tcbls ptcb prio  m qid time, *)
(*     ECBList_P head tail ectrl msgql ecbls tcbls -> *)
(*     TcbMod.get tcbls ptcb = Some (prio, wait (os_stat_sem qid) time, m) -> *)
(*     EcbMod.get ecbls qid = None -> *)
(*     ECBList_P head tail ectrl msgql ecbls  *)
(*       (TcbMod.set tcbls ptcb (prio, wait os_stat_time time, m)). *)
(* Proof. *)
(*   inductions ectrl. *)
(*   intros. *)
(*   simpl. *)
(*   simpl in H. *)
(*   auto. *)
(*   intros. *)
(*   simpl in H. *)
(*   mytac. *)
(*   destruct msgql; tryfalse. *)
(*   destruct a. *)
(*   destruct p. (* new add *) *)
(*   rename H3 into Hpetbl; rename H4 into H3. (* new add *) *)
(*   mytac. *)
(*   simpl. *)
(*   exists x. *)
(*   splits; auto. *)
(*   unfolds. *)
(*   destruct H2 as (Hr1 & Hr2 & Hr3). *)
(*   destruct Hr1 as (Hra3 & Hra1 & Hra2 & Hra4). *)
(*   destruct Hr2 as (Hrb3 & Hrb1 & Hrb2 & Hrb4). *)
(*   simpl in Hr3. *)
(*   splits. *)
(*   unfolds. *)
(*   splits; *)
(*   unfolds; *)
(*   intros; *)
(*   [eapply Hra3 in H6 | eapply Hra1 in H6 | eapply Hra2 in H6 | eapply Hra4 in H6]; *)
(*   mytac; *)
(*    assert (x3 = ptcb \/ x3 <> ptcb) by tauto; *)
(*   destruct H7; *)
(*   try (subst; *)
(*     unfold get in H6; simpl in H6; *)
(*     rewrite H0 in H6; *)
(*     inverts H6; *)
(*     eapply EcbMod.join_sig_get in H3; *)
(*     rewrite H3 in H1; *)
(*     inverts H1); *)
(*     try (subst; *)
(*     unfold get in H6; simpl in H6; *)
(*     rewrite H0 in H6; *)
(*     inverts H6); *)
(*     repeat eexists; *)
(*     rewrite TcbMod.set_sem; *)
(*     rewrite tidspec.neq_beq_false; eauto. *)
(*   unfolds; *)
(*   splits; *)
(*   unfolds; *)
(*   intros; *)
(*   assert (tid = ptcb \/ tid <> ptcb) by tauto; *)
(*     destruct H6; *)
(*     try subst; *)
(*     rewrite TcbMod.set_sem in H2; *)
(*     try (rewrite TcbMod.beq_refl in H2; inverts H2); *)
(*     rewrite tidspec.neq_beq_false in H2; eauto. *)
(*     simpl; auto. *)
(*     (* new add about petbl *) *)
(*     eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto. *)
(*   introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf. *)
(*    introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf. *)
(*   (* end of new add *) *)
(*   do 3 eexists; splits; eauto. *)
(*   eapply IHectrl; eauto. *)
(*   eapply  ecbmod_joinsig_get_none; eauto. *)
(* Qed. *)

Fixpoint get_ectr (eid:val) (head:val) (ectrl:list EventCtr) :=
  match eid, head, ectrl with
  | (Vptr e), (Vptr e'), (osevent, etbl)::vll =>
      match beq_addrval e e' with
      | true => Some (osevent, etbl)
      | false => match V_OSEventListPtr osevent with
                 | Some vn => get_ectr eid vn vll
                 | _ => None
                 end
      end
  | _,_,_ => None
  end.

Lemma beq_addrval_eq: forall a b, beq_addrval a b = true -> a = b.
Proof.
  introv HeqX.
  unfold beq_addrval in HeqX.
  destruct b, a.
  rewrite andb_true_iff in HeqX.
  destruct HeqX.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  lets Hx: Int.eq_spec i0 i.
  rewrite H0 in Hx.
  subst.
  auto.
Qed.

Lemma get_last_prop:
  forall (l : list EventCtr)  x v y,
    l <> nil -> 
    (get_last_ptr ((x, v) :: l)  =   y <->
     get_last_ptr  l =  y).
Proof.
  destruct l.
  intros.
  tryfalse.
  intros.
  unfolds get_last_ptr.
  simpl.
  destruct l; splits;auto.
Qed.

Lemma get_ectr_sing:
  forall qid head (els1: list os_inv.EventCtr) osevent etbl,
    els1 <> nil ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl) :: nil))  = Some (osevent,etbl) ->
    get_last_ptr els1 = Some (Vptr qid).
Proof.
  induction els1.
  intros.
  tryfalse.
  induction els1.
  unfold get_last_ptr.
  simpl.
  intros.
  destruct a.
  destruct head;
    try inverts H1.
  destruct (beq_addrval qid a); try tryfalse.
  destruct (V_OSEventListPtr v); try tryfalse. 
  destruct v1; try tryfalse. 
  destruct (beq_addrval qid a0) eqn: eq1.
  apply beq_addrval_eq in eq1.
  subst. auto.
  destruct (V_OSEventListPtr osevent); try tryfalse.
  destruct v1; try tryfalse.  
  intros.
  destruct a.
  assert (Hn: (a0 :: els1) <> nil) by pauto.
  eapply get_last_prop in Hn.
  erewrite Hn.
  destruct a0.
  eapply IHels1; try pauto;
    clear IHels0 IHels1 Hn;
    simpl in *;
    destruct head; try tryfalse; try auto;
    destruct (beq_addrval qid a) eqn: eq1; try tryfalse;
    destruct (V_OSEventListPtr v1); try auto; try tryfalse; 
    destruct (V_OSEventListPtr v); try tryfalse;  
    destruct v4; try tryfalse;  
    destruct (beq_addrval qid a0) eqn: eq2; try tryfalse; try eauto.
Qed.

Lemma prio_wt_inq_tid_neq:
  forall prio'  v'13  v'69 prio,
    nth_val' (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'13 = Vint32 v'69 ->
    Int.unsigned prio < 64 ->
    (PrioWaitInQ (Int.unsigned prio')
       (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'13
          (Vint32 (v'69&ᵢInt.not ($ 1<<ᵢ (prio &ᵢ $7))))) <->
       PrioWaitInQ  (Int.unsigned prio') v'13 /\  prio' <> prio).
Proof.
  intros.
  splits.
  intros.
  unfolds in H1.
  destruct H1 as (x & y & z & Hx & Hy & Hz & Hn & Heq).
  subst.
  rewrite Int.repr_unsigned in *.
  
  assert (Int.shru prio ($ 3) = Int.shru prio' ($ 3) \/
          Int.shru prio ($ 3) <> Int.shru prio' ($ 3)) by tauto.
  destruct H1.
  rewrite H1 in Hn.
  lets Hzs : nth_upd_eq  Hn.
  inverts Hzs.
  assert (prio&ᵢ$ 7 = prio'&ᵢ$ 7 \/ prio&ᵢ$ 7 <> prio'&ᵢ$ 7) by tauto.
  destruct H2.
  rewrite H2 in Heq.
  rewrite Int.and_assoc in Heq.
  assert (Int.not ($ 1<<ᵢ(prio'&ᵢ$ 7))&ᵢ(Int.one<<ᵢ(prio'&ᵢ$ 7)) = Int.zero).
  rewrite Int.and_commut.
  rewrite  Int.and_not_self; auto.
  rewrite H3 in Heq.
  rewrite Int.and_zero in Heq.
  false.
  gen Heq.
  clear -Hx.
  mauto.
  splits.
  unfolds.
  do 3 eexists.
  splits; eauto.
  rewrite Int.repr_unsigned.
  unfold nat_of_Z.
  rewrite H1 in H.
  apply nth_val'_imp_nth_val_int in H.
  eauto.
  rewrite Int.repr_unsigned.
  rewrite Int.and_assoc in Heq.
  
  assert (Int.unsigned (prio'&ᵢ$ 7) < 8).
  clear -Hx.
  mauto.
  assert (Int.unsigned (prio&ᵢ$ 7) < 8).
  clear -H0.
  mauto.
  lets Hxa : int_not_shrl_and H4 H3 H2.
  unfold Int.one in *.
  rewrite Hxa in Heq.
  auto.
  introv Hf.
  subst prio.
  apply H2.
  auto.
  apply nth_upd_neq in Hn.
  splits.
  unfolds.
  do 3 eexists.
  splits; eauto.
  rewrite Int.repr_unsigned.
  apply nth_val'_imp_nth_val_int in H.
  eauto.
  rewrite Int.repr_unsigned.
  eauto.
  introv hf.
  subst prio.
  apply H1.
  auto.
  unfold nat_of_Z.
  introv Hf.
  apply H1.
  rewrite Z2Nat.inj_iff in Hf.
  apply unsigned_inj.
  auto.
  apply Int.unsigned_range.
  apply Int.unsigned_range.
  intros.
  destruct H1 as (Hpro & Hneq).
  unfolds in Hpro.
  destruct Hpro as (px & py & pz & Hx& Hy& Hz &Hnt & Hez).
  unfolds.
  rewrite Int.repr_unsigned.
  apply nth_val'_imp_nth_val_int in H.
  assert (Int.shru prio ($ 3) = Int.shru prio' ($ 3) \/
          Int.shru prio ($ 3) <> Int.shru prio' ($ 3)) by tauto.
  destruct H1.
  unfold nat_of_Z in *.
  do 3 eexists.
  splits; eauto.
  rewrite H1 in *.
  eapply update_nth; eauto.
  subst py px.
  rewrite Int.repr_unsigned in *.
  rewrite H1 in *.
  rewrite H in Hnt.
  inverts Hnt.
  assert (pz &ᵢ Int.not ($ 1<<ᵢ(prio&ᵢ$ 7)) = Int.not ($ 1<<ᵢ(prio&ᵢ$ 7)) &ᵢ pz).
  apply Int.and_commut.
  rewrite H2.
  rewrite Int.and_assoc.
  rewrite Hez.
  lets Hsd : int_usigned_tcb_range Hx.
  destruct Hsd.
  assert (0<=Int.unsigned prio < 64).
  Require Import Lia.
  split; try lia.
  clear -prio'.
  int auto.
  lets Hss : int_usigned_tcb_range H5.
  destruct Hss.
  apply  int_not_shrl_and ; try lia.
  introv Hf.
  apply Hneq.

  rewrite math_prio_eq.
  rewrite math_prio_eq at 1.
  rewrite H1.
  rewrite Hf.
  auto.
  lia.
  lia.
  do 3 eexists.
  splits; eauto.
  subst px py.
  rewrite Int.repr_unsigned in *.
  unfold nat_of_Z in *.
  eapply nth_upd_neqrev; eauto.
  introv Hf.
  apply H1.
  rewrite Z2Nat.inj_iff in Hf.
  apply unsigned_inj.
  auto.
  apply Int.unsigned_range.
  apply Int.unsigned_range.
  subst px.
  rewrite Int.repr_unsigned in *.
  auto.
Qed.

Lemma RLH_ECB_ETbl_P_hold_for_update_sem_to_st:
  forall tcbls ct p qid osevent etbl ey egrp' st,
    Int.unsigned p < 64 ->
    TcbMod.get tcbls ct = Some (p, wait qid) -> 
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RLH_ECB_ETbl_P qid (osevent, etbl) tcbls -> 
    RLH_ECB_ETbl_P qid
      (update_nth_val 1 osevent (Vint32 egrp'),
        update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
          (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))))
      (TcbMod.set tcbls ct (p, st)).
Proof.
  introv Hpr Htg Hey Hre.
  unfolds in Hre.
  rename Hre into Hra2.
  unfolds.
  unfolds;
    funfold Hra2. 
  unfold V_OSEventType in *;
    intros. 
  assert (Hpr1: 0 <= prio /\ prio <= Int.max_unsigned) by (funfold H; clear -H H5; int auto). 
  destruct Hpr1 as (Hpr1 & Hpr2). 
  lets Hvp: int_usign_eq Hpr1 Hpr2. 
  rewrite <- Hvp in H.  
  pose proof prio_wt_inq_tid_neq. 
  specialize H1 with (prio':= $ prio). 
  lets Hpi: H1 Hey Hpr. 
  rewrite Hpi in H. 
  clear H1 Hpi. 
  rewrite Hvp in H. 
  destruct H. 
  assert (nq1: 0%nat <> 1%nat) by pauto. 
  lets Heq1: nth_upd_neq nq1 H0. 
  lets Hst: Hra2 H Heq1.
  destruct Hst as [tid].
  unfold get in *; unfold TcbMap in *. 
  exists tid. 
  assert (tid = ct \/ tid <> ct) by tauto. 
  destruct H3; 
    try (subst;
         rewrite Htg in H2;
         inverts H2);
    rewrite TcbMod.set_sem;
    rewrite tidspec.neq_beq_false; eauto.
Qed.

(* Lemma RHL_ECB_ETbl_P_hold_for_update_sem_to_wait: forall tcbls ct p qid wt msg osevent etbl ey egrp' ptbl vhold petbl, *)
(*     Int.unsigned p < 64 -> *)
(*     R_PrioTbl_P ptbl tcbls vhold -> *)
(*     TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg) -> *)
(*     nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey -> *)
(*     RHL_ECB_ETbl_P qid (osevent,etbl,petbl) tcbls -> *)
(*     RHL_ECB_ETbl_P qid *)
(*      (update_nth_val 1 osevent (Vint32 egrp'), *)
(*       update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl *)
(*       (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7)))),petbl) *)
(*       (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg)). *)
(* Proof. *)
(* introv Hpr Hrpt Htg Hey Hre. *)
(* destruct Hre as (Hrb1 & Hrb2 & Hrb3 & Hrb4). *)
(* unfolds; *)
(* splits; *)
(* unfolds; *)
(* [ funfold Hrb1 | funfold Hrb2 | funfold Hrb3 | funfold Hrb4]; *)
(* unfold V_OSEventType in *; *)
(* destruct Hrpt as (_ & _ & Hrpt); *)
(* funfold Hrpt; *)
(* intros; *)
(* unfold get in *; unfold TcbMap in *; *)
(* assert (tid = ct \/ tid <> ct) by tauto; *)
(* destruct H0; *)
(* rewrite TcbMod.set_sem in H; *)
(* try (subst; *)
(* rewrite TcbMod.beq_refl in H; *)
(* inverts H); *)
(* rewrite tidspec.neq_beq_false in H; try auto; *)
(* pose proof prio_wt_inq_tid_neq; *)
(* specialize H1 with (prio':= prio); *)
(* lets Hpi: H1 Hey Hpr; *)
(* rewrite Hpi; *)
(* clear Hpi; *)
(* lets Hnp: Hrpt H0 H Htg; *)
(* [ try eapply Hrb1 in H | try eapply Hrb2 in H | try eapply Hrb3 in H | try eapply Hrb4 in H]; *)
(* splits; try eapply nth_upd_neqrev; try pauto. *)
(* Qed. *)

Lemma Event_Type_P_hold_for_update:
  forall osevent v n,
    n <> 0%nat ->
    Event_Type_P osevent ->
    Event_Type_P (update_nth_val n osevent (Vint32 v)).
Proof.
  unfold Event_Type_P.
  unfold V_OSEventType.
  intros.
  eapply nth_upd_neqrev; try pauto.
Qed.

(* Lemma R_ECB_ETbl_P_hold_for_update_sem_to_wait: *)
(*   forall tcbls ct p qid wt msg osevent etbl y ey egrp' bitx ptbl vhold petbl, *)
(*       Int.unsigned p < 64 -> *)
(*       y = p >>ᵢ $ 3 -> *)
(*       bitx = $ 1<<ᵢ (p&ᵢ$ 7) -> *)
(*       R_PrioTbl_P ptbl tcbls vhold -> *)
(*       TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg) -> *)
(*       R_ECB_ETbl_P qid (osevent, etbl,petbl) tcbls -> *)
(*       nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey -> *)
(*       R_ECB_ETbl_P qid *)
(*        (update_nth_val 1 osevent (Vint32 egrp'), *)
(*          update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)),petbl) *)
(*        (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg)). *)
(* Proof. *)
(* introv Hpr Hy Hbitx Hrpt Htg Hre Hey. *)
(* funfold Hre. *)
(* unfolds. *)
(* splits. *)
(* eapply RLH_ECB_ETbl_P_hold_for_update_sem_to_st; try eauto. *)
(* eapply RHL_ECB_ETbl_P_hold_for_update_sem_to_wait; try eauto. *)
(* simpl in *. *)
(* eapply Event_Type_P_hold_for_update; try auto. *)
(* Qed. *)

Lemma EcbMod_get_join_sig_set:
  forall  qls qid a qls1 b,
    EcbMod.join (EcbMod.sig qid b) qls1 qls ->
    EcbMod.get qls1 qid = None ->
    EcbMod.join (EcbMod.sig qid a) qls1 (EcbMod.set qls qid a).
Proof.
  intros.
  unfold EcbMod.join.
  intros.
  rewrite EcbMod.sig_sem.
  rewrite EcbMod.set_sem.
  assert (qid = a0 \/ qid <> a0) by tauto.
  destruct H1.
  subst.
  rewrite EcbMod.beq_refl.
  rewrite H0. auto.
  eapply tidspec.neq_beq_false in H1.
  rewrite H1.
  destruct (EcbMod.get qls1 a0) eqn: eq2.
  lets Htg: EcbMod.join_get_r H  eq2.
  rewrite Htg.
  auto.
  assert (EcbMod.get qls a0 = EcbMod.get qls1 a0).
  eapply EcbMod.map_join_get_none; try eauto.
  rewrite EcbMod.sig_sem.
  rewrite H1. auto.
  rewrite H2. rewrite eq2. auto.
Qed.

Lemma RLH_ECBData_P_hold_sem:
  forall n ct w ecbcurl,
    RLH_ECBData_P ecbcurl (abssem n, w) ->
    RLH_ECBData_P ecbcurl (abssem n, remove_tid ct w).
Proof.
  intros.
  unfolds.
  unfolds in H.
  destruct ecbcurl; try tryfalse.
  split; pauto.
  simpl in *.
  mytac.
  split; intros.
  apply H0 in H.
  subst.
  simpl. auto.
  eapply H1.
  pure_auto.
  subst.
  simpl in *.
  tryfalse.
Qed.

(* Lemma R_ECB_PETbl_upd_hold_gen : *)
(*   forall x1 v v0 v0' v'36 x8 petbl n, *)
(*     n <> 0%nat -> *)
(*     R_ECB_PETbl_P x1 (v, v0, petbl) v'36 -> *)
(*     R_ECB_PETbl_P x1 (ifun_spec.update_nth val n v x8, v0', petbl) v'36. *)
(* Proof. *)
(*   introv Hneq Hr. *)
(*   unfolds in Hr. *)
(*   destruct Hr. *)
(*   unfolds. *)
(*   splits; unfolds; intros. *)
(*   eapply H; eauto. *)
(*   eapply nth_val_upd_prop with (m:= n); eauto. *)
(*   eapply H0 in H1. *)
(*   simpljoin1. *)
(*   splits; auto. *)
(*   eapply nth_val_upd_prop; eauto. *)
(* Qed. *)

(* Lemma R_ECB_PETbl_upd_hold_gen' : *)
(*   forall x1 v v0 v0' v'36 x8 petbl n, *)
(*     n <> 0%nat -> *)
(*     R_ECB_PETbl_P x1 (v, v0, petbl) v'36 -> *)
(*     R_ECB_PETbl_P x1 (update_nth_val n v x8, v0', petbl) v'36. *)
(* Proof. *)
(*   introv Hneq Hr. *)
(*   unfolds in Hr. *)
(*   destruct Hr. *)
(*   unfolds. *)
(*   splits; unfolds; intros. *)
(*   eapply H; eauto. *)
(*   eapply nth_upd_neq with (m:= n); eauto. *)
(*   eapply H0 in H1. *)
(*   simpljoin1. *)
(*   splits; auto. *)
(*   eapply nth_upd_neqrev with (m:= n); eauto. *)
(* Qed. *)

(* Lemma ECBList_P_hold_for_update_sem_to_wait: *)
(*   forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls  *)
(*               tcbls ct p wt msg ey egrp' y bitx qid ptbl vhold n wls petbl, *)
(*     Int.unsigned p < 64 -> *)
(*    y = p >>ᵢ $ 3 -> *)
(*    bitx = $ 1<<ᵢ (p&ᵢ$ 7) -> *)
(*   R_PrioTbl_P ptbl tcbls vhold -> *)
(*   length els1 = length ecblist1 -> *)
(*   RH_TCBList_ECBList_P ecbls tcbls ct -> *)
(*   TcbMod.get tcbls ct = Some (p, wait (os_stat_sem qid) wt, msg) -> *)
(*   EcbMod.get ecbls qid = Some (abssem n, wls) -> *)
(*   In ct wls -> *)
(*   get_ectr (Vptr qid) head els1  = None -> *)
(*   get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl,petbl) :: nil))  = Some (osevent,etbl,petbl) -> *)
(*   ECBList_P head Vnull (els1 ++ ((osevent,etbl,petbl) :: nil) ++ els2)  *)
(*                         (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls -> *)
(*   nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey -> *)
(*   osevent' = update_nth_val 1 osevent (Vint32 egrp') -> *)
(*   etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) -> *)
(*   ECBList_P head Vnull (els1 ++ ((osevent',etbl',petbl) :: nil) ++ els2)  *)
(*                         (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) *)
(*                          (EcbMod.set ecbls qid (abssem n, remove_tid ct wls)) *)
(*                         (TcbMod.set tcbls ct (p, wait os_stat_time wt, msg)) *)
(* . *)
(* Proof. *)
(* introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1. *)
(* introv Hgptr2 Hep Hey Het' Hetbl'. *)
(* assert (Hels1: els1 = nil \/ els1 <> nil) by tauto. *)
(* destruct Hels1. *)
(* subst els1. *)
(* assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto). *)
(* subst ecblist1. *)
(* simpl in *. *)
(* mytac. *)
(* destruct (beq_addrval qid x) eqn: eq1. *)
(* Focus 2. *)
(* destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse. *)
(* apply beq_addrval_eq in eq1. *)
(* subst x. *)
(* exists qid. *)
(* splits; try auto. *)
(* eapply R_ECB_ETbl_P_hold_for_update_sem_to_wait; try eauto. *)
(* eapply R_ECB_PETbl_upd_hold_gen'; eauto. *)
(* eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto. *)
(* introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf. *)
(* introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf. *)
(* exists (abssem n, remove_tid ct wls) x1 x2. *)
(* splits; try auto. *)
(* unfold V_OSEventListPtr in *. *)
(* eapply nth_upd_neqrev; try pauto. *)
(* unfold sig. unfold EcbMap. *)
(* eapply EcbMod_get_join_sig_set; try eauto. *)
(* eapply ejoin_get_none_r; [idtac | eauto]. *)
(* eapply EcbMod.map_get_sig. *)
(* lets Heg': EcbMod.join_sig_get H3. *)
(* destruct x0. *)
(* rewrite Heg in Heg'. *)
(* inverts Heg'. *)
(* eapply RLH_ECBData_P_hold_sem; auto. *)
(* eapply ECBList_P_high_tcb_block_hold_sem_to_wait; try eauto. *)
(* eapply ejoin_get_none_r; [idtac | eauto]. *)
(* eapply EcbMod.map_get_sig. *)
(* (* els1 <> nil *) *)
(* lets Hsp: Mbox_common.ecblist_p_decompose Hl Hep. *)
(* simpl in *. *)
(* mytac. *)
(* lets Hx2: get_ectr_sing H Hgptr1 Hgptr2. *)
(* destruct H3; rewrite H1 in Hx2; inverts Hx2. *)
(* eapply ecblist_p_compose; try eauto. *)
(* Focus 2. *)
(* eapply ECBList_P_high_tcb_block_hold_sem_to_wait; try eauto. *)
(* eapply ejoin_get_none_l; [idtac | eauto]. *)
(* eapply EcbMod.join_sig_get; eauto. *)
(* eapply EcbMod.my_joinsig_join_set; try eauto. *)
(* simpl. *)
(* exists qid. *)
(* splits; try auto. *)
(* eapply R_ECB_ETbl_P_hold_for_update_sem_to_wait; try eauto. *)
(* eapply R_ECB_PETbl_upd_hold_gen'; eauto. *)
(* eapply R_ECB_PETbl_P_high_tcb_block_hold''; eauto. *)
(* introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf. *)
(* introv Hf. destruct Hf as (qd0 & wt0 & Hf). inverts Hf. *)
(* exists (abssem n, remove_tid ct wls) x4 x5. *)
(* splits; try auto. *)
(* unfold V_OSEventListPtr in *. *)
(* eapply nth_upd_neqrev; try pauto. *)
(* unfold sig. unfold EcbMap. *)
(* eapply EcbMod_get_join_sig_set; try eauto. *)
(* eapply ejoin_get_none_r; [idtac | eauto]. *)
(* eapply EcbMod.map_get_sig. *)
(* lets Heg': EcbMod.join_sig_get H7. *)
(* destruct x3. *)
(* lets Heg2: EcbMod.join_get_r H2 Heg'. *)
(* rewrite Heg in Heg2. *)
(* inverts Heg2. *)
(* eapply RLH_ECBData_P_hold_sem; auto. *)
(* eapply ECBList_P_high_tcb_block_hold_sem_to_wait; try eauto. *)
(* eapply ejoin_get_none_r; [idtac | eauto]. *)
(* eapply EcbMod.map_get_sig. *)
(* Unshelve. *)
(* exact nil. *)
(* exact nil. *)
(* Qed. *)

Lemma RHL_ECB_ETbl_P_hold_for_update_sem_to_rdy:
  forall tcbls ct p qid osevent etbl ey egrp' ptbl vhold,
    Int.unsigned p < 64 ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait qid) -> 
    nth_val' (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl = Vint32 ey ->
    RHL_ECB_ETbl_P qid (osevent, etbl) tcbls -> 
    RHL_ECB_ETbl_P qid
      (update_nth_val 1 osevent (Vint32 egrp'),
        update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) etbl
          (Vint32 (ey&ᵢInt.not ($ 1<<ᵢ(p&ᵢ$ 7))))) 
      (TcbMod.set tcbls ct (p, rdy)). 
Proof.
  introv Hpr Hrpt Htg Hey Hre.
  unfolds in Hre.
  rename Hre into Hrb2.

  unfolds;
    unfolds;
    funfold Hrb2;
    unfold V_OSEventType in *. 
  destruct Hrpt as (_ & _ & Hrpt).
  funfold Hrpt.
  intros;
    unfold get in *; unfold TcbMap in *;
    assert (tid = ct \/ tid <> ct) by tauto;
    destruct H0;
    rewrite TcbMod.set_sem in H;
    try (subst;
         rewrite TcbMod.beq_refl in H;
         inverts H);
    rewrite tidspec.neq_beq_false in H; try auto;
    pose proof prio_wt_inq_tid_neq;
    specialize H1 with (prio':= prio);
    lets Hpi: H1 Hey Hpr;
    rewrite Hpi;
    clear Hpi;
    lets Hnp: Hrpt H0 H Htg;
    try eapply Hrb2 in H; 
    splits; try eapply nth_upd_neqrev; try pauto.
Qed.

Lemma R_ECB_ETbl_P_hold_for_update_sem_to_rdy:
  forall tcbls ct p qid osevent etbl y ey egrp' bitx ptbl vhold,
    Int.unsigned p < 64 ->
    y = p >>ᵢ $ 3 ->
    bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
    R_PrioTbl_P ptbl tcbls vhold ->
    TcbMod.get tcbls ct = Some (p, wait qid) -> 
    R_ECB_ETbl_P qid (osevent, etbl) tcbls -> 
    nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
    R_ECB_ETbl_P qid
      (update_nth_val 1 osevent (Vint32 egrp'),
        update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx))) 
      (TcbMod.set tcbls ct (p, rdy)).
Proof.
  introv Hpr Hy Hbitx Hrpt Htg Hre Hey.
  funfold Hre.
  unfolds.
  splits.
  eapply RLH_ECB_ETbl_P_hold_for_update_sem_to_st; try eauto.
  eapply RHL_ECB_ETbl_P_hold_for_update_sem_to_rdy; try eauto.
  simpl in *.
  eapply Event_Type_P_hold_for_update; try auto.
Qed.

Lemma ECBList_P_high_tcb_block_hold_sem_to_rdy:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio qid,
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, wait qid) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
      (TcbMod.set tcbls ptcb (prio, rdy)).
Proof.
  inductions ectrl.
  intros.
  simpl.
  simpl in H.
  auto.
  intros.
  simpl in H.
  mytac.
  destruct msgql; tryfalse.
  destruct a.
  mytac.
  simpl.
  exists x.
  splits; auto.
  unfolds.
  destruct H2 as (Hr1 & Hr2 & Hr3).
  unfolds in Hr1. rename Hr1 into Hra1.
  unfolds in Hr2. rename Hr2 into Hrb1.
  simpl in Hr3.
  
  splits.
  {
    unfolds.
    unfolds;
      intros; eapply Hra1 in H6; 
      mytac;
      assert (x3 = ptcb \/ x3 <> ptcb) by tauto;
      destruct H7;
      try (subst;
           unfold get in H6; simpl in H6;
           rewrite H0 in H6;
           inverts H6;
           eapply EcbMod.join_sig_get in H3;
           rewrite H3 in H1;
           inverts H1);
      try (subst;
           unfold get in H6; simpl in H6;
           rewrite H0 in H6;
           inverts H6);
      repeat eexists;
      rewrite TcbMod.set_sem;
      rewrite tidspec.neq_beq_false; eauto.
  }
  {
    unfolds;
      unfolds;
      intros;
      assert (tid = ptcb \/ tid <> ptcb) by tauto;
      destruct H6;
      try subst;
      rewrite TcbMod.set_sem in H2;
      try (rewrite TcbMod.beq_refl in H2; inverts H2);
      rewrite tidspec.neq_beq_false in H2; eauto.
  }
  {
    simpl; auto.
  }
  
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Require Import sempend_pure.

Lemma ecblist_p_decompose :
  forall  y1 z1  x y2 z2 t z ,
    length y1 = length y2 ->
    ECBList_P x Vnull (y1++z1) (y2++z2) t z ->
    exists x1 t1 t2,
      ECBList_P x x1 y1 y2 t1 z /\ ECBList_P x1 Vnull z1 z2 t2 z /\
      EcbMod.join t1 t2 t /\  (get_last_ptr y1 = None \/ get_last_ptr y1  = Some x1).
Proof.
  inductions y1; inductions y2.
  simpl.
  intros.
  do 3 eexists; splits; eauto.
  eapply EcbMod.join_emp; eauto.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H; tryfalse.
  intros.
  simpl in H.
  inverts H.
  simpl in H0.
  mytac.
  destruct a.
  mytac.
  lets Hx : IHy1 H2 H4.
  mytac.
  lets Hex : joinsig_join_ex H1 H7.
  mytac.
  do 3 eexists.
  splits.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits.
  eauto.
  2: eauto.
  3: eauto.
  2 : eauto.
  eauto.
  eauto.
  assert (y1 = nil \/ y1 <> nil) by tauto.
  destruct H11.
  subst y1.  
  right.
  simpl in H2.
  apply eq_sym in H2.
  apply length_zero_nil in H2.
  subst y2.
  simpl in H5.
  mytac.

  destruct H8.
  left.
  eapply  get_last_prop in H11.
  eapply H11; eauto.
  eapply  get_last_prop in H11.
  right.
  eapply H11; eauto.
Qed.  

Lemma ECBList_P_hold_for_update_sem_to_rdy:
  forall head (els1 els2: list os_inv.EventCtr) osevent etbl osevent' etbl' ecblist1 ecblist2 ecbcurl ecbls 
         tcbls ct p ey egrp' y bitx qid ptbl vhold n wls,
    Int.unsigned p < 64 ->
    y = p >>ᵢ $ 3 ->
    bitx = $ 1<<ᵢ (p&ᵢ$ 7) ->
    R_PrioTbl_P ptbl tcbls vhold ->
    length els1 = length ecblist1 ->
    RH_TCBList_ECBList_P ecbls tcbls ct ->
    TcbMod.get tcbls ct = Some (p, wait qid) -> 
    EcbMod.get ecbls qid = Some (abssem n, wls) ->
    In ct wls ->
    get_ectr (Vptr qid) head els1  = None ->
    get_ectr (Vptr qid) head (els1 ++ ((osevent,etbl) :: nil))  = Some (osevent,etbl) -> 
    ECBList_P head Vnull (els1 ++ ((osevent,etbl) :: nil) ++ els2) 
      (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2) ecbls tcbls ->
    nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 ey ->
    osevent' = update_nth_val 1 osevent (Vint32 egrp') ->
    etbl' = update_nth_val (Z.to_nat (Int.unsigned y)) etbl (Vint32 (ey&ᵢInt.not bitx)) ->
    ECBList_P head Vnull (els1 ++ ((osevent',etbl') :: nil) ++ els2) 
      (ecblist1 ++ (ecbcurl :: nil) ++ ecblist2)
      (EcbMod.set ecbls qid (abssem n, remove_tid ct wls))
      (TcbMod.set tcbls ct (p, rdy)).
Proof.
  introv Hpr Hy Hbitx Hrpt Hl Hrte Htg Heg Hi Hgptr1.
  introv Hgptr2 Hep Hey Het' Hetbl'.
  assert (Hels1: els1 = nil \/ els1 <> nil) by tauto.
  destruct Hels1.
  { (* els1 = nil *) 
    subst els1.
    assert (ecblist1 = nil) by (eapply length_zero_nil; simpl in *; auto).
    subst ecblist1.
    simpl in *.
    mytac.
    destruct (beq_addrval qid x) eqn: eq1.
    2: {
      destruct (V_OSEventListPtr osevent); try tryfalse; destruct v; try tryfalse.
    }
    apply beq_addrval_eq in eq1.
    subst x.
    exists qid.
    splits; try auto.
    eapply R_ECB_ETbl_P_hold_for_update_sem_to_rdy; try eauto.
    exists (abssem n, remove_tid ct wls) x1 x2.
    splits; try auto.
    unfold V_OSEventListPtr in *.
    eapply nth_upd_neqrev; try pauto.
    unfold sig. unfold EcbMap.
    eapply EcbMod_get_join_sig_set; try eauto.
    eapply ejoin_get_none_r; [idtac | eauto].
    eapply EcbMod.map_get_sig.
    lets Heg': EcbMod.join_sig_get H2.
    destruct x0.
    rewrite Heg in Heg'.
    inverts Heg'.
    eapply RLH_ECBData_P_hold_sem; auto.
    eapply ECBList_P_high_tcb_block_hold_sem_to_rdy; try eauto.
    eapply ejoin_get_none_r; [idtac | eauto].
    eapply EcbMod.map_get_sig.
  }
  {
    (* els1 <> nil *)
    lets Hsp: ecblist_p_decompose Hl Hep.
    simpl in *.
    mytac.
    lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
    destruct H3; rewrite H1 in Hx2; inverts Hx2.
    eapply ecblist_p_compose; try eauto.
    2: {
      eapply ECBList_P_high_tcb_block_hold_sem_to_rdy; try eauto.
      eapply ejoin_get_none_l; [idtac | eauto].
      eapply EcbMod.join_sig_get; eauto.
    }
    eapply EcbMod.my_joinsig_join_set; try eauto.
    simpl.
    exists qid.
    splits; try auto.
    eapply R_ECB_ETbl_P_hold_for_update_sem_to_rdy; try eauto.
    exists (abssem n, remove_tid ct wls) x4 x5.
    splits; try auto.
    unfold V_OSEventListPtr in *.
    eapply nth_upd_neqrev; try pauto.
    unfold sig. unfold EcbMap.
    eapply EcbMod_get_join_sig_set; try eauto.
    eapply ejoin_get_none_r; [idtac | eauto].
    eapply EcbMod.map_get_sig.
    lets Heg': EcbMod.join_sig_get H6.
    destruct x3.
    lets Heg2: EcbMod.join_get_r H2 Heg'.
    rewrite Heg in Heg2.
    inverts Heg2.
    eapply RLH_ECBData_P_hold_sem; auto.
    eapply ECBList_P_high_tcb_block_hold_sem_to_rdy; try eauto.
    eapply ejoin_get_none_r; [idtac | eauto].
    eapply EcbMod.map_get_sig.
  }
Qed.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Lemma in_remove_tid : forall {l t1 t2}, In t1 (remove_tid t2 l) -> In t1 l.
Proof.
  inductions l; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct (beq_tid t2 a) eqn : eq1.
  simpl.
  right.
  eapply IHl; eauto.
  simpl in H.
  destruct H.
  substs.
  simpl; auto.
  simpl.
  right.
  eapply IHl; eauto.
Qed.

Lemma in_rem_neq:
  forall wls tid t, 
    In tid (remove_tid t wls) ->
    tid <> t.
Proof.
  inductions wls.
  - introv Hin. simpl in Hin. false. 
  - introv Hin'.
    simpl in Hin'.
    destruct (beq_addrval t a) eqn: E.
    + eapply IHwls; eauto.
    + apply in_inv in Hin'.
      destruct Hin' as [Hhd | Htl].
      * subst.
        introv He.
        subst.
        rewrite new_inv.beq_addrval_true in E.
        false. 
      * eapply IHwls; eauto.
Qed.         

Lemma in_remove_tid' : forall l t1 t2, In t1 l -> t1 <> t2 -> In t1 (remove_tid t2 l).
Proof.
  inductions l ; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct H; substs.
  simpl.
  destruct(beq_tid t2 t1) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; tryfalse.
  simpl; auto.
  simpl.
  destruct(beq_tid t2 a) eqn : eq1.
  eapply IHl; eauto.
  simpl.
  right.
  eapply IHl; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_hold_for_sem_to_rdy:
  forall tcbls ct p qid ecbls n wls,
    TcbMod.get tcbls ct = Some (p, wait qid) ->
    EcbMod.get ecbls qid = Some (abssem n, wls) ->
    In ct wls ->
    RH_TCBList_ECBList_P ecbls tcbls ct ->
    RH_TCBList_ECBList_P (EcbMod.set ecbls qid (abssem n, remove_tid ct wls)) 
      (TcbMod.set tcbls ct (p, rdy)) ct. 
Proof.
  introv Htg Heg Hi Hrte.
  unfolds in Hrte.
  unfolds.  
  unfolds.
  funfold Hrte.

  split.
  -
    intros.
    casetac eid qid Ht Hf.
    + subst.
      rewrite set_a_get_a in H1.
      destruct H1.
      inverts H1.
      lets Hne: in_rem_neq H2; eauto.
      rewrite set_a_get_a'; eauto.
      apply in_remove_tid in H2.
      eapply H; eauto.
    + rewrite set_a_get_a' in H1; eauto.
      lets H__: H H1; eauto.
      casetac ct tid Htt Hff.
      * subst.
        destruct H__ as (pp & Hgt).
        unfolds in Hgt. unfold TcbMap in Hgt.
        l_rew12 (TcbMod.get tcbls tid).
        false.
      * rewrite set_a_get_a'; eauto.
  -
    introv Hgt.
    casetac eid qid Ht Hf.
    + subst.
      casetac ct tid Htt Hff.
      * 
        subst.
        rewrite set_a_get_a in Hgt.
        inverts Hgt.
      *
        rewrite set_a_get_a' in Hgt; eauto.
        rewrite set_a_get_a.
        do 2 eexists; split; eauto.
        specializes H0; eauto.
        simpljoin1.
        unfold get, EcbMap in H0.
        l_rew12 (EcbMod.get ecbls qid).
        eapply in_remove_tid'; eauto.
    + rewrite set_a_get_a'; eauto.
      casetac ct tid Htt Hff.
      * subst.
        rewrite set_a_get_a in Hgt.
        inverts Hgt.
      * rewrite set_a_get_a' in Hgt; eauto.
Qed.         
      
Lemma ecblist_p_decompose_new:
  forall l1 ll1 l2 ll2 head ecbls tcbls eptr curl ecbcurl,
    length l1 = length ll1 ->
    get_ectr (Vptr eptr) head l1  = None ->
    get_ectr (Vptr eptr) head (l1 ++ (curl :: nil))  = Some curl ->
    ECBList_P head Vnull
      (l1++ (curl :: nil) ++ l2) (ll1 ++ (ecbcurl :: nil) ++ ll2) ecbls tcbls ->
    exists ecbls1 ecbls2,
      ECBList_P head (Vptr eptr) l1 ll1 ecbls1 tcbls /\
        ECBList_P (Vptr eptr) Vnull ((curl :: nil) ++ l2) ((ecbcurl :: nil) ++ ll2) ecbls2 tcbls /\
        EcbMod.join ecbls1 ecbls2 ecbls /\ 
        (get_last_ptr l1 = None \/ get_last_ptr l1 = Some (Vptr eptr)).
Proof.
  introv Hl Hgptr1 Hgptr2 Hep.
  assert (Hl1: l1 = nil \/ l1 <> nil) by tauto.
  destruct Hl1.
  subst l1.
  assert (ll1 = nil) by (eapply length_zero_nil; simpl in *; auto).
  subst ll1.
  simpl in *.
  destruct curl.
  mytac.
  destruct (beq_addrval eptr x) eqn: eq1.
  2: {
    destruct (V_OSEventListPtr v); try tryfalse; destruct v1; try tryfalse.
  }
  apply beq_addrval_eq in eq1.
  subst x.
  do 2 eexists.
  splits; try eauto.
  exists eptr. splits; try auto.
  do 3 eexists. splits; eauto.
  apply EcbMod.map_join_comm.
  apply EcbMod.map_join_emp.
  lets Hsp: ecblist_p_decompose Hl Hep.
  simpl in *.
  destruct curl.
  mytac.
  lets Hx2: get_ectr_sing H Hgptr1 Hgptr2.
  destruct H3; rewrite H1 in Hx2; inverts Hx2.
  do 2 eexists. splits; try eauto.
  exists eptr. splits; try auto.
  do 3 eexists. splits; eauto.
Qed.
