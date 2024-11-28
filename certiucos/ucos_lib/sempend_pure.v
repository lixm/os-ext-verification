Require Export sem_common.
Require Import Lia.

Open Scope code_scope.
Hint Resolve CltEnvMod.beq_refl: brel .


Lemma TCBListP_head_in_tcb:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'34 v'50 xx,
    TCBList_P (Vptr v'52)
      ((v'51
          :: v'22
          :: x9
          :: x8
          :: Vint32 i9
          :: Vint32 i8
          :: Vint32 xx
          :: Vint32 i6
          :: Vint32 i5
          :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33)
      v'34 v'50 ->
    exists st, TcbMod.get v'50 v'52 = Some (xx, st). 
Proof.
  intros.
  unfolds in H.
  fold TCBList_P in H.
  mytac.
  unfolds in H2.
  destruct x2. 
  mytac.
  unfolds in H2.
  unfolds in H4.
  simpl in H2.
  simpl in H4.
  inverts H2.
  inverts H4.
  inverts H.
  unfolds in H0; simpl in H0.
  inverts H0.
  unfold TcbJoin in H1.
  unfold join in H1; simpl in H1.
  unfolds in H1.
  eexists.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

(* several hypotheses are no longer needed due to the simplification *)
Lemma low_stat_rdy_imp_high:
  forall a b c d e f g h i j st rtbl p t,
    (* array_type_vallist_match Int8u rtbl -> *)
    (* length rtbl = ∘OS_RDY_TBL_SIZE -> *)
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: Vint32 f
         :: g
         :: h :: i :: j :: nil)
      rtbl (p, t) ->
    Int.eq st ($ OS_STAT_RDY) = true ->
    (* Int.eq e ($ 0) = true -> *)
    t = rdy .
Proof.
  introv (* Hmt Hlen *) Hr Heq.
  unfolds in Hr.
  destruct Hr as (Hlhr & Hhlr & Hlhw & Hhlw).
  destruct t; auto.
  unfolds in Hhlw.
  unfolds in Hhlw.
  specializes Hhlw; eauto.
  simpljoin.
  unfolds in H1. simpl in H1.
  inverts H1.
  false. 
  Unshelve.
Qed. 

(* Lemma low_stat_rdy_imp_high: *)
(*   forall a b c d e f g h i j st rtbl p t,  *)
(*     array_type_vallist_match Int8u rtbl -> *)
(*     length rtbl = ∘OS_RDY_TBL_SIZE -> *)
(*     RL_TCBblk_P  (a *)
(*                     :: b *)
(*                     :: c *)
(*                     :: d *)
(*                     :: Vint32 e *)
(*                     :: Vint32 st *)
(*                     :: Vint32 f *)
(*                     :: g *)
(*                     :: h :: i :: j :: nil) *)
(*     -> *)
(*       R_TCB_Status_P *)
(*         (a *)
(*            :: b *)
(*            :: c *)
(*            :: d *)
(*            :: Vint32 e *)
(*            :: Vint32 st *)
(*            :: Vint32 f *)
(*            :: g *)
(*            :: h :: i :: j :: nil) *)
(*         rtbl (p, t) -> Int.eq st ($ OS_STAT_RDY) = true -> *)
(*     Int.eq e ($ 0) = true -> *)
(*     t = rdy . *)
(*  Proof. *)
(*   introv Hz Hlen Ht Hr Heq Heqq.   *)
(*   funfold Ht. *)
(*   unfolds in Hr. *)
(*   mytac. *)
(*   clear H0 H2. *)
(*   unfolds in H. *)
(*   unfolds in H1. *)
(*   mytac. *)
(*   unfolds in H1. *)
(*   unfold RdyTCBblk in *. *)
(*   unfold V_OSTCBStat in *; simpl in *. *)
(*   unfold WaitTCBblk in *; simpl in *. *)
(*   unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *. *)
(*   assert (Some (Vint32 x) = Some (Vint32 x)). *)
(*   { auto. } *)
(*   unfold Pos.to_nat in Hlen. *)
(*   simpl in Hlen. *)
(*   assert ( 0 <= Int.unsigned x < 64 ) by lia. *)
(*   lets Hdis : prio_rtbl_dec  Hz Hlen; eauto. *)
(*   assert (if Int.eq x4 ($ OS_STAT_RDY) then  x4  =($ OS_STAT_RDY) *)
(*           else x4 <> ($ OS_STAT_RDY)). *)
(*   { apply Int.eq_spec. } *)
(*   rewrite Heq in H3. *)
(*   subst. *)
(*   destruct Hdis as [Hd1 | Hd2]. *)
(*   assert (Some (Vint32 x) = Some (Vint32 x) /\ *)
(*           prio_in_tbl x rtbl).  *)
(*   { split; auto. } *)
(*   apply H in H3. *)
(*   destruct H3 as ( _ & Had & Hzd).  *)
(*   inverts Hzd.  *)
(*   auto. *)
  
(*   assert (Some (Vint32 e) = Some (Vint32 e)). *)
(*   { auto. } *)
(*   assert (Some (Vint32 x) = Some (Vint32 x) /\ *)
(*           prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 e)).    *)
(*   { splits; auto. } *)
(*   apply H0 in H11; auto. (* change H9 -> H11 *) *)
(*   mytac. *)
(*   apply ltu_eq_false in H11. (* change H9 -> H11 *) *)
(*   unfold Int.zero in H11. (* change H9 -> H11 *) *)
(*   rewrite Heqq in H11. (* change H9 -> H11 *) *)
(*   tryfalse. *)
(* Qed. *)
 
Lemma sempend_TCBListP_head_in_tcb_rdy:
  forall v'51 v'52 v'22 x9 x8 i9 i8 i6 i5 i4 i3 v'33 v'50 xx rtbl,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    TCBList_P (Vptr v'52)
              ((v'51
                  :: v'22
                  :: x9
                  :: x8
                  :: Vint32 i9
                  :: Vint32 i8
                  :: Vint32 xx
                  :: Vint32 i6
                  :: Vint32 i5
                  :: Vint32 i4 :: Vint32 i3 :: nil) :: v'33)
              rtbl v'50 ->
    i9 = $ 0 ->
    i8 = $ OS_STAT_RDY ->
    TcbMod.get v'50 v'52 = Some (xx, rdy).
Proof.
  intros.
  unfolds in H1.
  fold TCBList_P in H1.
  mytac_H.
  unfolds in H6.
  destruct x2.
  mytac_H.
  unfolds in H4; unfolds in H2; unfolds in H3.
  simpl in H2; simpl in H4; simpl in H3.
  inverts H2; inverts H4; inverts H3.
  assert (t = rdy).
  { eapply low_stat_rdy_imp_high; eauto. }
  subst t.
  inverts H1.
  unfold TcbJoin in H5.
  eapply TcbMod.join_get_l.
  eauto.
  eapply TcbMod.get_a_sig_a.
  apply CltEnvMod.beq_refl.
Qed.

Lemma tcblist_p_node_rl_sem:
  forall v'33 v'49 v'42 v'47 v'21 x10 x9 i i8 i7 i6 i5 i4 i3 i1 v'32 ,
    TCBList_P (Vptr (v'49, Int.zero))
          ((v'47
            :: v'21
               :: x10
                  :: x9
                     :: Vint32 i8
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3 :: Vint32 i1 :: nil) :: v'32)
          v'33 v'42 ->
    RL_TCBblk_P
     (v'47
      :: v'21
         :: x10
            :: x9
               :: Vint32 i
                  :: V$OS_STAT_SEM
                     :: Vint32 i6
                        :: Vint32 i5
                           :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: nil).
Proof.
  introv Ht.
  simpl in Ht.
  mytac;simpl_hyp.
  inverts H.
  unfolds in H2.
  destruct x2.
  mytac; simpl_hyp.
  funfold H0.
  unfolds.
  do 6 eexists;splits; try unfolds; simpl;  eauto.
  splits; auto.
  eexists.
  splits.
  unfolds.
  simpl; eauto.
  introv Hf.
  inverts Hf.
Qed.

(* same copy from Mbox_common.v *)
(* Lemma R_ECB_PETbl_P_set_tcb_wait_hold: *)
(*   forall tcbls ptcb prio m st m' x v0 v1 v prio', *)
(*     ~(exists qid, st = wait qid) ->  *)
(*     TcbMod.get tcbls ptcb = Some (prio, rdy, m) -> *)
(*     R_ECB_PETbl_P x (v0, v1, v) tcbls -> *)
(*     R_ECB_PETbl_P x (v0, v1, v) *)
(*       (TcbMod.set tcbls ptcb (prio', st, m')). *)
(* Proof. *)
(* intros. *)
(* funfold H1. *)
(* unfolds; splits; unfolds; intros. *)
(* eapply H1 in H4; eauto. *)
(* mytac. *)
(* unfold get in *; unfold TcbMap in *. *)
(* assert (Hc: ptcb = x0 \/ ptcb <> x0) by tauto. *)
(* destruct Hc. *)
(* subst. *)
(* rewrite H0 in H4; inverts H4. *)
(* repeat eexists. *)
(* rewrite TcbMod.set_a_get_a'; eauto. *)
(* eapply tidspec.neq_beq_false; eauto. *)
(* unfold get in *; unfold TcbMap in *. *)
(* assert (Hc: ptcb = tid \/ ptcb <> tid) by tauto. *)
(* destruct Hc. *)
(* subst. *)
(* rewrite TcbMod.map_get_set in H3. *)
(* inverts H3. *)
(* false. eapply H; eauto. *)
(* rewrite TcbMod.map_get_set' in H3; auto. *)
(* eapply H2; eauto. *)
(* Qed. *)
  
Lemma ECBList_P_high_tcb_block_hold_sem:
  forall  ectrl head tail msgql ecbls tcbls ptcb prio qid,
    ECBList_P head tail ectrl msgql ecbls tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, rdy) ->
    EcbMod.get ecbls qid = None ->
    ECBList_P head tail ectrl msgql ecbls 
      (TcbMod.set tcbls ptcb (prio, wait qid)). 
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
  unfolds.
  {
    unfolds.
    intros.
    eapply Hra1 in H6;eauto.
    mytac.
    assert (x3 = ptcb \/ x3 <> ptcb) by tauto.
    destruct H7.
    subst.
    unfold get in H6; simpl in H6.
    rewrite H0 in H6.
    inverts H6.
    exists x3.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  }

  unfolds.

  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.
    destruct H6.
    subst.
    rewrite TcbMod.set_sem in H2.
    rewrite tidspec.eq_beq_true in H2; eauto.
    inverts H2.
    apply ecbmod_joinsig_get in H3.
    rewrite H3 in H1.
    tryfalse.
    rewrite TcbMod.set_sem in H2.
    rewrite tidspec.neq_beq_false in H2; eauto.
  }

  simpl; auto.
  do 3 eexists; splits; eauto.
  eapply IHectrl; eauto.
  eapply  ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ejoin_get_none_r :
  forall ma mb mc x a,
    EcbMod.get ma x = Some a ->
    EcbMod.join ma mb mc ->
    EcbMod.get mb x = None.  
Proof.
  intros.
  unfolds in H0.
  lets adf : H0 x.
  destruct (EcbMod.get ma x).
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
  destruct (EcbMod.get mb x).
  tryfalse.
  auto.
Qed.

Lemma ejoin_get_none_l :
  forall ma mb mc x a,
    EcbMod.get mb x = Some a ->
    EcbMod.join ma mb mc ->
    EcbMod.get ma x = None. 
Proof.
  intros.
  apply EcbMod.join_comm in H0.
  eapply ejoin_get_none_r; eauto.
Qed.

Lemma R_ECB_ETbl_P_high_tcb_block_hold:
  forall (l : addrval) (vl : vallist) (egrp : int32) 
         (v2 v3 v4 v5 : val) (etbl : vallist) (tcbls : TcbMod.map)
         (ptcb : tidspec.A) (prio : int32) (st : taskstatus) 
         (y bity bitx ey : int32) (av : addrval), 
    Int.unsigned prio < 64 ->
    R_PrioTbl_P vl tcbls av ->
    R_ECB_ETbl_P l
      (V$OS_EVENT_TYPE_SEM :: Vint32 egrp :: v2 :: v3 :: v4 :: v5 :: nil, etbl)  
      tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st) ->
    y = Int.shru prio ($ 3) ->
    bity = Int.shl ($ 1) y ->
    bitx = Int.shl ($ 1) (prio &ᵢ $ 7) ->
    nth_val ∘(Int.unsigned y) etbl = Some (Vint32 ey) ->
    R_ECB_ETbl_P l
      (V$OS_EVENT_TYPE_SEM
         :: Vint32 (Int.or egrp bity) :: v2 :: v3 :: v4 :: v5 :: nil,
        update_nth_val ∘(Int.unsigned y) etbl (Vint32 (Int.or ey bitx))) 
      (TcbMod.set tcbls ptcb (prio, wait l)). 
Proof.
  introv Hran Hrs  Hre Htc Hy Hb1 Hb2 Hnth.
  subst.
  unfolds in Hre.
  destruct Hre as (Hre1 & Hre2 & Het).
  unfolds.
  splits.
  unfolds.

  {
    unfolds.
    intros.
    unfolds in Hre1.
    unfolds in Hre2.
    unfolds in Hre1.
    unfolds in Hre2.
    assert (prio = $ prio0 \/ prio <> $ prio0) by tauto.
    destruct H1.
    subst.
    exists ptcb.
    rewrite TcbMod.set_sem.
    erewrite tidspec.eq_beq_true; eauto.
    lets Hres : prio_wt_inq_keep Hran H1 Hnth .
    destruct Hres.
    apply H2 in H.
    apply Hre1 in H.
    mytac.
    exists x.
    assert (x = ptcb \/ x <> ptcb) by tauto.
    destruct H4.
    subst.
    unfold get in H; simpl in H.
    rewrite Htc in H.
    inverts H.
    tryfalse.
    rewrite TcbMod.set_sem.
    erewrite tidspec.neq_beq_false; eauto.
    unfolds. 
    simpl; auto.
  }
  
  unfolds.
  {
    unfolds.
    intros.
    assert (tid = ptcb \/ tid <> ptcb) by tauto.  
    destruct H0.
    subst.
    splits.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    unfolds.
    rewrite Int.repr_unsigned.
    exists ( prio0 &ᵢ $ 7).
    exists (Int.shru prio0 ($3)).
    exists ((Int.or ey ($ 1<<ᵢ(prio0 &ᵢ $ 7)))).
    splits; eauto.
    clear - Hran.
    int auto.
    eapply pure_lib.update_nth; eauto.
    rewrite Int.and_commut.
    rewrite Int.or_commut.
    unfold Int.one.
    rewrite Int.and_or_absorb.
    auto.
    unfolds; simpl; auto.
    rewrite TcbMod.set_sem in H.
    erewrite tidspec.neq_beq_false in H; eauto.
    unfolds in Hre2.
    lets Hasd : Hre2  H.
    destruct Hasd as (Has1 & Has2).
    splits.
    eapply prio_wt_inq_keep; eauto.
    rewrite Int.repr_unsigned.
    unfolds  in Hrs.
    destruct Hrs.
    destruct H2.
    unfolds in H3.
    lets Hdd : H3 H0 H Htc.
    eauto.
    unfolds; simpl; auto.
  }
  
  unfolds; simpl; auto.
Qed.

Lemma RLH_Rdy_prioneq_prop_hold:
  forall p prio a rtbl t grp,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_RdyI_P a rtbl (p, t)  ->
    RLH_RdyI_P a
               (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                               (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t). 
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  intros.
  eapply Hrl; auto.
  unfolds in H.
  unfolds.
  simpljoin; try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Rdy_prioneq_prop_hold:
  forall p prio a rtbl t grp,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_RdyI_P a rtbl (p, t)  ->
    RHL_RdyI_P a
               (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                               (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  intros.
  lets Hs : Hrl H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_neq_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RLH_Wait_prioneq_prop_hold:
  forall p prio a rtbl t grp,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_TCB_Status_Wait_P a rtbl (p, t) ->
    RLH_TCB_Status_Wait_P a
                          (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                          (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  (* destruct Hrl as (Hrl1 & Hrl2 & Hrl3 & Hrl4 & Hrl5  & Hrl6). *)
  (* splits. *)
  unfolds in Hrl.
  unfolds.
  intros.
  eapply Hrl; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_neq_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Wait_prioneq_prop_hold:
  forall p prio a rtbl t grp,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_TCB_Status_Wait_P a rtbl (p, t) ->
    RHL_TCB_Status_Wait_P a
                          (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                          (Vint32 (grp&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) (p, t).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  (* destruct Hrl as (Hrl1 & Hrl2 & Hrl3 & Hrl4 & Hrl5 & Hrl6). *)
  (* splits. *)
  unfolds in Hrl.
  unfolds.
  intros.
  lets Hex : Hrl H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_neq_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma update_rtbl_tcblist_hold:
  forall vl vptr rtbl tcbls prio grp,
    0<= Int.unsigned prio < 64 ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    (forall tid a b, TcbMod.get tcbls tid  = Some (a,b) -> a <> prio) -> 
    TCBList_P vptr vl rtbl tcbls ->
    TCBList_P vptr vl
      (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
         (Vint32 (grp &ᵢInt.not ($ 1<<ᵢ(prio &ᵢ$ 7))))) tcbls.
Proof.
  inductions vl.
  intros; simpl in *.
  auto.
  intros.
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin;try splits.
  exists x x0 x1 x2.
  splits; auto.
  unfolds in H5.
  unfolds.
  destruct x2.
  (* destruct p. *)
  simpljoin;try splits; auto.
  lets Hds : tcbjoin_get_a H4. 
  apply H1 in Hds.
  unfolds in H7.
  unfolds.
  lets Hran : tcbblk_prio_range H5 H2.
  unfolds in H8. 
  simpljoin; try splits. 
  eapply RLH_Rdy_prioneq_prop_hold; eauto.
  eapply RHL_Rdy_prioneq_prop_hold; eauto.
  eapply RLH_Wait_prioneq_prop_hold; eauto.
  eapply RHL_Wait_prioneq_prop_hold; eauto.
  eapply IHvl; auto.
  intros; eapply H1.  
  eapply tcbjoin_get_get; eauto.
Qed.  

Lemma TCBList_P_tcb_block_hold :
  forall ptcb v1 v2 v3 v5 v6 v8 v9 v10 v11 rtbl vl
         tcbls prio st m qid time ry,
    TCBList_P (Vptr ptcb) ((v1::v2::v3::m::v5::(Vint32 v6)::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)::vl) rtbl tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st) -> 
    prio_neq_cur tcbls ptcb (prio) ->
    st = rdy -> 
    nth_val (nat_of_Z (Int.unsigned v9)) rtbl = Some (Vint32 ry) ->
    TCBList_P (Vptr ptcb)
      ((v1::v2::(Vptr qid)::m::(Vint32 time)::(Vint32 ($ OS_STAT_SEM))::(Vint32 prio)::v8::(Vint32 v9)::(Vint32 v10)::v11::nil)
         ::vl) 
      (update_nth_val ∘(Int.unsigned v9) rtbl (Vint32 (Int.and ry (Int.not v10)))) 
      (TcbMod.set tcbls ptcb (prio, wait qid)). 
Proof.
  introv  Htcb Htm Hst Hprio Hnth.
  unfolds in Htcb;fold TCBList_P in Htcb.
  mytac.
  inverts H.
  unfolds in H0.
  simpl in H0; inverts H0.
  unfolds.
  fold TCBList_P.
  exists x x0.
  exists x1.
  exists (prio,wait qid).
  splits; eauto.
  eapply tcbjoin_set; eauto.
  {
    unfolds in H2.
    destruct x2.
    mytac.
    unfolds in H.
    simpl in H; inverts H.
    unfolds.
    funfold H0.
    split.
    auto. 

    split.
    unfolds.
    do 6 eexists; splits; try unfolds; simpl; eauto.
    splits; eauto.
    eexists.
    splits.
    unfolds;simpl; eauto.
    introv Hf.
    inverts Hf.
    
    lets Hexa : tcbjoin_get H1 Htm.
    inverts Hexa.
    unfolds in H2.
    split.
    unfolds.
    intros.
    simpl_hyp.
    unfolds in H.
    destruct H.
    simpl_hyp.
    unfolds in H0.
    assert (prio&ᵢ$ 7 = prio&ᵢ$ 7) by auto.
    assert (Int.shru ( prio) ($ 3) =Int.shru (prio) ($ 3)) by auto.
    assert ( nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3)))
               (update_nth_val ∘(Int.unsigned (Int.shru (prio) ($ 3))) rtbl
                  (Vint32 (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
               Some (Vint32  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))))).
    eapply pure_lib.update_nth; eauto.
    lets Hr: H0 H H4 H5.
    rewrite Int.and_assoc in Hr.
    assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
    {
      rewrite Int.and_commut.
      rewrite Int.and_not_self.
      auto.
    }
    rewrite H6  in Hr.
    rewrite Int.and_zero in Hr.
    assert ($ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply  math_prop_neq_zero2; try lia).
    {
      unfold Int.zero in Hr.
      tryfalse.
    }
    split.
    unfolds.
    intros.
    inverts H.
    split.
    unfolds.
    
    unfolds.
    intros.
    inverts H0.
    inverts H4.
    unfolds in H.
    mytac.
    inverts H.
    auto.

    unfolds.
    unfolds.
    intros.
    inverts H.
    split.
    unfolds.
    splits; try unfolds ; simpl ; auto.

    intros.
    subst.
    apply nth_upd_eq in H4.
    inverts H4.
    rewrite Int.and_assoc.
    assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
    {
      rewrite Int.and_commut.
      rewrite Int.and_not_self.
      auto.
    }
    rewrite H.
    rewrite  Int.and_zero.
    auto. 

    split.
    unfolds; simpl; auto.
    unfolds; simpl; auto.
  }
  
  unfolds in H2.
  destruct x2.
  mytac; simpl_hyp.
  funfold H0.

  
  eapply update_rtbl_tcblist_hold; eauto.
  unfolds in Hst.
  intros.
  lets Has : tcbjoin_get_getneq H1 H.
  destruct Has.
  eapply Hst; eauto.
Qed.

Lemma RH_CurTCB_high_block_hold_sem :
  forall ptcb tcbls prio st qid, 
    RH_CurTCB ptcb tcbls ->
    TcbMod.get tcbls ptcb = Some (prio, st) ->
    RH_CurTCB ptcb (TcbMod.set tcbls ptcb (prio, wait qid)).                        
Proof.
  introv Hr Ht.
  unfolds in Hr.
  mytac.
  unfold get in H; simpl in H.
  rewrite H in Ht.
  inverts Ht.
  unfolds.
  do 2 eexists.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; eauto.
Qed.

Lemma RH_TCBList_ECBList_P_high_block_hold_sem :
  forall ecbls tcbls pcur qid cnt wl prio,  
    RH_TCBList_ECBList_P ecbls tcbls pcur ->
    EcbMod.get ecbls qid = Some (abssem cnt, wl) ->
    TcbMod.get tcbls pcur = Some (prio, rdy) -> 
    RH_TCBList_ECBList_P
      (EcbMod.set ecbls qid (abssem cnt, pcur::wl))
      (TcbMod.set tcbls pcur (prio, wait qid)) pcur.   
Proof.
  introv Hr Ht He.
  unfolds in Hr.
  rename Hr into Hr1.
  (* destruct Hr as (Hr3 & Hr1 & Hr2 & Hr4). *)
  unfolds.

  {
    unfolds.
    splits.
    intros.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H1.
    subst.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; auto.
    inverts H.
    simpl in H0.
    destruct H0.
    eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
    assert (EcbMod.get ecbls eid = Some (abssem n, wl) /\ In tid wl) by eauto.
    apply Hr1 in H0.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H1.
    eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.eq_beq_true; auto.
    eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    rewrite EcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; auto.
    assert (EcbMod.get ecbls eid = Some (abssem n, wls) /\ In tid wls) by eauto.
    apply Hr1 in H2.
    mytac.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H3.
    subst.
    unfold get in H2; simpl in H2.
    rewrite H2 in He.
    inverts He. 
    eexists;
    rewrite TcbMod.set_sem ;
    rewrite tidspec.neq_beq_false; eauto.
    intros.
    assert (pcur = tid \/ pcur <> tid) by tauto.
    destruct  H0.
    subst.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.eq_beq_true in H; eauto.
    inverts H.
    exists cnt.
    exists (tid::wl).
    splits; eauto.
    rewrite EcbMod.set_sem.
    rewrite tidspec.eq_beq_true; eauto.
    simpl; left; auto.
    rewrite TcbMod.set_sem in H.
    rewrite tidspec.neq_beq_false in H; eauto.
    apply Hr1 in H.
    mytac.
    assert (qid  = eid \/ qid <> eid) by tauto.
    destruct H2.
    subst.
    rewrite EcbMod.set_sem.
    rewrite tidspec.eq_beq_true; auto.
    do 2 eexists; splits; eauto.
    unfold get in H; simpl in H.
    rewrite H in Ht.
    inverts Ht.
    simpl.
    right; auto.
    rewrite EcbMod.set_sem.
    rewrite tidspec.neq_beq_false; auto.
    do 2 eexists; splits; eauto.
  }

Qed.


