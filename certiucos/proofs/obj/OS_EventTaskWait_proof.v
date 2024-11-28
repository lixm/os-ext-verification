
(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(**Proof of Internal Fucntion: void OS_EventTaskWait(OS_EVENT* pevent) **)
(**************************** Code:***********************************)
(*
Void ·OS_EventTaskWait·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ ⌟;

1       OSTCBCur′→OSTCBEventPtr =ₑ pevent′;ₛ
2       OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ 
                 OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
3       If (OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0)
        {
4           OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼OSTCBCur′→OSTCBBitY)
        };ₛ
5       pevent′→OSEventTbl[OSTCBCur′→OSTCBY] =ₑ 
               pevent′→OSEventTbl[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
6       pevent′→OSEventGrp =ₑ pevent′→OSEventGrp |ₑ OSTCBCur′→OSTCBBitY;ₛ
7       RETURN
}·. 
*)

(* Require Import ucert. *)
Require Import ucos_include.
Require Import OSETWaitPure.
Require Import Lia.

Open Scope code_scope.

Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma event_wait_rl_tbl_grp':
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 i1 i0 v'1 x,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'1 ->
    Int.eq (x&ᵢInt.not i2) ($ 0) = true ->
    RL_Tbl_Grp_P v'1 (Vint32 i0) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'1 (Vint32 (x&ᵢInt.not i2)))
      (Vint32 (i0&ᵢInt.not i1)).
Proof.
  introv Hrl Harr  Hint Hrll.
  assert (if Int.eq (x&ᵢInt.not i2) ($ 0) then
            (x&ᵢInt.not i2)  = $ 0 else   (x&ᵢInt.not i2)  <> $ 0  ) by (apply Int.eq_spec).
  rewrite Hint in H.
  rewrite H.
  unfolds in Hrl.
  funfold Hrl.
  funfold Hrll.
  unfolds.
  introv Hn Hnth Hvin.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))) by tauto.
  destruct H0.
  lets Hex : nth_upd_neq H0 Hnth.
  assert (Vint32 i0 = Vint32 i0) by auto.
  lets Hes : Hrll Hn Hex H1.
  destruct Hes.
  inverts Hvin.
  lets Hzx : math_prop_and H0; try lia; auto.
  splits.
  destruct H2.
  split.
  intros.
  apply H2.
  rewrite Int.and_assoc in H5. 
  rewrite Hzx in H5.
  auto.
  intros.
  apply H4 in H5.
  rewrite Int.and_assoc.
  rewrite Hzx ; auto.
  split.
  intros.
  destruct H3.
  rewrite Int.and_assoc in H4.
  rewrite Hzx in H4.
  apply H3; auto.  
  intros.
  rewrite Int.and_assoc.
  rewrite Hzx.
  apply H3; auto.
  subst n.
  lets Hdx : nth_upd_eq Hnth.
  inverts Hdx.
  inverts Hvin.
  assert ( 0 <= Int.unsigned x0 < 64) by lia.
  lets Hdd : math_prop_eq0 H0.
  split.
  split; auto.
  intros.
  rewrite Int.and_assoc.
  rewrite Hdd.
  rewrite Int.and_zero.
  auto.
  rewrite Int.and_assoc.
  rewrite Hdd.
  rewrite Int.and_zero.
  split.
  intros.
  apply math_lshift_neq_zero in H0.
  tryfalse.
  intros.
  clear -H1.
  false.
Qed.

Lemma event_wait_rl_tbl_grp:
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 v'5 x0 i i1,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'5 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'5 = Vint32 x0 ->
    RL_Tbl_Grp_P v'5 (Vint32 i) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'5 (Vint32 (Int.or x0 i2)))
      (Vint32 (Int.or i i1)).
Proof.
  introv Hrl Harr Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x < 64) as Hran by lia.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 i = Vint32 i) by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  split.
  split.
  intros.
  apply He1.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  
  lets Hc : math_and_zero Hran Hn H.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  lets Hc : math_and_zero Hran Hn H.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He1; auto.
  lets Hc : math_and_zero Hran Hn H.
  split.
  intros.
  apply He2.
  rewrite Int.and_commut in H1.
  rewrite Int.and_or_distrib in H1.
  rewrite Hc in H1.
  rewrite Int.or_zero in H1.
  rewrite Int.and_commut.
  auto.
  intros.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  rewrite Hc.
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  apply He2; auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
  inverts Hins.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib .
  split.
  split.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  lets Hf : math_prop_neq_zero Hran.
  tryfalse.
  intros.
  apply int_or_zero_split in H.
  destruct H.
  apply math_prop_neq_zero2 in H0.
  tryfalse.
  auto.
  split.
  intros.
  apply int_ltu_true; auto.
  intros.
  rewrite math_prop_eq; auto.
  rewrite Int.and_idem.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
Qed.

Lemma event_wait_rl_tbl_grp'':
  forall x10 x9 x8 x7 i10 i6 i5 i4 i3 i2 i1 i0 v'1 x,
    RL_TCBblk_P
      (x10
         :: x9
         :: x8
         :: x7
         :: Vint32 i10
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) ->
    array_type_vallist_match Int8u v'1 ->
    nth_val' (Z.to_nat (Int.unsigned i3)) v'1 = Vint32 x ->
    Int.eq (x&ᵢInt.not i2) ($ 0) = false ->
    RL_Tbl_Grp_P v'1 (Vint32 i0) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned i3)) v'1 (Vint32 (x&ᵢInt.not i2)))
      (Vint32 i0).
Proof.
  introv Hrl Harr Htt Hnth Hrt.
  funfold Hrl.
  funfold Hrt.
  assert ( 0 <= Int.unsigned x0 < 64) as Hran by lia.
  clear H5 H13.
  unfolds.
  introv Hn Hnv Hvi.
  inverts Hvi.
  assert (n <> (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3)))) \/
          n = (Z.to_nat (Int.unsigned (Int.shru x0 ($ 3))))) by tauto.
  destruct H.
  lets Hex : nth_upd_neq H Hnv.
  assert (Vint32 v' = Vint32 v') by auto.
  lets Hexz : Hrt Hn Hex H0.
  destruct Hexz as (He1 & He2).
  auto.
  subst n.
  lets Hins : nth_upd_eq  Hnv.
   apply nth_val'_imp_nth_val_int in Htt.
   assert (Vint32 v' = Vint32 v') by auto.
  lets Hdx : Hrt Hn Htt H.
  inverts Hins.
  split.
  split.
  destruct Hdx.
  intros.
  apply H0 in H2.
  subst.
  rewrite Int.and_commut.
  rewrite Int.and_zero.
  auto.
  intros.
  rewrite H0 in Hnth.
  rewrite Int.eq_true in Hnth.
  tryfalse.
  split.
  intros.
  destruct Hdx.
  apply H2 in H0.
  apply int_eq_false_ltu; eauto.
  intros.
  destruct Hdx.
  apply H2.
  apply int_eq_false_ltu; eauto.
  apply Int.eq_false.
  assert (   x <> $ 0  \/  x = $ 0) by tauto.
  destruct H3; auto.
  subst x.
  rewrite Int.and_commut in Hnth.
  rewrite Int.and_zero in Hnth.
  unfold Int.zero in Hnth.
  rewrite Int.eq_true in Hnth.
  tryfalse.
Qed.

Lemma OSEventTaskWait_proof:
  forall tid vl p r ll, 
    Some p =
      BuildPreI os_internal OS_EventTaskWait
        vl ll OS_EventTaskWaitPre tid ->
    Some r =
      BuildRetI os_internal OS_EventTaskWait vl ll OS_EventTaskWaitPost tid ->
    exists t d1 d2 s,
      os_internal OS_EventTaskWait = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}} s {{Afalse}}. 
Proof. 
  init_spec.
  hoare unfold.

  hoare forward.
  hoare unfold.

  lets Hi3: range_ostcby H.
  destruct Hi3 as [Hi3 Hi2].
  assert (Z.to_nat (Int.unsigned i3) < length v'0)%nat.
  {
    rewrite H8.
    unfold OS_RDY_TBL_SIZE.
    
    apply z_le_7_imp_n;auto.
    lia.
  }
  
  lets Hx: array_int8u_nth_lt_len H2 H12.
  Import DeprecatedTactic.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)

(* ** ac:   Locate array_type_vallist_match_imp_rule_type_val_match. *)
  Import symbolic_lemmas.
  
  eapply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  
  apply z_le_7_imp_n;auto.
  lia.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.
  rewrite H27.
  auto.

  go.
  (* simpl;splits;pauto. *)
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  (*
  Focus 2.
  hoare lift 8%nat pre.
  apply backward_rule1 with Afalse.
  intros.

  sep remember (1::nil)%nat in H2.
  simpl in H2.
  mytac;auto.
  apply pfalse_rule.
   *)
  unfold AOSRdyGrp.
  hoare forward.
  (* simpl;splits;pauto. *)
  go.
  rewrite H27.

  rewrite <- update_nth_val_length_eq.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite len_lt_update_get_eq.
  rewrite H27.
  simpl.
  rtmatch_solve.
  apply int_lemma1;auto.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  rewrite H27.
  rewrite len_lt_update_get_eq.
  simpl.
(* ** ac:   Locate "$". *)
  Local Open Scope int_scope.
  destruct (Int.eq (x&ᵢInt.not i2) ($ 0));auto.
  rewrite H8.
  unfold OS_RDY_TBL_SIZE.
  simpl Z.of_nat.
  auto.
  
  eapply forward_rule2.
  hoare forward.

  go.
  (* simpl;splits;pauto. *)
  unfold val_inj.
  unfold and.

  destruct v'1;tryfalse.
  auto.
  intros.
  apply H29.
  apply disj_rule;pure intro.
  clear H35 H33 H34.
  
  assert (Z.to_nat (Int.unsigned i3) < length v'4)%nat.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  lets Hx:array_int8u_nth_lt_len H4 H33.
  mytac.
  hoare forward.
  go.
  (* simpl;splits;pauto. *)
  rewrite H34.
  simpl.
  rtmatch_solve.
  go.
  (* simpl;splits;pauto. *)
  rewrite H34.
  simpl.
  auto.
  go.
  (* simpl;splits;pauto. *)

  eapply eq_int;auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
  simpl;auto.
  simpl;auto.
  2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto.
  splits;auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H27.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H34.
  simpl.
  auto.
  split;auto.
  rewrite H27.
  simpl.
  rewrite H27 in H30.
  rewrite len_lt_update_get_eq in H30.
  assert (Int.eq (x &ᵢInt.not i2) ($ 0) =true).
  clear -H30.
  simpl in H30.
  simpl.
  destruct (Int.eq (x &ᵢInt.not i2) ($ 0));tryfalse;auto.

  eapply event_wait_rl_tbl_grp';eauto.
  rewrite H8.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H27.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  apply int_lemma1;auto.
  split.
  rewrite H27.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  lia.
  rewrite H27.

  rewrite <- update_nth_val_length_eq.
  auto.
  go.

  rewrite H34.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  apply array_type_vallist_match_hold;auto.
  rewrite H34.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_unsigned_or_prop';auto.
  pauto.
  pauto.
  pauto.

  (*------------------------------*)
   
  assert (Z.to_nat (Int.unsigned i3) < length v'4)%nat.
  rewrite H9.
  unfold OS_EVENT_TBL_SIZE.
  apply z_le_7_imp_n;auto.
  lia.
  lets Hx:array_int8u_nth_lt_len H4 H31.
  mytac.
  hoare forward.
  go.

  rewrite H32.
  simpl.
  rtmatch_solve.
  go.
  rewrite H32.
  simpl.
  auto.
  go.

  eapply eq_int;auto.

  hoare forward.
  go.
  go.
  
  hoare forward.
   simpl;auto.
  simpl;auto.
  2:simpl;auto.
  2:auto.
  4:simpl;auto.
  5:auto.
  6:simpl;auto.
  splits;auto.
  eapply nth_val'_imp_nth_val_int;eauto.
  simpl.
 
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H27.

  simpl.
  auto.
  rewrite unsigned_to_z_eq.
  eapply nth_val'_imp_nth_val_int;eauto.
  splits;auto.
  rewrite <- unsigned_to_z_eq.
  rewrite unsigned_to_z_eq.
  rewrite H32.
  simpl.
  auto.
  split;auto.
  rewrite H27.
  simpl.
  rewrite H27 in H30.
  rewrite len_lt_update_get_eq in H30.
  assert (Int.eq (x &ᵢInt.not i2) ($ 0) = false).
  clear -H30.
  simpl in H30.
  destruct H30.
  simpl in H.
  destruct (Int.eq (x &ᵢInt.not i2) ($ 0));tryfalse;auto.
  simpl in H.
  destruct (Int.eq (x &ᵢInt.not i2) ($ 0));tryfalse;auto.
  

  eapply event_wait_rl_tbl_grp'';eauto.
  rewrite H8.
  simpl;auto.
  unfold and.
  unfold val_inj.
  rewrite H27.
  eapply idle_in_rtbl_hold;eauto.

  rtmatch_solve.
  split.
  rewrite H27.

  eapply array_type_vallist_match_int8u_update_hold;eauto.
  lia.
  rewrite H27.

  rewrite <- update_nth_val_length_eq.
  auto.
  go.
  simpl.
  rewrite H32.
  eapply event_wait_rl_tbl_grp;eauto.
  simpl;auto.
  apply array_type_vallist_match_hold;auto.
  rewrite H32.
  rtmatch_solve.
  apply int_unsigned_or_prop;auto.
  simpl;splits;auto.
  rtmatch_solve.
  rtmatch_solve.
  apply int_unsigned_or_prop';auto.
  pauto.
  pauto.
  pauto.

Qed.
