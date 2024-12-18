Require Import sem_common.
Require Import Lia.
(* Require Import Mbox_common. (* new add *) *)

Open Scope code_scope.

Lemma sem_ecb_wt_ex_prop :
  forall grp etbl v x v'21 v'23 mqls tcbls cnt x2 x3 v'42 ecbls tid pegrp,
    Int.eq grp ($ 0) = false ->
    Int.unsigned grp <= 255 ->
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_EVENT_TBL_SIZE ->
    RL_Tbl_Grp_P etbl (Vint32 grp) -> 
    ECBList_P v (Vptr x)  v'21 v'23 mqls tcbls->
    R_ECB_ETbl_P x
                 (V$OS_EVENT_TYPE_SEM
                   :: Vint32 grp
                   :: Vint32 cnt :: x2 :: x3 :: v'42 :: Vint32 pegrp :: nil,
                  etbl) tcbls ->
    RH_TCBList_ECBList_P ecbls tcbls tid ->
    exists cnt' t' tl,
      EcbMod.get ecbls x = Some (abssem cnt', t' :: tl).
Proof.
  introv Hinteq Hiu Harr Hlen  Hrl Hep Hrp Hz.
  unfolds in Hrp.
  unfolds in Hrl.
  lets Hex : int8_neq0_ex Hiu Hinteq.
  destruct Hex as (n & Hn1 & Hn2).
  lets Heu :  n07_arr_len_ex Hn1 Harr Hlen.
  destruct Heu as (vv & Hnth & Hint).
  assert ( Vint32 grp = Vint32 grp) by auto.
  lets Hed : Hrl Hn1 Hnth H.
  destruct Hed as (Hed1 & Hed2).
  destruct Hed2.
  lets Hed22 : H0 Hn2.
  destruct Hrp as (Hrp1 & Hrp2).
  lets Hexx : prio_inq Hn1 Hed22 Hint Hnth.
  destruct Hexx as (prio & Hpro).
  unfolds in Hrp1.
  lets Hxq : Hrp1 Hpro.
  destruct Hxq as (tid' & Hte).
  unfolds; simpl; auto.
  unfolds in Hz.
  destruct Hz. 
  lets Hea : H3 Hte.
  heat.
  apply pure_lib.inlist_ex in H9.
  heat.
  swallow; mytac.
Qed.

Lemma semdel_ecblist_ecbmod_get :
  forall v'53 v'33 v'34 v'36 v'57 i2 x5 x6 x7 v'45 v'38 pegrp,
    Int.unsigned i2 <= 65535 ->
    array_type_vallist_match Int8u v'53 ->
    RH_CurTCB v'36 v'34 ->
    length v'53 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'33 v'34 v'36 ->
    RL_Tbl_Grp_P v'53 (V$0) ->
    ECBList_P (Vptr (v'57, Int.zero)) Vnull 
              (nil ++
                   ((V$OS_EVENT_TYPE_SEM :: V$0 :: Vint32 i2 :: x5 :: x6 :: x7 :: Vint32 pegrp :: nil,
                     v'53) :: nil) ++ v'45) (nil ++ (DSem i2 :: nil) ++ v'38) v'33 v'34 ->
    EcbMod.get v'33 (v'57, Int.zero) = Some (abssem i2, nil) /\
    exists vv, EcbMod.join vv (EcbMod.sig (v'57, Int.zero) (abssem i2, nil)) v'33 /\
               ECBList_P x7 Vnull v'45 v'38 vv v'34.
Proof.
  introv  Hi Harr Hcur Hrl Htcb Hre Hep.
  rewrite app_nil_l in Hep.
  rewrite app_nil_l in Hep.
  unfolds in Hre.
  assert (forall n, (0 <= n < 8)%nat  ->  nth_val n v'53 = Some (Vint32 ($ 0))).
  intros.
  lets Hex : n07_arr_len_ex H  Harr Hrl.
  destruct Hex as (vh & Hnth & Hneq).
  assert (V$0 = V$0) as Hasrt by auto.
  lets Hres : Hre H Hnth Hasrt.
  destruct Hres as (Hrs1 & Hrs2).
  destruct Hrs1 as (Hrs11 & Hrs22).
  rewrite Int.and_zero_l in Hrs11.
  assert (vh = $ 0) .
  apply Hrs11.
  auto.
  subst vh.
  auto.
  simpl in Hep.
  destruct Hep as (qid & Heq & Heb & Hex).
  destruct Hex as (absmq & mqls' & v' & Hv & Hej & Hmt & Hlp). 
  destruct absmq.
  destruct e; tryfalse.
  usimpl Hv.
  inverts Heq.
  destruct Hmt as (Hm1 & Hm2).
  unfolds in Hm2.
  assert (Hf:w = nil \/ w <> nil) by tauto.
  destruct Hf as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  (* destruct Htcb as (_ & Htcb1&Htcb2). *)
  rename Htcb into Htcb1.
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get v'33 (v'57, Int.zero) = Some (abssem i, w) /\ In tid w) by (split; auto).
  destruct Htcb1 as (Htb & Htb2).
  lets Hjj : Htb H0.
  destruct Hjj as (prio & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 & _).
  unfolds in Heb2.
  rename Heb2 into Heba. 
  (* destruct Heb2 as (_ & Heba & Hebb). *)
  lets Hebs : Heba Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H Hnn.
  tryfalse.
  mytac.
  swallow.
  (*lets Heq : int_usign_eq H4 H5. *)
  eapply ecbmod_joinsig_get; eauto.
  eapply ecbmod_joinsig_sig; eauto.
  eauto.
Qed.
 
Lemma semdel_ecb_del_prop_RHhold:
  forall v'35 v'36 v'38 x y absmg,
    (* ~(exists x y pqwaitset, absmg = absmsgq x y pqwaitset /\ pqwaitset <> nil) -> (* new add *) *) 
    RH_TCBList_ECBList_P v'35 v'36 v'38 ->
    EcbMod.join x (EcbMod.sig y (absmg, nil))
      v'35 ->  RH_TCBList_ECBList_P x v'36 v'38 .
Proof.
  introv Hrh Hjo.
  unfolds in Hrh.
  rename Hrh into Hrh2.
  unfolds.

  destruct Hrh2.
  splits.
  intros.
  mytac.
  lets Hg : EcbMod.join_get_get_l Hjo H1.
  eapply H.
  eauto.
  intros.
  assert (eid = y \/ eid <>y) by tauto.
  apply H0 in H1.
  mytac.
  destruct H2.
  subst y.
  apply EcbMod.join_comm in Hjo.
  eapply EcbMod.join_sig_get in Hjo.
  unfold get in H1; simpl in H1.
  rewrite H1 in Hjo.
  inverts Hjo.
  simpl in H3.
  tryfalse.
  do 2 eexists; split; try eapply ecbmod_get_join_get; eauto.
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

Lemma semdel_ecblist_p_decompose :
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


Lemma semdel_ecblist_ecbmod_get' :
  forall v'57 v'40 v'35 v'53 v'33 v'34 v'36 v'47 i2 x5 x6 x7 v'45 v'38 ,
    Some (Vptr (v'57, Int.zero)) = get_last_ptr v'40 ->
    length v'40 = length v'35 ->
    Int.unsigned i2 <= 65535 ->
    array_type_vallist_match Int8u v'53 ->
    RH_CurTCB v'36 v'34 ->
    length v'53 = ∘OS_EVENT_TBL_SIZE ->
    RH_TCBList_ECBList_P v'33 v'34 v'36 ->
    RL_Tbl_Grp_P v'53 (V$0) ->
    ECBList_P v'47 Vnull
              (v'40 ++
                    ((V$OS_EVENT_TYPE_SEM :: V$0 :: Vint32 i2 :: x5 :: x6 :: x7 :: nil,
                      v'53) :: nil) ++ v'45) (v'35 ++ (DSem i2 :: nil) ++ v'38) v'33
              v'34 ->
    EcbMod.get v'33 (v'57, Int.zero) = Some (abssem i2, nil) /\
    exists vg vv vx,
      ECBList_P v'47 (Vptr (v'57, Int.zero)) v'40 v'35 vg v'34 /\
      EcbMod.join vg vx v'33 /\
      EcbMod.join vv (EcbMod.sig (v'57, Int.zero) (abssem i2, nil)) vx /\
      ECBList_P x7 Vnull v'45 v'38 vv v'34.
Proof.
  introv Hsom Hlen Hi Harr Hcur Hrl Htcb Hre Hep.
  lets Hex : semdel_ecblist_p_decompose Hlen Hep.

  mytac_H.
  destruct H2.
  rewrite H2 in Hsom; tryfalse.
  rewrite H2 in Hsom ; inverts Hsom.
  unfolds in Hre.
  assert (forall n, (0 <= n < 8)%nat  ->  nth_val n v'53 = Some (Vint32 ($ 0))).
  intros.
  lets Hex : n07_arr_len_ex H3  Harr Hrl.
  destruct Hex as (vh & Hnth & Hneq).
  assert (V$0 = V$0) as Hasrt by auto.
  lets Hres : Hre H3 Hnth Hasrt.
  destruct Hres as (Hrs1 & Hrs2).
  destruct Hrs1 as (Hrs11 & Hrs22).
  rewrite Int.and_zero_l in Hrs11.
  assert (vh = $ 0) .
  apply Hrs11.
  auto.
  subst vh.
  auto.
  simpl in H0.
  destruct H0 as (qid & Heq & Heb & Hex). (* add Hpb *)
  destruct Hex as (absmq & mqls' & v' & Hv & Hej & Hmt & Hlp).
  destruct absmq.
  destruct e; tryfalse.
  usimpl Hv.
  inverts Heq.
  destruct Hmt as (Hm1 & Hm2).
  unfolds in Hm2.
  mytac_H.
  assert (Hf:w = nil \/ w <> nil) by tauto.
  destruct Hf as [Hnil | Hnnil].
  Focus 2.
  unfolds in Hcur.
  unfolds in Htcb.
  rename Htcb into Htcb1.
  lets Hj : ecbmod_joinsig_get Hej.
  lets Hea : qwaitset_notnil_ex Hnnil.
  destruct Hea as (tid & Hin).
  assert ( EcbMod.get x1 (v'57, Int.zero) = Some (abssem i, w) /\ In tid w) by (split; auto).
  lets Has : EcbMod.join_get_get_r H1 H5.
  assert ( EcbMod.get v'33 (v'57, Int.zero) = Some (abssem i, w) /\ In tid w) by (split; auto).
  destruct Htcb1 as (Htc & Htc').
  lets Hjj : Htc H6.
  destruct Hjj as (prio & Htcg).
  unfolds in Heb.
  destruct Heb as (Heb1 & Heb2 & _).
  unfolds  in Heb1.
  unfolds in Heb2.
  rename Heb2 into Hebb.
  (* destruct Heb2 as (_ & Hebb & Heb2). *)
  lets Hebs : Hebb Htcg.
  lets Hbb : prioinq_exists Hebs.
  destruct Hbb as (n0 & Hnn & Hnth).
  lets Hfs : H3 Hnn.
  tryfalse.
  subst w.
  mytac.
  assert (EcbMod.get x1 (v'57, Int.zero) = Some (abssem i, nil)).
  {
    eapply ecbmod_joinsig_get; eauto.
  }
  swallow.
  eapply EcbMod.join_get_get_r;eauto.
  eauto.
  eauto.
  eapply ecbmod_joinsig_sig.
  unfold sig in Hej; simpl in Hej.
  eauto.
  eauto.
Qed.


Lemma semdel_ecbjoin_sig_join:
  forall x x1 v'35 x0 v'61 i2,
    EcbMod.join x x1 v'35 ->
    EcbMod.join x0 (EcbMod.sig (v'61, Int.zero) (abssem i2, nil)) x1 ->
    exists y,
      EcbMod.join x0 x y /\
        EcbMod.join y (EcbMod.sig (v'61, Int.zero) (abssem i2, nil)) v'35.
Proof.
  intros.
  set ( EcbMod.join_assoc_r H0 H).
  mytac.
  exists x2.
  split; auto.
  apply EcbMod.join_comm in H1.
  auto.
Qed.

Lemma upd_last_prop:
  forall v g x vl z,
    V_OSEventListPtr v = Some x ->
    vl = upd_last_ectrls ((v, g) :: nil) z ->
    exists v', vl = ((v', g) ::nil) /\ V_OSEventListPtr v' = Some z.
Proof.
  intros.
  unfolds in H.
  destruct v;simpl in H; tryfalse.
  destruct v0; simpl in H; tryfalse.
  destruct v1; simpl in H; tryfalse.
  destruct v2; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse.
  destruct v4; simpl in H; tryfalse.
  inverts H.
  unfold upd_last_ectrls in H0.
  simpl in H0.
  eexists; splits; eauto.
Qed.

Lemma nth_val_upd_prop:
  forall vl n m v x,
    (n<>m)%nat ->
    (nth_val n (ifun_spec.update_nth val m vl v) = Some x  <->
     nth_val n vl  = Some x).
Proof.
  inductions vl.
  intros.
  simpl.
  split;
    intros; tryfalse.
  intros.
  simpl.
  destruct n.
  destruct m.
  tryfalse.
  simpl.
  intros; split; auto.
  destruct m.
  simpl.
  split; auto.
  assert (n <> m) by lia.
  simpl.
  eapply IHvl.
  eauto.
Qed.

Lemma R_ECB_upd_hold :
  forall x1 v v0 v'36 x8,
    R_ECB_ETbl_P x1 (v, v0) v'36 ->
    R_ECB_ETbl_P x1 (ifun_spec.update_nth val 5 v x8, v0) v'36.
Proof.
  introv Hr.
  unfolds in Hr.
  destruct Hr.
  unfolds.
  splits. 
  unfolds in H.
  rename H into Hr2. 
  (* destruct H as (Hr1 & Hr2 & Hr3 & Hr4). *)
  
  unfolds in Hr2.
  unfolds.
  unfolds. 
  intros.
  eapply Hr2; eauto.
  assert (0<>5)%nat by lia.
  eapply nth_val_upd_prop; eauto.
  
  destruct H0 as (H0 & _).
  unfolds in H0.
  rename H0 into Hr2.  
  unfolds.
  unfolds.
  intros.
  apply Hr2 in H0.
  destruct H0.
  split; eauto.
  assert (0<>5)%nat by lia.
  eapply nth_val_upd_prop; eauto.

  destruct H0.
  unfolds in H1.
  unfolds.
  simpl in *.
  unfold V_OSEventType in *.
  eapply nth_val_upd_prop; eauto.
Qed.

Lemma semdel_ecb_list_join_join :
  forall v'40  v'52 v'61 v'21 x x2  v'36 x8 v'42 v'37 x0 v'51,
     v'40 <> nil ->
     ECBList_P v'52 (Vptr (v'61, Int.zero)) v'40 v'21 x v'36 ->
     ECBList_P x8 Vnull v'42 v'37 x0 v'36 ->
     v'51 = upd_last_ectrls v'40 x8 -> 
     EcbMod.join x0 x x2 -> 
     ECBList_P v'52 Vnull (v'51 ++ v'42) (v'21 ++ v'37) x2 v'36.
Proof.
  inductions v'40.
  - 
    simpl.
    intros.
    mytac.
    unfold upd_last_ectrls in H.
    simpl in H.
    tryfalse.
  -    
    introv Hneq Hep Hepp Hsom Hj.
    assert (v'40 = nil \/ v'40 <> nil) by tauto.
    destruct H.
    subst v'40.
    destruct v'21.
    simpl in Hep.
    mytac; tryfalse.
    simpl in Hep.
    mytac.
    destruct a.
    mytac.
    remember (upd_last_ectrls ((v, v0) :: nil) x8) as vl.
    lets Hx : upd_last_prop  H Heqvl.
    mytac.
    unfolds in H3.
    simpl in H3.
    inverts H3.
    unfolds upd_last_ectrls.
    simpl.
    eexists; splits; eauto.
    eapply R_ECB_upd_hold; eauto.
    do 2 eexists.
    exists x8.
    split; auto.
    split.
    eapply ecbmod_join_sigg; eauto.
    split; eauto.
    destruct a.
    lets Hzz :  upd_last_prop' Hsom;auto.
    destruct Hzz as (vll & Hv1 & Hv2).
    rewrite Hv1.
    destruct v'21.
    simpl in Hep; mytac; tryfalse.
    simpl.
    simpl in Hep.
    destruct Hep as (qid & Heq & Hr & Hex). (* add Hpeb *)
    destruct Hex as (abs & mqls & vv & Heaq & Hjoin & Hrl & Hepc ).
    lets Hxz : joinsig_join_sig2 Hjoin Hj.
    destruct Hxz as (x6 & Hj1 & Hj2).
    subst v'52.
    eexists.
    split; eauto.
    splits; auto.
    do 2 eexists.
    exists vv.
    splits; eauto.
Qed.
