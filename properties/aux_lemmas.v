
Require Import base_tac. 
Require Import memory. 
Require Import anno_language.
Require Import aux_notations.

Require Import common_defs. 
Require Import succ_gen.

Require Import aux_tacs. 

Lemma abt_succs_contra: 
  forall cd,
    has_succ spec_abort cd ->
    cd = ABORT.
Proof.
  introv Hhs.
  inverts Hhs; auto.
  inverts H.
Qed. 

Lemma join_get_same_l:
  forall (O0 O0' O O' Of: osabst) x, 
    get O0 x = get O0' x ->
    join O0 Of O ->
    join O0' Of O' ->
    get O x = get O' x.
Proof.
  introv Hg Hjo Hjo'.
  assert ((exists z, get O0 x = Some z) \/ get O0 x = None).
  {
    destruct (get O0 x) eqn: E.
    left. eexists; eauto. right; auto.
  }
  destruct H.
  -
    simpljoin.
    rewrite H in Hg.
    assert (Hg': get O' x = Some x0).
    {
      symmetry in Hg.
      eapply join_get_get_l; eauto. 
    }
    rewrite Hg'.
    eapply join_get_get_l; eauto.
  -
    assert (get O x = get Of x).
    {
      eapply map_join_get_none; eauto. 
    }
    assert (get O' x = get Of x).
    {
      rewrite H in Hg; symmetry in Hg.
      eapply map_join_get_none; eauto. 
    }
    congruence. 
Qed.

Lemma beq_tid_true : forall t, beq_tid t t = true.
Proof.
  intros.
  unfolds; destruct t.
  rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_refl.
  rewrite Int.eq_true.
  simpl; auto.
Qed.

Lemma beq_tid_true_eq: forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H; destruct t1; destruct t2.
  apply andb_true_iff in H; destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Pos.eqb_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.


Lemma in_remove_tid_false : forall wl t, In t (remove_tid t wl) -> False.
Proof.
  intro; inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  eapply IHwl; eauto.
  simpl in H.
  destruct H.
  substs.
  rewrite beq_tid_true in eq1; tryfalse.
  eapply IHwl; eauto.
Qed.

Lemma in_remove_tid : forall wl t ct, In ct (remove_tid t wl) -> In ct wl.
Proof.
  inductions wl; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  simpl.
  right; eapply IHwl; eauto.
  simpl in H; destruct H; substs.
  simpl; left; auto.
  simpl; right; eapply IHwl; eauto.
Qed.


Lemma distinct_sub2:
  forall t a ws, 
    distinct (t::a::ws) ->
    distinct (t::ws).
Proof.
  introv Hds.
  unfold distinct in *.
  introv Hn1 Hn2 Hneq.
  casetac i 0%nat Ht Hf.
  -
    subst.  simpl in Hn1. inverts Hn1.
    specialize (Hds 0%nat (S j) t1 t2).
    simpl in Hds.
    eapply Hds; eauto.
    destruct j.
    false.
    simpl.
    simpl in Hn2.
    auto.
  -
    destruct i.
    false.
    simpl in Hn1.
    casetac j 0%nat Htt Hff.
    +
      subst.
      simpl in Hn2.
      inverts Hn2.
      specialize (Hds (S (S i)) 0%nat t1 t2).
      simpl in Hds.
      eapply Hds; eauto.
    +
      destruct j.
      false.
      simpl in Hn2.
      specialize (Hds (S (S i)) (S (S j)) t1 t2).
      simpl in Hds.
      eapply Hds; eauto. 
Qed.                 


Lemma distinct_in_contr:
  forall ws t, 
    distinct (t :: ws) -> In t ws -> False.
Proof. 
  induction ws.
  intros. simpl in H0. false.
  introv Hds Hin.
  simpl in Hin.
  destruct Hin.
  subst.
  unfolds in Hds.
  specialize (Hds 0%nat 1%nat t t).
  simpl in Hds.
  eapply Hds; eauto.
  assert (distinct (t :: ws)).
  { eapply distinct_sub2; eauto. } 
  eapply IHws; eauto.
Qed. 

Lemma distinct_sub1:
  forall a ws, 
    distinct (a::ws) -> 
    distinct ws. 
Proof.
  introv Hds.
  unfold distinct in *.
  introv Hnth1 Hnth2 Hneq.
  specialize (Hds (S i) (S j) t1 t2).
  eapply Hds; eauto. 
Qed. 


Lemma atids_valid_set_tcb_preserve: 
  forall tls t tcb tcb' ts, 
    get tls t = Some tcb ->
    atids_valid tls ts ->
    atids_valid (set tls t tcb') ts. 
Proof.
  introv Hg Htv.
  unfold atids_valid in *.
  destruct Htv as (Hdt & Htv).
  split; auto. 
  intros.
  specialize (Htv t0).
  destruct Htv as (H12 & H21).
  split.
  - casetac t t0 Ht Hf.
    + subst. rewrite set_a_get_a. 
      rewrite Hg in H12.
      introv _.
      eapply H12; eauto.
      introv Hn. inverts Hn.
    + rewrite set_a_get_a'; eauto.
  - introv Hin.
    lets H__: H21 Hin.
    casetac t t0 Ht Hf.
    + subst. rewrite set_a_get_a.
      introv Hn; inverts Hn.
    + rewrite set_a_get_a'; eauto.
Qed.             

Require Import seplog_lemmas. 

Lemma atids_valid_decomp:
  forall tls t ts, 
    atids_valid tls (t :: ts) ->
    (exists p st,
        get tls t = Some (p, st)
        /\ exists tls', join (sig t (p, st)) tls' tls /\ atids_valid tls' ts). 
Proof.
  introv Hav.
  unfolds in Hav.
  destruct Hav as (Hds & Hav).
  assert (Hav_:=Hav).
  specialize (Hav t).
  destruct Hav as (Hgtls & Hin).
  specializes Hin; eauto.
  { simpl. left; auto. }
  destruct (get tls t) eqn: E.
  - destruct p. 
    do 2 eexists.
    split; eauto.
    clear Hin.
    assert (Hex: exists tls', join (sig t (p, t0)) tls' tls).
    {
      eapply map_tactics.get_join; eauto. 
    }
    destruct Hex as (tls' & Hjo).
    assert (atids_valid tls' ts).
    {
      unfolds.
      split.
      eapply distinct_sub1; eauto. 
      intro t_.
      split.
      - introv Hg'.
        (* map_join_get_no_perm1 *)
        (* map_join_get_some *) 
        assert (get (sig t (p, t0)) t = Some (p, t0)).
        {
          join auto.
        }
        assert (exists p st, get tls' t_ = Some (p, st)).
        {
          destruct (get tls' t_) eqn: E'.
          + destruct p0.
            do 4 eexists; eauto. 
          + false. 
        }
        simpljoin.
        assert (t <> t_).
        {
          eapply join_get_get_neq with (ma:=(sig t (p, t0))) (mb:=tls'); eauto. 
        }
        specialize (Hav_ t_).
        destruct Hav_ as (Hin_ & _). 
        specializes Hin_; eauto. 
        {
          match goal with
            H: get tls' t_ = Some ?e |- _ => assert (Hgsome: get tls t_ = Some e)
          end.
          { eapply join_get_r; eauto. }
          rewrite Hgsome.
          introv Hf; inverts Hf.
        }
        simpl in Hin_.
        destruct Hin_.
        tauto.
        auto.
      -
        introv Hin_.                      
        specialize (Hav_ t_).
        destruct Hav_ as (_ & Hg).
        specializes Hg; eauto. 
        { simpl. right; auto. }
        lets H__:  distinct_in_contr Hds; eauto.
        assert (Hneq: t <> t_).
        {
          introv Hf. subst. apply H__ in Hin_. false. 
        }
        introv Hgn.
        apply Hg.
        eapply map_join_get_none''' with (m1:=sig t (p, t0)) (m2:=tls'); eauto.
        join auto.
    }
    eexists.
    split; eauto. 
  -
    false. 
Qed.


Lemma val_destruct: 
  forall (vp: val), 
    (exists eid, vp = Vptr eid) \/ (forall eid, vp <> Vptr eid).
Proof.
  intros.
  destruct vp.
  right. intros. introv Hf. false.
  right. intros. introv Hf. false.
  right. intros. introv Hf. false.
  left. eexists; eauto. 
Qed. 

Lemma val_not_ptr_match: 
  forall vp eid,
    (forall eid, vp <> Vptr eid) -> 
    match vp with
    | Vptr eid' => beq_tid eid eid'
    | _ => false
    end = false. 
Proof.
  introv Ha.
  destruct vp; auto. 
  specialize (Ha a).
  false. 
Qed. 

