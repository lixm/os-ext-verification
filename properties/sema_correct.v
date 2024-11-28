
Require Import memory.
Require Import anno_language.
Require Import common_defs.
Require Import sem_sys.
Require Import good_code.

Require Import sema_invs.
Require Import proof_method.

Require Import semwait_preserves_inv.
Require Import semsignal_preserves_inv.
Require Import timetick_preserves_inv. 

Require Import aux_tacs.
Require Import init.
Require Import asrt_sat.

Lemma sema_init_sat_dtinv:
  init_sat_dtinv init_st_sema dtinv. 
Proof.
  unfolds.
  introv Hit Hist.
  unfolds.
  destruct Hist as (Hits & Hiss & Higmp & Hilmp).
  unfolds in Hits.
  unfolds in Hiss.
  unfolds in Higmp.
  simpljoin.
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto. 
  splits.
  - (* atids_valid *)
    auto.
  - (* cond_pv1 *)
    unfolds.
    introv Hf.
    rewrite H4 in Hf.
    false.
  - (* cond_pv0 *)
    unfolds.
    introv Hf.
    rewrite H4 in Hf.
    false.
  - (* wait_progpt *)
    unfolds.
    introv Hf.
    rewrite H4 in Hf.
    false.
  - (* none_progpt *)
    unfold none_progpt.
    introv Hnex.
    introv Hf.
    unfolds in Hilmp.
    unfolds in Hit.
    destruct Hit as (Heqd & _).
    unfolds in Heqd.
    destruct Heqd as (tls & Hgtls & Haiff).
    l_rew21 (get O abstcblsid).
    match goal with
      H: context [atids_valid] |- _ =>
        destruct H as (_ & Hiff)
    end.
    eapply Hiff in Hf; eauto.
    assert (Hex: exists a, get tls t = Some a).
    {
      destruct (get tls t) eqn: E.
      eexists. eauto.
      false.
    }
    eapply Haiff in Hex; eauto.
    assert (Hnn: get T t <> None).
    {
      introv Hff. destruct Hex as (C& Hg).
      rewrite Hg in Hff. inverts Hff.
    }
    eapply Hilmp in Hnn; eauto.
    introv Hgso.
    rewrite Hnn in Hgso.
    inverts Hgso.  
Qed.   
  
Lemma dtinv_set_curt_preserved: 
  forall O aust t, 
    dtinv O aust ->
    dtinv (set O curtid (oscurt t)) aust. 
Proof.
  introv Hdt.
  unfold dtinv in *.
  simpljoin.
  do 4 eexists; splits; eauto; 
  rewrite join_lib.set_a_get_a'; eauto; 
  introv Hf; inverts Hf.
Qed.       

Theorem sema_correct :
  forall pu,
    good_client_code pu -> 
    rc_dtinv pu (api_spec, int_spec, GetHPrio) init_st_sema dtinv.
Proof.
  intros.
  eapply proof_method with (li := fun lau => (tskpt lau) = PtNormal).
  eapply sema_init_sat_dtinv; eauto.
  {
    unfolds.
    introv Hgetf Hsuc Hsat Hsp Hgt Hgl Hsl Hdti.
    unfold api_spec in Hgetf.
    simpl in Hgetf.
    destruct (Zeq_bool service_sema_P f) eqn: E1.
    {
      apply Zeq_bool_eq in E1; subst.
      inverts Hgetf.
      eapply sem_wait_preserves_inv; eauto.
    }
    {
      destruct (Zeq_bool service_sema_V f) eqn: E2.
      {
        apply Zeq_bool_eq in E2; subst.
        inverts Hgetf.
        eapply sem_signal_preserves_inv; eauto.
      }
      false.
    }
  }
  {
    unfolds.
    introv Hgeth Hsuc Hsp Hgt Hgl Hsl Hdti.
    unfolds in Hgeth.
    simpl in Hgeth.
    destruct h. inverts Hgeth. 
    eapply timetick_preserves_inv; eauto.
    false. 
  }
  {
    unfolds.
    intros.
    eapply dtinv_set_curt_preserved; eauto.
  }
  {
    unfolds.
    introv Hrc.
    eapply reachable_hasrt_sat; eauto.
  }

Qed. 
