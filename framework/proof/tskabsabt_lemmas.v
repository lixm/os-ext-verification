
Require Import include_frm.
Require Import auxdef.
Require Import simulation.
Require Import base_tac.
Require Import step_prop.
Require Import join_prop.

(* Lemma hmstepstar_htsteps:  *)
(*   forall pc A spc sd aop O aop' O' ke ks cst t,  *)
(*     hmstepstar sd aop O aop' O' -> *)
(*     A = (spc, sd) ->  *)
(*       htsteps (pc, A) t *)
(*         (curs (hapi_code aop), (ke, ks)) cst O *)
(*         (curs (hapi_code aop'), (ke, ks)) cst O'.   *)
(* Proof. *)
(*   induction 1. *)
(*   - constructors.  *)
(*   - introv HA. *)
(*     lets IHH: IHspec_stepstar HA. clear IHspec_stepstar. *)
(*     constructors; eauto. *)
(*     eapply hapi_step; eauto. *)
(*     constructors; auto. *)
(*     rewrite HA. simpl. *)
(*     auto. *)
(* Qed. *)

Lemma hmsps_htsps:
  forall A pc aop aop' OO OO' ke ks cst t,
    hmstepstar (snd A) aop OO aop' OO' ->
    htstepstar (pc, A) t
      (curs (hapi_code aop), (ke, ks)) cst OO
      (curs (hapi_code aop'), (ke, ks)) cst OO'.
Proof.
  introv Hsps.
  remember (snd A) as SC. 
  induction Hsps.
  - 
    constructors.
  -
    subst. 
    constructors.
    {
      introv Hf.
      simpl in Hf.
      destruct A.
      destruct p.
      simpljoin; tryfalse.
    }
    { eapply hapi_step; eauto. constructors; eauto. }
    eapply IHHsps; eauto.
Qed.     

Lemma absabt_tskabsabt:
  forall A pc aop OO ke ks cst t, 
    (exists OO', hmstepstar (snd A) aop OO (ABORT) OO') -> 
    tskabsabt (pc, A) (curs (hapi_code aop), (ke, ks)) cst OO t. 
Proof.
  introv Hsps.
  destruct Hsps as (OO' & Hsps).
  unfolds.
  left.
  do 4 eexists.
  eapply hmsps_htsps; eauto. 
Qed. 

(* Lemma htsteps_hpsteps:  *)
(*   forall Th Ch t hp Ch' cst cst' O O',  *)
(*     htsteps hp t Ch cst O Ch' cst' O' -> *)
(*     get O curtid = Some (oscurt t) -> *)
(*     get Th t = Some Ch -> *)
(*     hpsteps hp Th cst O (set Th t Ch') cst' O'.  *)
(* Proof. *)
(*   introv Hsps. *)
(*   generalize dependent Th. *)
(*   induction Hsps; intros. *)
(*   - asserts_rewrite (set Th t c = Th). *)
(*     apply get_set_same; auto. *)
(*     constructors.  *)
(*   - lets IHH0: IHHsps (set Th t c''). *)
(*     assert (H': get (set Th t c'') t = Some c'') by apply get_set_eq. *)
(*     lets Htideq: htstep_tidsame H. *)
(*     assert (HtidO'': get O'' curtid = Some (oscurt t)). *)
(*     { unfold tidsame in Htideq. rewrite <- Htideq. auto. } *)
(*     lets IHH: IHH0 HtidO'' H'; auto. *)
(*     clear IHH0. *)
(*     rewrite <- set_set_eq in IHH. *)
(*     eapply hpsteps_S; eauto. *)
(*     eapply hp_step; eauto. *)
(*   - lets IHH0: IHHsps (set Th t c''). *)
(*     assert (H': get (set Th t c'') t = Some c'') by apply get_set_eq. *)
(*     assert (HeqO: O = O'') by (inverts H; auto). *)
(*     lets IHH: IHH0 H'; auto. clear IHH0. *)
(*     subst O''; auto. *)
(*     rewrite <- set_set_eq in IHH. *)
(*     subst O''. *)
(*     eapply hpsteps_S_ev; eauto. *)
(*     assert (Heqcst: cst = cst'') by (inverts H; auto). *)
(*     subst cst''. *)
(*     eapply hpt_stepev; eauto. *)
(* Qed. *)
     
       
Lemma htstepstar_hpstepstar:
  forall hp t C cst O C' cst' O' T, 
    htstepstar hp t C cst O C' cst' O' ->
    get O curtid = Some (oscurt t) -> 
    get T t = Some C -> 
    hpstepstar hp T cst O (set T t C') cst' O'.
Proof.
  introv Hsr.
  generalize T.
  induction Hsr.
  - 
    intros.
    rewrite get_set_same; eauto. 
    constructors. 
  -
    introv Hgt Hgc.
    assert (get O' curtid = Some (oscurt t)).
    {
      inverts H0; eauto. 
      lets H__: hapistep_tidsame H2; eauto. 
      unfolds in H__; congruence.
    }
    eapply hp_stepS; eauto.
    constructors; eauto.
    specialize (IHHsr (set T0 t c')).
    specializes IHHsr; eauto.
    rewrite set_a_get_a; auto.
    rewrite <- set_set_eq in IHHsr.
    auto.
Qed.  

Lemma htstepevstar_hpstepevstar:
  forall hp t C cst O C' cst' O' T v,
    htstepevstar hp t C cst O C' cst' O' v ->
    get O curtid = Some (oscurt t) ->
    get T t = Some C ->
    hpstepevstar hp T cst O (set T t C') cst' O' v.
Proof.
  introv Hsr.
  generalize T.
  induction Hsr.
  {
    intros.
    eapply hp_stepev with (T':=set T0 t c') (T'':=set T0 t c'') (O':=O'); eauto.
    eapply htstepstar_hpstepstar; eauto.
    lets Hts: htstepstar_tidsame H; eauto.    
    constructors; eauto.
    unfolds in Hts; congruence.
    rewrite set_a_get_a; eauto.
    rewrite <- set_set_eq; eauto.
    lets H__: htstepstar_hpstepstar (set T0 t c'') H1; eauto.
    specializes H__; eauto. 
    lets Hts: htstepstar_tidsame H; eauto.
    unfolds in Hts; congruence.
    rewrite set_a_get_a; eauto.
    rewrite <- set_set_eq in H__.
    auto.
  }
Qed.     

Lemma tskabsabt_prgabsabt:
  forall Th hp t Ch cst O,
    get Th t = Some Ch ->
    get O curtid = Some (oscurt t) ->
    tskabsabt hp Ch cst O t ->
    prgabsabt hp Th cst O.
Proof.
  introv HTht HOctid Htskabt.
  unfold tskabsabt in Htskabt.
  unfold prgabsabt.
  destruct Htskabt as [Hnev | Hev].
  -
    left.
    simpljoin.
    lets H__: htstepstar_hpstepstar H; eauto.
    specializes H__; eauto.
    do 3 eexists; split; eauto.
    unfolds.
    exists t x x0.
    rewrite set_a_get_a.
    auto.
  -
    right.
    simpljoin. 
    lets H__: htstepevstar_hpstepevstar H; eauto.
    specializes H__; eauto.
    do 4 eexists; split; eauto.
    unfolds.
    exists t x x0.
    rewrite set_a_get_a.
    auto. 
Qed. 

(* Lemma htsteps_local:  *)
(*   forall (p : hprog) t *)
(*          (C : code) (cst : clientst) (O : osabst) (C' : code) (cst' : clientst) *)
(*          (O' OO Of : osabst), *)
(*     htsteps p t C cst O C' cst' O' -> *)
(*     join O Of OO -> *)
(*     exists OO', htsteps p t C cst OO C' cst' OO' /\ join O' Of OO'.  *)
(* Proof. *)
(*   introv Hsps. generalize OO. *)
(*   induction Hsps. *)
(*   - introv Hjo. exists OO0. *)
(*     split; auto. constructors; auto. *)
(*   - intros. *)
(*     lets H'': htstep_O_local H H0. *)
(*     destruct H'' as (OO' & Hsps' & Hjo'). *)
(*     apply IHHsps in Hjo'. *)
(*     destruct Hjo' as (OO'0 & Hsps'' & Hjo''). *)
(*     exists OO'0. *)
(*     split; auto. *)
(*     eapply htsteps_S; eauto. *)
(*   - assert (O'' = O) by (inverts H; auto). *)
(*     subst O''. *)
(*     introv Hjo. *)
(*     lets Hsp': IHHsps Hjo. *)
(*     assert (Hspev: htstepev p t c cst OO0 c'' cst'' OO0 ev). *)
(*     { inverts keep H. constructors; eauto. } *)
(*     destruct Hsp' as (OO' & Hsp'' & Hjo''). *)
(*     exists OO'. split; auto. *)
(*     eapply htsteps_S_ev; eauto. *)
(* Qed.       *)
