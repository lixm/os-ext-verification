
Require Import memory.
Require Import anno_language. 
Require Import anno_opsem.  
Require Import aux_notations.
Require Import join_lib.
Require Import aux_tacs.

Require Import succ_gen. 

Definition ks_noint_apicode_c (aspc: fid -> option osapi) c ks :=
  forall cd, 
    c = curs (hapi_code cd) -> 
    absintcont ks = None ->
    ((exists fid acode ft vl,
         aspc fid = Some (acode, ft) /\ has_succ (acode vl) cd) 
     \/ cd = ABORT \/ (exists vo, cd = END vo)).

Fixpoint ks_noint_apicode_cont (aspc: fid -> option osapi) (ks: stmtcont) := 
  match ks with
    kseq _ ks
  | kcall _ _ _ ks
  | kint _ _ _ ks
  | kassignr _ _ ks
  | kassignl _ _ ks
  | kfuneval _ _ _ _ ks
  | kif _ _ ks
  | kwhile _ _ ks
  | kret ks
    => ks_noint_apicode_cont aspc ks
  | kevent c ke ks =>
      ks_noint_apicode_cont aspc ks /\ 
        (absintcont ks = None ->
         forall cd,         
           c = curs (hapi_code cd) ->
           ((exists fid acode ft vl,
                aspc fid = Some (acode, ft) /\  (has_succ (acode vl) cd)) 
            \/ cd = ABORT \/ (exists vo, cd = END vo)))
  | kstop => True
  end.

Definition ks_noint_apicode (aspc: fid -> option osapi) (C: code) :=
  match C with
    (c, (ke, ks)) => 
      ks_noint_apicode_c aspc c ks /\
        ks_noint_apicode_cont aspc ks
  end.

Definition pool_ks_no_int_apicode (aspc: fid -> option osapi) (T: tasks) :=
  forall t C,
    get T t = Some C ->
    ks_noint_apicode aspc C.

Lemma ks_noint_apicode_estep_preserve:
  forall c ke m c' ke' m' ks aspc, 
    estep c ke m c' ke' m' ->
    ks_noint_apicode aspc (c, (ke, ks)) ->
    ks_noint_apicode aspc (c', (ke', ks)).
Proof.   
  introv Hes Hkna.
  unfolds in Hkna.
  simpljoin.
  inverts Hes; 
  try (unfolds; split; [unfolds; introv Heq; inverts Heq | auto]). 
Qed.

Lemma callcont_noint_apicode: 
  forall ks f s le' ks' aspc, 
    ks_noint_apicode_cont aspc ks ->
    callcont ks = Some (kcall f s le' ks') ->
    ks_noint_apicode_cont aspc ks'. 
Proof.
  inductions ks; 
  introv Hkna Hk; 
    try (simpl in Hk; inverts Hk);
    try (eapply IHks; eauto; fail).
  - 
    simpl in Hkna; auto.
  -
    eapply IHks; eauto.
    simpl in Hkna. simpljoin. 
    auto.
Qed.

Require Import rc_no_subabs.

Lemma ks_noint_apicode_sstep_preserve:
  forall pu c ks m c' ks' m' ke aspc, 
    sstep pu c ks m c' ks' m' ->
    ks_noint_apicode aspc (c, (ke, ks)) ->
    tskcode_no_sub_abs (c, (ke, ks)) -> 
    ks_noint_apicode aspc (c', (ke, ks')).
Proof.
  introv Hss Hkna Htcna.
  unfolds.
  inverts Hss;
    try 
      (split; 
       [ unfolds; introv Heq Hnone; inverts Heq | 
         simpl; 
         simpl in Hkna; simpljoin; 
         auto]; fail).
  -
    split.
    +
      unfolds.
      introv Heq Hnone.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl. simpl in Hkna. simpljoin. auto.
  -
    split.
    +
      unfolds.
      introv Heq Hnone.
      inverts Heq.
    +
      unfolds in Hkna.
      destruct Hkna as (_ & Hk).
      eapply callcont_noint_apicode; eauto. 
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      destruct Htcna as (Hf & _).
      simpl in Hf.
      destruct Hf; simpljoin; tryfalse.
    +
      simpl.
      simpl in Hkna.
      simpljoin.
      auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna.
      simpljoin.
      auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna. simpljoin. auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna. simpljoin. auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna.
      simpljoin.
      auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      simpl in Htcna.
      simpljoin; tryfalse.
    +
      simpl.
      simpl in Hkna.
      simpljoin; auto.
 Qed.

Lemma ks_noint_apicode_cstep_preserve:
  forall pu C m C' m' aspc, 
    cstep pu C m C' m' ->
    ks_noint_apicode aspc C ->
    tskcode_no_sub_abs C -> 
    ks_noint_apicode aspc C'.
Proof.
  introv Hsp Hkna Hna.
  inverts Hsp.
  eapply ks_noint_apicode_estep_preserve; eauto.
  eapply ks_noint_apicode_sstep_preserve; eauto. 
Qed.   

Require Import good_code.
Require Import init. 
Require Import common_defs. 

Lemma ks_noint_apicode_spec_step_preserve:
  forall sc cd O cd' O' ke ks lau lau' aspc, 
    spec_step sc cd O lau cd' O' lau' ->
    ks_noint_apicode aspc (curs (hapi_code cd), (ke, ks)) ->
    ks_noint_apicode aspc (curs (hapi_code cd'), (ke, ks)).
Proof.
  introv Hsps Hkna.
  unfold ks_noint_apicode in *.
  simpljoin. split; auto.
  introv Heq.
  inverts Heq.
  introv Hnone.
  specializes H; eauto.
  destruct H as [Hac | [Habt | Hend]].
  -
    simpljoin.
    lets H__: succ_step_preserve Hsps; eauto. 
    destruct H__ as [Ha | [Habt | Hend]].
    + left. do 4 eexists. split; eauto.
    + right. left. auto.
    + right; right. auto.
  -
    subst.
    inverts Hsps.
  -
    simpljoin. inverts Hsps.
Qed.

Lemma ks_noint_apicode_apistep_preserve:
  forall sc C O C' O' lau lau' aspc ispc, 
    hapistep (aspc, ispc, sc) C O lau C' O' lau' ->
    ks_noint_apicode aspc C ->
    ks_noint_apicode aspc C'. 
Proof.
  introv Has Hkna.
  inverts Has.
  - 
    unfolds.
    unfolds in Hkna.
    simpljoin. split; auto.
    introv Heq Hnone.
    inverts Heq.
    left.
    do 3 eexists. exists (vl++vl').
    split; eauto. 
    constructors; auto.
  -
    eapply ks_noint_apicode_spec_step_preserve; eauto.
  -
    unfolds.
    unfolds in Hkna.
    simpljoin. split; auto.
    introv Heq Hnone.
    inverts Heq.
  -
    unfolds in Hkna.
    unfolds.
    destruct Hkna as (Hc & Hk).
    split.
    + 
      simpl in Hk.
      destruct Hk as (_ & H').      
      introv Hce Hke.
      subst.
      specializes H'; eauto.
    +
      simpl in Hk.
      simpljoin.
      auto.
Qed. 

Lemma ks_noint_apicode_htstep_preserve:
  forall sc C O C' O' cst cst' pu t aspc ispc lau lau', 
    htstep (pu, (aspc, ispc, sc)) t C cst O lau C' cst' O' lau' -> 
    tskcode_no_sub_abs C -> 
    ks_noint_apicode aspc C ->
    ks_noint_apicode aspc C'. 
Proof.
  introv Hsp Hna Hkna.
  inverts Hsp; 
    try match goal with H: (_, _) = _ |- _ => inverts H end.
  -
    eapply ks_noint_apicode_cstep_preserve; eauto.
  -
    eapply ks_noint_apicode_apistep_preserve; eauto.  
Qed.

(* Lemma get_hprio_d_preserve:  *)
(*   forall O O' t,  *)
(*     get O abstcblsid = get O' abstcblsid -> *)
(*     get O kscurdomid = get O' kscurdomid ->  *)
(*     get_hprio_d O t -> *)
(*     get_hprio_d O' t. *)
(* Proof. *)
(*   introv Hgteq Hgdeq Hp. *)
(*   unfold get_hprio_d in *. *)
(*   simpljoin. *)
(*   rewrite <- Hgteq. *)
(*   rewrite <- Hgdeq. *)
(*   do 6 eexists. *)
(*   split; eauto. *)
(* Qed. *)

Lemma pool_ks_noint_apicode_hpstep_preserve:
  forall T O T' O' cst cst' pu sc aspc ispc lau lau',
    hpstep (pu, (aspc, ispc, sc)) T cst O lau T' cst' O' lau' -> 
    task_pool_no_sub_abs T -> 
    pool_ks_no_int_apicode aspc T ->
    pool_ks_no_int_apicode aspc T'.
Proof.
  introv Hsp Hna Hpkna.
  unfold pool_ks_no_int_apicode in *.
  introv Hgt.
  inverts Hsp.
  -
    casetac t0 t Ht Hf.
    +
      subst. rewrite set_a_get_a in Hgt. inverts Hgt.
      specializes Hpkna; eauto.
      specializes Hna; eauto.
      eapply ks_noint_apicode_htstep_preserve; eauto.
    +
      rewrite set_a_get_a' in Hgt; eauto.
  -
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with
      H: context [htistep] |- _ => inverts H
    end.
    casetac t0 t Ht Hf.
    + subst. rewrite set_a_get_a in Hgt. inverts Hgt.
      unfolds.
      split.
      *
        unfolds. introv Heq Hk. simpl in Hk. inverts Hk.
      * 
        specializes Hpkna; eauto.
        simpl.
        unfolds in Hpkna.
        simpljoin.
        split; auto.
    +
      rewrite set_a_get_a' in Hgt; eauto.
  -
    match goal with H: (_, _) = _ |- _ => inverts H end.
    casetac t0 t Ht Hf.
    + subst. rewrite set_a_get_a in Hgt. inverts Hgt.
      specializes Hpkna; eauto.
      simpl. simpl in Hpkna.
      simpljoin. split; auto.
      unfolds.
      unfolds in H.
      introv Heq Hnone.
      specializes H; eauto.
      destruct H as [Hff | [Hff | Hff]]; simpljoin; tryfalse.
      inverts Heq.
      left. do 4 eexists; splits; eauto.
      instantiate (1:=x2).
      unfold has_succ in *.
      destruct H4.
      {
        right. rewrite <- H4. constructors. 
      }
      {
        right. eapply succ_seq_cd2; eauto. 
      }
    +
      rewrite set_a_get_a' in Hgt; eauto.
Qed.

Lemma pool_ks_noint_apicode_hpstepokstar_preserve: 
  forall pu T cst O T' cst' O' aspc ispc sc lau lau',    
    pu_noabs pu -> 
    hpstepokstar (pu, (aspc, ispc, sc)) T cst O lau T' cst' O' lau' ->
    task_pool_no_sub_abs T -> 
    pool_ks_no_int_apicode aspc T ->
    pool_ks_no_int_apicode aspc T'.
Proof. 
  introv Hpn Hstepstar.
  remember (pu, (aspc, ispc, sc)) as hp0.
  induction Hstepstar.
  intros; auto.
  introv Hpna Hni.
  subst. 
  inverts H. 
  lets H_: pool_ks_noint_apicode_hpstep_preserve H0; eauto.
  eapply IHHstepstar; eauto.
  eapply noabs_preserve_hpstep; eauto.  
Qed.

Lemma reachable_ks_noint_apicode: 
  forall pu sc aspc ispc T cst O laump ini_st, 
    pu_noabs pu -> 
    reachable (pu, (aspc, ispc, sc)) ini_st T cst O laump -> 
    pool_ks_no_int_apicode aspc T.
Proof.
  introv Hn Hrc.
  assert (Hr := Hrc).
  inverts Hrc.
  simpljoin.
  eapply pool_ks_noint_apicode_hpstepokstar_preserve; eauto.
  { (* task_pool_no_sub_abs *)
    simpljoin.
    unfolds.
    introv HC.
    unfold init_tsk in *.
    simpljoin.
    eapply H0 in HC; eauto.
    simpljoin.
    unfolds in Hn.
    specializes Hn; eauto.
    unfold nilcont. 
    unfolds.
    split; simpl; auto.
  }
  { (* pool_ks_no_int_apicode *)
    simpljoin.
    unfolds.
    introv HC.
    unfold init_tsk in *.
    simpljoin.
    eapply H0 in HC; eauto.
    simpljoin.
    unfolds in Hn.
    specializes Hn; eauto.
    unfold nilcont.
    unfolds.
    split; simpl; auto.
    unfolds.
    introv Hs Hk.
    inverts Hs.
    simpl in Hn. false.
  }
Qed.

