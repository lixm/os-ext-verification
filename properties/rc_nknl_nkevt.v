
Require Import memory.
Require Import anno_language.  
Require Import anno_opsem. 
Require Import aux_notations.
Require Import join_lib.
Require Import aux_tacs.

(* Require Import sem_sys. *)
(* Require Import rc_kevt_nonest. *)

(* given command is not a kernel statement *) 
Definition not_knl_stmt (c: cureval) :=   
  (exists e, c = cure e)
  \/ exists s, c = curs s /\ (~exists ss, s = hapi_code ss).

Definition nknl_nkevt0 c ks :=
  not_knl_stmt c -> absintcont ks = None. 

Fixpoint nknl_nkevt_cont (ks: stmtcont) :=
  match ks with
    kstop => True
  | kseq _ ks | kcall _ _ _ ks | kint _ _ _ ks | kassignr _ _ ks | kassignl _ _ ks
  | kfuneval _ _ _ _ ks | kif _ _ ks | kwhile _ _ ks | kret ks => nknl_nkevt_cont ks
  | kevent c ke ks => nknl_nkevt0 c ks /\ nknl_nkevt_cont ks 
  end.

Definition nknl_nkevt (C: code) :=
  forall c ke ks,
    C = (c, (ke, ks)) -> nknl_nkevt0 c ks /\ nknl_nkevt_cont ks. 

Definition pool_nknl_nkevt T :=
  forall t C, get T t = Some C -> nknl_nkevt C. 


Lemma no_intcont_cc:
  forall ks ks' f s E, 
    absintcont ks = None -> 
    callcont ks = Some (kcall f s E ks') -> 
    absintcont ks' = None.
Proof.
  induction ks; 
    introv Hnn Hcc; 
    try (simpl in Hcc; tryfalse); 
    try (simpl in Hnn; eapply IHks; eauto; fail).  
  inverts Hcc. simpl in Hnn. auto.
Qed.

Lemma nknl_expr: forall e, not_knl_stmt (cure e).
Proof.
  intros.
  unfolds.
  left.
  eexists; eauto.
Qed.

Local Hint Resolve nknl_expr : not_knl_lemmas.

Lemma nknl_skip: forall v, not_knl_stmt ([v]).
Proof.
  intros.
  unfolds.
  right.
  eexists.
  split; eauto.
  introv Hf.
  simpljoin.
  inverts H.
Qed.

Local Hint Resolve nknl_skip: not_knl_lemmas. 

Lemma nknl_nkevt_estep_preserve:
  forall c ke m c' ke' m' ks, 
    estep c ke m c' ke' m' -> 
    nknl_nkevt (c, (ke, ks)) ->
    nknl_nkevt (c', (ke', ks)). 
Proof.
  introv Hes Hnn.
  unfold nknl_nkevt in *.
  introv Heq; inverts Heq.
  inverts Hes; 
    try (
        specializes Hnn; eauto; 
        destruct Hnn as (Hc & Hcont); 
        split; eauto;  
        unfold nknl_nkevt0 in *;
        intros; eapply Hc; eauto;
        eauto with not_knl_lemmas; fail).
Qed.

Lemma nknl_cstmt:
  forall s, (~(exists cd, s = hapi_code cd)) -> not_knl_stmt (curs s).  
Proof.
  intros.
  unfolds.
  right.
  eexists.
  splits; eauto.
Qed. 

Lemma nknl_nkevt_callcont:
  forall ks f s le' ks0, 
    nknl_nkevt_cont ks ->
    callcont ks = Some (kcall f s le' ks0) -> 
    nknl_nkevt_cont ks0. 
Proof.
  induction ks; 
    introv Hnn Hcc;
    try (simpl in Hnn; simpl in Hcc; inverts Hcc; auto; tryfalse; fail); 
    try (inverts Hcc; eapply IHks; eauto; fail).
  -
    eapply IHks; eauto.
    simpl in Hnn. simpljoin. auto. 
Qed.   

Lemma nknl_nkevt_sstep_preserve:
  forall pu c ks m c' ks' m' ke, 
    sstep pu c ks m c' ks' m' ->
    nknl_nkevt (c, (ke, ks)) ->
    nknl_nkevt (c', (ke, ks')).
Proof.
  introv Hsp Hnn.
  unfold nknl_nkevt in *.
  introv Heq; inverts Heq.
  specializes Hnn; eauto.
  inverts Hsp;
    try (
        simpl nknl_nkevt_cont; 
        simpl nknl_nkevt_cont in Hnn; 
        destruct Hnn as (Hc & Hcont); 
        split; eauto; 
        unfold nknl_nkevt0 in *; 
        intros; eapply Hc; eauto; 
        apply nknl_cstmt; introv Hf; simpljoin; tryfalse; fail). 
  -
    destruct Hnn as (Hc & Hcont).
    split; eauto.
    2: { eapply nknl_nkevt_callcont; eauto. }
    unfolds. intros. unfolds in Hc.
    specializes Hc; eauto.
    eapply nknl_cstmt; eauto.
    introv Hf. simpljoin. tryfalse.     
    eapply no_intcont_cc; eauto. 
Qed. 

Lemma nknl_nkevt_cstep_preserve: 
  forall pc c ke ks c' ke' ks' ge le M ge' le' M', 
    cstep pc (c, (ke, ks)) (ge, le, M) (c', (ke', ks')) (ge', le', M') -> 
    nknl_nkevt (c, (ke, ks)) ->
    nknl_nkevt (c', (ke', ks')).
Proof.
  introv Hcs Hnn.
  inverts Hcs; 
    match goal with H: (_, (_, _)) = _ |- _ => inverts H end.
  eapply nknl_nkevt_estep_preserve; eauto.
  eapply nknl_nkevt_sstep_preserve; eauto.
Qed. 

Lemma knl_api: forall cd, ~not_knl_stmt (curs (hapi_code cd)).
Proof.
  intros.
  introv Hf.
  unfolds in Hf.
  inverts Hf.
  inverts H; tryfalse.
  simpljoin.
  inverts H.
  apply H0.
  eexists; eauto.
Qed.

Lemma nknl_nkevt_hapistep_preserve: 
  forall spc c ke ks O c' ke' ks' O' lau lau', 
    (* kevt_no_nest ks ->   *)
    hapistep spc (c, (ke, ks)) O lau (c', (ke', ks')) O' lau' ->  
    nknl_nkevt (c, (ke, ks)) ->
    nknl_nkevt (c', (ke', ks')). 
Proof.
  introv (* Hnst *) Hstep Hnn.
  inverts Hstep.
  -
    match goal with H: (_, (_, _)) = _ |- _ => inverts H end.
    match goal with H: (_, (_, _)) = _ |- _ => inverts H end.
    unfolds.
    introv Hf; inverts Hf. 
    split.
    + 
      unfolds. introv Hf.
      eapply knl_api in Hf. tryfalse.
    +
      unfolds in Hnn.
      specializes Hnn; eauto.
      simpljoin; auto. 
  -
    unfolds.
    introv Hf; inverts Hf.
    split.
    +
      unfolds. introv Hf.
      eapply knl_api in Hf. tryfalse.
    +
      unfolds in Hnn.
      specializes Hnn; eauto. 
      simpljoin.
      auto. 
  -
    unfolds. introv Hf.
    inverts Hf.
    split.
    +
      unfolds.
      introv H_.
      auto.
    +
      unfolds in Hnn.
      specializes Hnn; eauto.
      simpljoin.
      auto. 
  -
    unfolds.
    introv Heq.
    inverts Heq.
    unfolds in Hnn.
    specializes Hnn; eauto.
    simpl nknl_nkevt_cont in Hnn.
    simpljoin.
    split; auto. 
Qed.

Lemma nknl_nkevt_htstep_preserve: 
  forall t hp c ke ks cst O c' ke' ks' cst' O' lau lau',   
    (* kevt_no_nest ks ->   *)
    htstep hp t (c, (ke, ks)) cst O lau (c', (ke', ks')) cst' O' lau' ->  
    nknl_nkevt (c, (ke, ks)) ->
    nknl_nkevt (c', (ke', ks')). 
Proof.
  introv (* Hnst  *)Hstep Hnn.
  inverts Hstep.
  - eapply nknl_nkevt_cstep_preserve; eauto.
  - eapply nknl_nkevt_hapistep_preserve; eauto. 
Qed.

Lemma nknl_nkevt_htistep_preserve:
  forall ospc c ke ks O c' ke' ks'  O', 
    htistep ospc (c, (ke, ks)) O (c', (ke', ks')) O' ->
    nknl_nkevt (c, (ke, ks)) ->
    nknl_nkevt (c', (ke', ks')). 
Proof.
  introv Hsp Hnn.
  unfolds in Hnn.
  unfolds.
  introv Heq; inverts Heq.
  specializes Hnn; eauto.
  inverts Hsp.
  simpljoin.
  split.
  - unfolds.
    introv H_.
    eapply knl_api in H_. tryfalse.    
  -
    simpl nknl_nkevt_cont.
    split; eauto. 
Qed.     

Lemma nknl_nkevt_hpstep_preserve:
  forall hp T cst O T' cst' O' lau lau', 
    (* pool_kevt_no_nest T ->  *)
    hpstep hp T cst O lau T' cst' O' lau' ->
    pool_nknl_nkevt T ->
    pool_nknl_nkevt T'. 
Proof.
  introv (* Hpn  *)Hstep Hnn.
  inverts Hstep.
  -
    unfold pool_nknl_nkevt in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      destruct C as (c_, (ke_, ks_)).
      destruct C0 as (c0_, (ke0_, ks0_)).
      eapply nknl_nkevt_htstep_preserve; eauto. 
    * rewrite set_a_get_a' in Hget; eauto.
  -
    unfold pool_nknl_nkevt in *. 
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      destruct C as (c_, (ke_, ks_)). 
      destruct C0 as (c0_, (ke0_, ks0_)).
      eapply nknl_nkevt_htistep_preserve; eauto. 
    * rewrite set_a_get_a' in Hget; eauto.
  -  
    unfold pool_nknl_nkevt in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget.
      inverts Hget.
      introv Hf; inverts Hf.
      split.
      **
        unfolds. introv Hf. 
        eapply knl_api in Hf. tryfalse.
      **
        specializes Hnn; eauto.
        unfolds in Hnn.
        specializes Hnn; eauto.
        simpljoin; auto. 
    *      
      rewrite set_a_get_a' in Hget; eauto.
Qed.

Lemma nknl_nkevt_hpstepokstar_preserve: 
  forall pu aspc ispc sc T cst O T' cst' O' lau lau',    
    hpstepokstar (pu, (aspc, ispc, sc)) T cst O lau T' cst' O' lau' ->
    (* pool_kevt_no_nest T ->      *)
    pool_nknl_nkevt T ->
    pool_nknl_nkevt T'. 
Proof.
  introv Hstepstar.
  remember (pu, (aspc, ispc, sc)) as hp.
  induction Hstepstar.
  intros; auto.
  introv Hpn Hnn.
  inverts H. 
  lets H_: nknl_nkevt_hpstep_preserve H0; eauto.
  eapply IHHstepstar; eauto.
Qed.

Require Import init.
Require Import common_defs. 

Lemma reachable_nknl_nkevt:
  forall pu aspc ispc sc T cst O lau ini_st, 
    reachable (pu, (aspc, ispc, sc)) ini_st T cst O lau ->
    pool_nknl_nkevt T.
Proof.
  introv Hrc.
  inverts Hrc.
  simpljoin.
  eapply nknl_nkevt_hpstepokstar_preserve; eauto.

  rename H0 into Hit.
  rename H1 into His.
  unfolds in Hit.
  destruct Hit as (_ & Ha).
  unfolds.
  introv Hget.
  lets H_: Ha Hget.
  simpljoin.
  unfolds.
  introv Heq.
  unfolds in Heq. inverts Heq.
  split.
  - unfolds.
    intros.
    simpl. auto.
  -
    simpl. auto. 
Qed. 
    
 
