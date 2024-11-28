
Require Import memory.
Require Import anno_language. 
Require Import anno_opsem.  
Require Import aux_notations.
Require Import join_lib.
Require Import aux_tacs.

Fixpoint stmt_noabs (s: stmts) :=
  match s with
    sskip _ | sassign _ _ | sret | srete _ | scall _ _ | scalle _ _ _ 
  | sfexec _ _ _ | sfree _ _ | salloc _ _ | sprim _ | sprint _ => True 
  | sif e s1 s2 => stmt_noabs s1 /\ stmt_noabs s2
  | sifthen e s => stmt_noabs s 
  | swhile e s => stmt_noabs s
  | sseq s1 s2 => stmt_noabs s1 /\ stmt_noabs s2 
  | hapi_code cd => False
  end.

Definition ceval_noabs (c: cureval) :=
  match c with
    cure e => True 
  | curs s => stmt_noabs s
  end.

Fixpoint ks_noabs (ks: stmtcont) :=
  match ks with 
    kstop => True
  | kseq s ks => stmt_noabs s /\ ks_noabs ks
  | kcall f s E ks => stmt_noabs s /\ ks_noabs ks
  | kint ce ke E ks => ceval_noabs ce /\ ks_noabs ks
  | kassignr e tp ks => ks_noabs ks
  | kassignl v tp ks => ks_noabs ks
  | kfuneval f vl tl el ks => ks_noabs ks 
  | kif s1 s2 ks => stmt_noabs s1 /\ stmt_noabs s2 /\ ks_noabs ks
  | kwhile e s ks => stmt_noabs s /\ ks_noabs ks 
  | kret ks => ks_noabs ks 
  | kevent ce ke ks =>
      (ceval_noabs ce \/ (exists cd, ce = curs (hapi_code cd)))
      /\ ks_noabs ks
  end.

Definition tskcode_no_sub_abs (C: code) :=
  match C with
    (c, (ke, ks)) =>
      (ceval_noabs c \/ (exists cd, c = curs (hapi_code cd)))
        /\ ks_noabs ks
  end.

Lemma noabs_preserve_estep: 
  forall c c' ke ke' ks m m', 
    estep c ke m c' ke' m' ->
    tskcode_no_sub_abs (c, (ke, ks)) ->
    tskcode_no_sub_abs (c', (ke', ks)). 
Proof.
  introv Hestep Hnabs.
  inverts Hestep; 
    try (simpl in Hnabs; simpl; simpljoin; split; auto; fail). 
Qed. 

Definition pu_noabs (pu: progunit) :=  
  (forall f t dl1 dl2 s, pu f = Some (t, dl1, dl2, s) -> stmt_noabs s). 

Lemma callcont_noabs:
  forall ks f s E ks', 
    ks_noabs ks ->
    callcont ks = Some (kcall f s E ks') ->
    ks_noabs ks'.
Proof.
  induction ks; introv Hnabs Hcc;
    try (simpl in Hcc; tryfalse; fail); 
    try (simpl in Hcc; simpl in Hnabs; simpljoin; auto;
         eapply IHks; eauto; fail).    
  -
    simpl in Hcc.
    inverts Hcc.
    simpl in Hnabs. simpljoin. auto.
Qed.     
  
Lemma noabs_preserve_sstep:
  forall pu c c' ks ks' m m',
    pu_noabs pu -> 
    sstep pu c ks m c' ks' m' ->
    tskcode_no_sub_abs (c, (kenil, ks)) ->
    tskcode_no_sub_abs (c', (kenil, ks')).  
Proof.
  introv Hpu Hsstep Hnabs.
  unfolds in Hpu.
  inverts Hsstep; simpl; simpl in Hnabs; simpljoin; 
    try (split; auto; fail).
  - split; auto. 
    split; auto. eapply Hpu; eauto.
  - split; auto.
    eapply callcont_noabs; eauto.
  - inverts H.
    simpljoin. splits; auto.
    simpljoin. tryfalse.
  - inverts H.
    simpljoin.
    splits; auto.
    simpljoin. tryfalse.
  - splits; auto.
    inverts H.
    auto.
    simpljoin. tryfalse. 
  - splits; auto.
    inverts H.
    auto.
    simpljoin. tryfalse. 
Qed.     

Lemma noabs_preserve_cstep:
  forall pu C m C' m',
    pu_noabs pu -> 
    cstep pu C m C' m' -> 
    tskcode_no_sub_abs C ->
    tskcode_no_sub_abs C'.
Proof.
  introv Hpu Hcstep Hnabs.
  inverts Hcstep.
  - eapply noabs_preserve_estep; eauto.
  - eapply noabs_preserve_sstep; eauto.
Qed. 

Lemma noabs_preserve_hapistep:
  forall osspc cd O cd' O' lau lau',
    hapistep osspc cd O lau cd' O' lau' ->
    tskcode_no_sub_abs cd ->
    tskcode_no_sub_abs cd'. 
Proof.
  introv Hastep Hnabs.
  inverts Hastep; 
    try (simpl; simpl in Hnabs;
         simpljoin;
         split; auto; 
         right; eexists; eauto; fail).
Qed. 
    
Lemma noabs_preserve_htstep: 
  forall hp pu aspc t C cst O C' cst' O' lau lau',
    hp = (pu, aspc) -> 
    pu_noabs pu -> 
    htstep hp t C cst O lau C' cst' O' lau' ->
    tskcode_no_sub_abs C ->
    tskcode_no_sub_abs C'. 
Proof.
  introv Hhp Hpu Hstep Hnabs.
  destruct hp as (pu_ & spc_).
  inverts Hhp.
  invert Hstep.
  - intros. inverts H. eapply noabs_preserve_cstep; eauto.
  - intros. inverts H. eapply noabs_preserve_hapistep; eauto.
Qed.

Definition task_pool_no_sub_abs (T: tasks) :=
  forall t C, get T t = Some C -> tskcode_no_sub_abs C. 

Lemma noabs_preserve_hpstep:
  forall hp pu spc T cst O T' cst' O' lau lau',
    hp = (pu, spc) ->
    pu_noabs pu -> 
    hpstep hp T cst O lau T' cst' O' lau' ->
    task_pool_no_sub_abs T ->
    task_pool_no_sub_abs T'. 
Proof.
  introv Hhp Hpu Hstep Hnabs.
  inverts Hstep.
  - unfold task_pool_no_sub_abs in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0. rewrite set_a_get_a in Hget.
      inverts Hget.
      eapply noabs_preserve_htstep; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  - inverts H.
    match goal with H': htistep _ _ _ _ _ |- _ => inverts H' end.
    unfolds.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0.
      rewrite set_a_get_a in Hget.
      inverts Hget.
      simpl. apply Hnabs in H1. simpl in H1.
      simpljoin.
      splits; auto.
      right; eexists; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  - inverts H.
    unfold task_pool_no_sub_abs in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0.
      rewrite set_a_get_a in Hget.
      inverts Hget.
      apply Hnabs in H2.
      simpl in H2. simpl.
      simpljoin.
      split; auto.
      right. eexists; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
Qed.       

Lemma no_sub_abs_preserve_hpstepokstar:
  forall hp pu spc T cst O T' cst' O' lau lau', 
    hp = (pu, spc) ->
    pu_noabs pu -> 
    hpstepokstar hp T cst O lau T' cst' O' lau' ->
    task_pool_no_sub_abs T ->
    task_pool_no_sub_abs T'.
Proof.
  introv Hhp Hpu Hsteps.
  induction Hsteps.
  - auto.
  - introv Hnabs.
    eapply IHHsteps; eauto.
    inverts H.
    eapply noabs_preserve_hpstep; eauto.
Qed. 

Require Import init.
Require Import common_defs. 

Lemma reachable_no_sub_abs: 
  forall hp pu spc T cst O lau ini_st,
    hp = (pu, spc) -> 
    pu_noabs pu -> 
    reachable hp ini_st T cst O lau ->
    task_pool_no_sub_abs T. 
Proof.
  introv Hhp Hnabs Hrc. 
  unfolds in Hrc.
  destruct Hrc as (pu_ & spc_ & Hhp' & Hex).
  destruct Hex as (T0 & cst0 & O0 & aust0 & Hit & His & Hsteps). 

  unfolds in Hit.
  destruct Hit as (Heqd & Hall).
  rewrite Hhp in Hhp'. inverts Hhp'.

  eapply no_sub_abs_preserve_hpstepokstar; eauto.
  unfolds.
  introv Hget.
  unfold get in Hget. unfold TasksMap in Hget.
  apply Hall in Hget.
  simpl.
  simpljoin.
  unfolds in Hnabs.
  unfolds.
  unfold nilcont.
  simpl.
  split; auto.
  left.
  eapply Hnabs; eauto.
Qed. 

