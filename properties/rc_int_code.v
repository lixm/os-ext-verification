
Require Import memory.
Require Import anno_language. 
Require Import anno_opsem. 
Require Import aux_notations. 
Require Import join_lib.
Require Import aux_tacs. 

(* Require Import sem_sys. *)

Require Import succ_gen.

Require Import rc_no_subabs.
(* Require Import rc_kevt_nonest. *)
Require Import rc_nknl_nkevt.

Definition apicode_type_c (ispc: hid -> option int_code) (C:code)  :=
  match C with
    (c, (ke, ks))=>
      (forall cd,
          absintcont ks <> None ->
          c = curs (hapi_code cd) ->
          exists iid icode,
            ispc iid = Some icode /\
              (has_succ icode cd \/ cd = ABORT \/ (exists vs, cd = END vs)))   
  end.

Fixpoint code_tp_cont (ispc: hid -> option int_code) (ks: stmtcont) := 
  match ks with
    kstop => True
  | kseq _ ks | kcall _ _ _ ks | kint _ _ _ ks | kassignr _ _ ks | kassignl _ _ ks
  | kfuneval _ _ _ _ ks | kif _ _ ks | kwhile _ _ ks | kret ks => code_tp_cont ispc ks 
  | kevent c ke ks =>
      code_tp_cont ispc ks /\ 
        (forall cd,
            absintcont ks <> None ->
            c = curs (hapi_code cd) ->
            exists iid icode,
              ispc iid = Some icode /\
                (has_succ icode cd \/ cd = ABORT \/ (exists vs, cd = END vs))) 
  end.

Definition kevt_impl_icode (ispc: hid -> option int_code) (C: code) :=
  match C with
    (c, (ke, ks)) =>apicode_type_c ispc C /\ code_tp_cont ispc ks
  end.

Definition pool_int_code (ispc: hid -> option int_code) (T: tasks) :=
  forall t C, get T t = Some C -> kevt_impl_icode ispc C.   


Lemma code_tp_cont_call:
  forall ks f s le' ks' ispc, 
    code_tp_cont ispc ks ->
    callcont ks = Some (kcall f s le' ks') ->
    code_tp_cont ispc ks'.
Proof.
  inductions ks; 
    introv Hcont Heq; 
    try (simpl in Heq; tryfalse; fail); 
    try (simpl in Heq; 
         eapply IHks; eauto; fail).
  -
    simpl in Heq.
    inverts Heq.
    simpl in Hcont. 
    auto. 
  -
    simpl in Heq.
    eapply IHks; eauto.
    simpl in Hcont.
    simpljoin.
    auto. 
Qed. 

Lemma int_code_estep_preserve:
  forall c ke m c' ke' m' ks ispc, 
    estep c ke m c' ke' m' ->
    kevt_impl_icode ispc (c,(ke,ks)) ->
    kevt_impl_icode ispc (c',(ke',ks))  .
Proof.
  introv Hstep Hic.
  unfolds. unfolds in Hic.
  destruct Hic as (Hc & Hcont).
  split; auto. 
  - introv Habsintcont Hcurapi.
    inverts Hstep;tryfalse.
Qed.

Lemma int_code_sstep_preserve:
  forall pu c ks m c' ks' m' ke ispc, 
    sstep pu c ks m c' ks' m' ->
    tskcode_no_sub_abs (c,(ke,ks)) ->
    kevt_impl_icode ispc (c, (ke, ks)) ->
    kevt_impl_icode ispc (c', (ke, ks')).
Proof.
  introv Hsp Hns Hic.
  unfolds in Hic. unfolds.
  simpl apicode_type_c in *.
  inverts Hsp; 
    try (
        simpljoin; 
        simpl code_tp_cont; 
        split; eauto; 
        introv Hnn Hf; 
        inverts Hf; fail); 
    try (
        simpl code_tp_cont in Hic;
        simpl code_tp_cont; 
        simpljoin; 
        split; eauto; 
        introv _ Heq; 
        inverts Heq; 
        destruct Hns as (_ & Hf); 
        unfolds in Hf; 
        destruct Hf as (Hf & _); 
        unfolds in Hf; tryfalse; fail).
  -
    split.
    + introv _ Hf. inverts Hf.
    + destruct Hic as (Hc & Hcont).
      eapply code_tp_cont_call; eauto.
  -
    simpl code_tp_cont in Hic; 
      simpl code_tp_cont; 
      simpljoin; 
      split; eauto; 
      introv _ Heq; 
      inverts Heq; 
      destruct Hns as (Hf & _); 
      destruct Hf as [Hf | Hf]; 
      [simpl in Hf; simpljoin; false | simpljoin; false]. 
  -
    simpl code_tp_cont in Hic; 
      simpljoin; 
      split; eauto; 
      introv _ Heq; 
      inverts Heq; 
      destruct Hns as (_ & Hf); 
      simpl in Hf; 
      simpljoin; false. 
Qed.     

Lemma int_code_cstep_preserve:
  forall pu C m C' m' ispc, 
    cstep pu C m C' m' ->
    tskcode_no_sub_abs C ->
    kevt_impl_icode ispc C ->
    kevt_impl_icode ispc C' .
Proof.
  introv Hstep Htsknosubabs Hatc .
  inverts Hstep.
  eapply int_code_estep_preserve;eauto.
  eapply int_code_sstep_preserve;eauto.
Qed.

Lemma int_code_specstep_preserve:
  forall sc cd O cd' O' ke ks lau lau' ispc, 
    spec_step sc cd O lau cd' O' lau' ->
    kevt_impl_icode ispc (curs (hapi_code cd), (ke, ks)) ->
    kevt_impl_icode ispc (curs (hapi_code cd'), (ke, ks)).  
Proof.
  introv Hstep Hatc.
  unfolds.
  unfolds in Hatc.
  simpljoin.
  split; auto.

  simpl in H.
  simpl.
  introv Hnn Heq.
  specializes H; eauto.
  inverts Heq.
  destruct H as (iid & ic & Hic & Hor).
  do 2 eexists.
  splits; eauto.

  destruct Hor as [Hl | [Hf | Hf]].
  - lets H__: succ_step_preserve Hl; eauto.
  - subst cd. inverts Hstep.
  - simpljoin.     
    inverts Hstep.
Qed. 

Lemma int_code_hapistep_preserve: 
  forall sc C O C' O' c ke ks lau lau' aspc ispc, 
    hapistep (aspc, ispc, sc) C O lau C' O' lau' ->
    C = (c, (ke, ks)) -> 
    (* kevt_no_nest ks -> *)
    nknl_nkevt C ->
    kevt_impl_icode ispc C ->
    kevt_impl_icode ispc C' .
Proof.
  introv Hstep Hc (* Hkevtnonest  *)Hnknlnkevt1 Hatc.
  inverts Hstep.
  - unfolds in Hatc.  
    unfolds.
    inverts H1.
    destruct Hatc as (Hatc & Hcont).
    split; auto.
    unfolds. 
    intros.
    inverts H2.
    specializes Hatc; eauto.
    unfolds in Hnknlnkevt1.
    specializes Hnknlnkevt1; eauto.
    destruct Hnknlnkevt1 as (Hn & _).
    unfolds in Hn.
    specializes Hn; eauto.
    eapply nknl_cstmt; eauto. 
    introv Hf. simpljoin; tryfalse.
    tryfalse. 
  - inverts H0.
    eapply int_code_specstep_preserve;eauto.
  - unfolds.
    unfolds in Hatc.
    inverts H0.
    simpljoin.
    split; auto. 
    unfolds; intros.
    tryfalse.
  - inverts H.
    unfolds.
    unfolds in Hatc.
    simpl code_tp_cont in Hatc. simpljoin.
    split; auto. 
Qed.

Lemma int_code_htstep_preserve:
  forall p sc t C cst O C' cst' O' ke ks c lau lau' aspc ispc, 
    htstep (p, (aspc, ispc, sc)) t C cst O lau C' cst' O' lau' ->
    C = (c, (ke, ks)) -> 
    (* kevt_no_nest ks ->   *)
    nknl_nkevt C ->
    tskcode_no_sub_abs C ->
    kevt_impl_icode ispc C ->
    kevt_impl_icode ispc C'.
Proof.
  introv Hstep HC Hnknlnevt Htsknosub1 (* Htsknosub2 *) Hatc.
  inverts Hstep.
  eapply int_code_cstep_preserve;eauto.
  eapply int_code_hapistep_preserve;eauto.
  inverts H.
  eauto.
Qed.

Lemma int_code_htistep_preserve:
  forall O C C' O' ispc, 
    htistep ispc C O C' O' ->
    (* kevt_no_nest ks ->   *)
    nknl_nkevt C->
    tskcode_no_sub_abs C ->
    kevt_impl_icode ispc C ->
    kevt_impl_icode ispc C'.
Proof.
  introv Hstep (* Hkevtnonest *) Hnknlnkevt1 Hnosubabs1 (* Hnosubabs2 *) Hatc.
  inverts Hstep.
  simpl in Hatc.
  destruct Hatc as (Hc & Hcont).
  simpl.
  split.
  - introv Hnn Heq.
    inverts Heq.
    do 2 eexists; split; eauto.
    left. constructors; auto.
  - split; auto.
Qed.     

Lemma pool_int_code_hpstep_preserve: 
  forall p sc T cst O T'  cst' O' lau lau' aspc ispc, 
    hpstep (p, (aspc, ispc, sc)) T cst O lau T' cst' O' lau' ->
    pool_nknl_nkevt T->
    task_pool_no_sub_abs T->
    (* pool_kevt_no_nest T ->   *)
    pool_int_code ispc T ->
    pool_int_code ispc T'.
Proof.
  introv Hstep Hpoolnknlnkevt Hpolnosubabs (* Hpolkevtnonest *) Hpolatc.
  unfolds in Hpoolnknlnkevt.
  unfolds in Hpolnosubabs.
  (* unfolds in Hpolkevtnonest. *)
  unfolds in Hpolatc.
  unfolds.
  introv Hget.
  inverts Hstep.
  - 
    casetac t t0 Ht Hf.
    * subst t0. rewrite set_a_get_a in Hget. inverts Hget.
      lets Hatc: Hpolatc H1.
      clear Hpolatc.
      destruct C0 as (c_, (ke_, ks_)).
      eapply int_code_htstep_preserve;eauto.
    * rewrite set_a_get_a' in Hget; eauto.
  - 
    casetac t t0 Ht Hf.
    * subst t0. rewrite set_a_get_a in Hget. inverts Hget.
      lets Hatc: Hpolatc H1.
      clear Hpolatc.
      destruct C0 as (c_, (ke_, ks_)).
      inverts H.
      eapply int_code_htistep_preserve;eauto.
    * rewrite set_a_get_a' in Hget; eauto.
  - 
    casetac t t0 Ht Hf.
    * subst t0. rewrite set_a_get_a in Hget. inverts Hget.
      lets Hatc: Hpolatc H2.
      unfolds in Hatc.
      unfolds.
      destruct Hatc as (Hatc & Hcont).
      split; auto. 
      introv Habsintcont Hcurs.
      specializes Hatc; eauto.
      destruct Hatc as (iid & ic & Hic & Hor).
      inverts Hcurs.
      destruct Hor as [Hhc | [Habt | Hend]].
      ** unfolds in Hhc. exists iid ic.
         splits; eauto.
         destruct Hhc.
         subst ic. left. right. constructors; eauto.
         left. right. eapply succ_seq_cd2; eauto.
      **
        inverts Habt.
      **
        simpljoin; tryfalse. 
    * rewrite set_a_get_a' in Hget; eauto.
Qed.

Lemma pool_int_code_hpstepokstar_preserve: 
  forall sc p T cst O T' cst' O' lau lau' aspc ispc, 
    pu_noabs p ->    
    hpstepokstar (p, (aspc, ispc, sc)) T cst O lau T' cst' O' lau' ->
    pool_nknl_nkevt T->
    task_pool_no_sub_abs T->
    (* pool_kevt_no_nest T ->       *)
    pool_int_code ispc T ->
    pool_int_code ispc T'.
Proof.
  introv Hp Hstep.
  inductions Hstep; introv Hpolnknlnkevt Hpolnosubabs Hpolatc. 
  auto.
  eapply IHHstep; eauto.
  inverts H.
  eapply nknl_nkevt_hpstep_preserve; eauto.
  inverts H.
  eapply noabs_preserve_hpstep;eauto.
  inverts H.
  eapply pool_int_code_hpstep_preserve;eauto.
Qed.

Require Import init.
Require Import common_defs. 

Lemma reachable_apicode_type_c: 
  forall p sc T cst O lau aspc ispc ini_st, 
    pu_noabs p ->
    reachable (p, (aspc, ispc, sc)) ini_st T cst O lau -> 
    pool_int_code ispc T. 
Proof.
  introv Hp Hrch.
  unfolds in Hrch.
  destruct Hrch as (pu & spc & Hhp & Hex).
  destruct Hex as (T0 & cst0 & O0 & aust0 & Hitt & Hits & Hsstar).
  assert(Hrc: reachable (p, (aspc, ispc, sc)) ini_st T0 cst0 O0 aust0).
  {
    unfolds.
    do 2 eexists.
    split; eauto.
    do 4 eexists.
    splits; eauto.
    constructors.
  }
  inverts Hhp.
  eapply pool_int_code_hpstepokstar_preserve;eauto.
  -
    eapply reachable_nknl_nkevt; eauto.
  -
    eapply reachable_no_sub_abs; eauto.
  -
    unfolds in Hitt.
    destruct Hitt as (Heqd & Hall).
    unfolds.
    introv Hget.
    lets H_:Hall Hget.
    simpljoin.
    unfold nilcont.
    simpl.
    split; auto.
    introv Hf. false. 
Qed.
