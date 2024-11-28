
Require Import memory.
Require Import anno_language.
Require Import anno_opsem.
Require Import init.

Require Import good_code.

Require Import succ_gen. 
Require Import join_lib.

Require Import common_defs.
Require Import aux_tacs.
Require Import rc_no_subabs.
Require Import rc_int_code.
Require Import rc_ks_noint_apicode.


Definition init_sat_dtinv 
  (ini_st: progunit -> tasks -> clientst -> osabst -> LAuxStMod.map -> Prop)
  (I: osabst -> LAuxStMod.map -> Prop) := 
  forall pu T cst O laump,
    init_tsk pu T O -> 
    ini_st pu T cst O laump ->
    I O laump.  

Definition api_preserves_dtinv
  (apispec: fid -> option osapi) (I: osabst -> LAuxStMod.map -> Prop) :=  
  forall f vl cd cd' ac tp laump lau laump' lau' O O' t sc, 
    apispec f = Some (ac, tp) ->
    has_succ (ac vl) cd -> 
    head_asrt_sat cd lau ->
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) ->
    get laump t = Some lau ->
    laump' = set laump t lau' ->
    I O laump ->
    I O' laump'. 

Definition int_preserves_dtinv
  (intspec: hid -> option int_code) (I: osabst -> LAuxStMod.map -> Prop) :=  
  forall h cd0 cd cd' laump lau laump' lau' O O' t sc, 
    intspec h = Some cd0 ->
    has_succ cd0 cd -> 
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) ->
    get laump t = Some lau ->
    laump' = set laump t lau' ->
    I O laump ->
    I O' laump'. 
  
Definition rc_asrt
  pu osspc 
  (ini_st: progunit -> tasks -> clientst -> osabst -> LAuxStMod.map -> Prop)
  (li: LAuxSt -> Prop)
  :=    
  forall T cst O laump, 
    reachable (pu, osspc) ini_st T cst O laump ->
    pool_hasrt_sat T laump li.

Definition dti_change_curt (dti: osabst -> LAuxStMod.map -> Prop) :=
  forall t laump O, 
    dti O laump -> 
    dti (set O curtid (oscurt t)) laump. 

Definition rc_dtinv
  pu osspc 
  (ini_st: progunit -> tasks -> clientst -> osabst -> LAuxStMod.map -> Prop) 
  (dtinv: osabst -> LAuxStMod.map -> Prop) := 
  forall T cst O aust,
    good_client_code pu ->
    reachable (pu, osspc) ini_st T cst O aust ->
    dtinv O aust. 

Lemma GoodStmt_noabs: 
  forall s, GoodStmt_h s -> stmt_noabs s.
Proof.
  inductions s; 
    introv HGS;
    try (simpl; auto).
  - 
    simpl in HGS.
    simpljoin.
    split; eauto.
  -
    simpl in HGS.
    simpljoin.
    split; eauto.
Qed. 

Lemma good_client_code_impl_noabs:
  forall cliprogs, 
    good_client_code cliprogs ->
    pu_noabs cliprogs.
Proof.
  introv Hgcc.
  unfolds in Hgcc.
  unfolds.
  introv Hcf.
  lets H__: Hgcc Hcf.
  apply GoodStmt_noabs; auto. 
Qed. 

Lemma apistep_preserves_dtinv_hpstep_preserves_dtinv:
  forall pu aspc ispc sc ini_st dti O O' cst cst' T T' laump laump' li, 
    api_preserves_dtinv aspc dti ->
    int_preserves_dtinv ispc dti -> 
    good_client_code pu -> 
    reachable (pu, (aspc, ispc, sc)) ini_st T cst O laump -> 
    hpstep (pu, (aspc, ispc, sc)) T cst O laump T' cst' O' laump' ->
    (* good_task_code aspc ispc T ->  *)
    pool_hasrt_sat T laump li ->    
    dti_change_curt dti -> 
    dti O laump ->
    dti O' laump'.  
Proof.
  introv Hapd Hipd Hgc Hrc Hhp Hphs Hdct Hdti.
  inverts Hhp.
  - (* htstep *)
    mttac htstep ltac: (fun H => inverts H).
    + 
      match goal with H: (_, _) = (_, _) |- _ => inverts H end.
      mttac cstep ltac: (fun H => inverts H).
      *
        mttac estep ltac: (fun H => inverts H); 
          try (rewrite get_set_same; auto; fail).
      *
        mttac sstep ltac: (fun H => inverts H);
          try (rewrite get_set_same; auto; fail).
    +
      match goal with H: (_, _) = (_, _) |- _ => inverts H end.
      unfolds in Hapd.
      mttac hapistep ltac: (fun H => inverts H).
      *
        match goal with H: (_, _) = (_, _) |- _ => inverts H end.
        rewrite get_set_same; eauto.
      *
        lets Hsat: Hphs H1; eauto.
        specializes Hsat; eauto.
        unfolds in Hsat.
        destruct Hsat as (c & ke0 & ks0 & Heq & Hcmd & Hcont).
        inverts Heq. 
        casetac (absintcont ks0) (None: option stmtcont) Ht Hf.
        **
          lets Hconj: Hcmd Ht; eauto.
          destruct Hconj as (Hhs & Hnml).
          specializes Hhs; eauto.
          lets H__: reachable_ks_noint_apicode Hrc; eauto.
          eapply good_client_code_impl_noabs; eauto. 
          lets H_: H__ H1; eauto. clear H__.
          simpl in H_.
          destruct H_ as (Hca & Hconta). 
          unfolds in Hca.
          specializes Hca; eauto.
          destruct Hca as [Hsucc | [Hf | Hf]].
          ***
            destruct Hsucc as (f & ac & ft & vl & Hfid & Hsuc).
            eapply Hapd; eauto.
          ***
            subst cd.
            mttac spec_step ltac: (fun H => inverts H).
          ***
            simpljoin.
            mttac spec_step ltac: (fun H => inverts H).
        **
          clear Hcmd. clear Hapd.
          lets H__: reachable_apicode_type_c Hrc; eauto.
          eapply good_client_code_impl_noabs; eauto.
          lets H_: H__ H1; eauto. clear H__.
          simpl in H_.
          destruct H_ as (Hic & Hconti).
          specializes Hic; eauto.
          destruct Hic as (iid & icd & Hicd & Hor).
          destruct Hor as [Hsuc | [Hf_ | Hf_]].
          ***
            unfolds in Hipd.
            eapply Hipd; eauto.
          ***
            subst cd. mttac spec_step ltac: (fun H => inverts H).
          ***
            simpljoin. mttac spec_step ltac: (fun H => inverts H).
      *
        rewrite get_set_same; eauto.
      *
        rewrite get_set_same; eauto.
  -
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
    mttac htistep ltac: (fun H => inverts H). 
    auto.
  -
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
    apply Hdct; auto.
Qed.          

Lemma hpstepokstar_extend: 
  forall hp T0 cst0 O0 aust0 T cst O aust T' cst' O' aust', 
    hpstepokstar hp T0 cst0 O0 aust0 T cst O aust ->
    hpstep_ok hp T cst O aust T' cst' O' aust' ->
    hpstepokstar hp T0 cst0 O0 aust0 T' cst' O' aust'.
Proof.
  introv Hsps Hsp.
  induction Hsps.
  - 
    eapply hp_stepS; eauto.
    constructors.
  -
    specializes IHHsps; eauto.
    clear Hsps Hsp.
    eapply hp_stepS; eauto.
Qed. 

Lemma reachable_extend:
  forall hp ini_st T cst O aust T' cst' O' aust', 
    reachable hp ini_st T cst O aust -> 
    hpstep_ok hp T cst O aust T' cst' O' aust' ->
    reachable hp ini_st T' cst' O' aust'.
Proof.
  introv Hrc Hsp.
  unfold reachable in *.
  simpljoin.
  do 2 eexists; splits; eauto.
  do 4 eexists; splits; eauto.
  eapply hpstepokstar_extend; eauto.
Qed.   

Lemma apistep_preserves_dtinv_hpstepstar_preserves_dtinv: 
  forall pu aspc ispc sc ini_st dti O O' cst cst' T T' laump laump' li, 
    hpstepokstar (pu, (aspc, ispc, sc)) T cst O laump T' cst' O' laump' ->
    api_preserves_dtinv aspc dti ->
    int_preserves_dtinv ispc dti -> 
    good_client_code pu -> 
    reachable (pu, (aspc, ispc, sc)) ini_st T cst O laump -> 
    rc_asrt pu (aspc, ispc, sc) ini_st li ->    
    dti_change_curt dti -> 
    dti O laump ->
    dti O' laump'.
Proof.
  introv Hsps.
  inductions Hsps.
  - intros. auto.
  - intros.
    eapply IHHsps; eauto.
    eapply reachable_extend; eauto.
    mttac hpstep_ok invtac.
    eapply apistep_preserves_dtinv_hpstep_preserves_dtinv; eauto.
Qed.   


(* the theorem that generates the proof obligations for the condition 
    rc_dtinv --- this condition expresses that the global invariant on the
    abstract states is satisfied by all reachable configurations of the system*) 
Lemma proof_method:  
  forall pu aspc ispc sc ini_st dti li,
    init_sat_dtinv ini_st dti ->
    api_preserves_dtinv aspc dti ->
    int_preserves_dtinv ispc dti ->
    dti_change_curt dti -> 
    rc_asrt pu (aspc, ispc, sc) ini_st li ->
    rc_dtinv pu (aspc, ispc, sc) ini_st dti.
Proof.
  introv Hisd Hapd Hipd Hdchg Hra.
  unfolds.
  introv Hgc Hrc.
  unfolds in Hrc.
  destruct Hrc as (pu0 & spc & Heq & Hex).
  destruct Hex as (T0 & cst0 & O0 & aust0 & Hit & His & Hsps).
  assert (Hrc0: reachable (pu, (aspc, ispc, sc)) ini_st T0 cst0 O0 aust0).
  {
    unfolds. do 2 eexists. splits; eauto.
    do 4 eexists; splits; eauto.
    constructors; auto.
  }
  inverts Heq.
  lets H__: apistep_preserves_dtinv_hpstepstar_preserves_dtinv Hsps Hapd Hipd; eauto.
Qed. 
  

  
