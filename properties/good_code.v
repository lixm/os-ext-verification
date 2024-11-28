
Require Import memory. 
Require Import anno_language.
Require Import anno_opsem.
Require Import aux_notations.
(* Require Import sem_sys. *)

Require Import succ_gen.
Require Import common_defs. 
Require Import aux_tacs. 

Require Import init.
Require Import join_lib. 

Fixpoint GoodStmt_h (s : stmts) {struct s} : Prop :=
  match s with
  | sskip _ => True
  | sassign _ _ => True
  | sif _ s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
  | sifthen _ s => GoodStmt_h s
  | swhile _ s' => GoodStmt_h s'
  | sret => True
  | srete  _ => True
  | scall f _ => True
  | scalle _ f _ => True
  | sseq s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
  | sfexec _ _ _ => False
  | sfree _ _ => False
  | salloc _ _ => False
  | sprim _ => True
  | sprint _ => True
  | hapi_code _ => False
  end.

Definition good_client_code (client_code: progunit) :=
      (forall (f : fid) (a : type) (b c : decllist) (s : stmts),
       client_code f = Some (a, b, c, s) -> GoodStmt_h s).

Definition good_api_stmt (aspc: fid -> option osapi) (ispc: hid -> option int_code) s :=   
  (exists f acode ft vl, aspc f = Some (acode, ft) /\ has_succ (acode vl) s) 
  \/ (exists h icode, ispc h = Some icode /\ has_succ icode s)    
  \/ (exists v, s = END v) \/ (s = ABORT).

Fixpoint goodstmt_h
  (aspc: fid -> option osapi) (ispc: hid -> option int_code) (s : stmts) {struct s} : Prop :=
  match s with
  | sskip _ => True
  | sassign _ _ => True
  | sif _ s1 s2 => goodstmt_h aspc ispc s1 /\ goodstmt_h aspc ispc s2
  | sifthen _ s => goodstmt_h aspc ispc s
  | swhile _ s' => goodstmt_h aspc ispc s'
  | sret => True
  | srete _ => True
  | scall f _ => True
  | scalle _ f _ => True
  | sseq s1 s2 => goodstmt_h aspc ispc s1 /\ goodstmt_h aspc ispc s2
  | sfexec _ _ _ => True
  | sfree _ _ => True
  | salloc _ _ => True
  | sprim _ => True
  | sprint _ => True 
  | hapi_code s => good_api_stmt aspc ispc s
  end.

Definition goodeval_h (aspc: fid -> option osapi) (ispc: hid -> option int_code) (c:cureval):=
  match c with
    | cure _ => True
    | curs s => goodstmt_h aspc ispc s
  end.

Fixpoint goodks_h (aspc: fid -> option osapi) (ispc: hid -> option int_code) ks:=
  match ks with
    | kint _ _ _ _ => False
    | kevent c ke ks' => goodeval_h aspc ispc c /\ goodks_h aspc ispc ks'
    | kstop => True
    | kcall _ s _ ks' => goodks_h aspc ispc ks' /\ goodstmt_h aspc ispc s
    | kseq s ks' => goodks_h aspc ispc ks' /\ goodstmt_h aspc ispc s
    | kassignr _ _ ks' => goodks_h aspc ispc ks'
    | kassignl _ _ ks' => goodks_h aspc ispc ks'
    | kfuneval _ _ _ _ ks' => goodks_h aspc ispc ks'
    | kif s1 s2 ks' => goodks_h aspc ispc ks' /\ goodstmt_h aspc ispc s1 /\ goodstmt_h aspc ispc s2
    | kwhile _ s ks' => goodks_h aspc ispc ks' /\ goodstmt_h aspc ispc s
    | kret ks' => goodks_h aspc ispc ks'
  end.

Definition goodcode_h (aspc: fid -> option osapi) (ispc: hid -> option int_code) (c:code):=
  match c with
  | (c, (ke, ks)) => goodeval_h aspc ispc c /\ goodks_h aspc ispc ks
  end.

Definition good_task_code (aspc: fid -> option osapi) (ispc: hid -> option int_code) (T: tasks) := 
  forall t c, get T t = Some c -> goodcode_h aspc ispc c.


Lemma GoodStmt_imp_goodstmt:
  forall s aspc ispc,
    GoodStmt_h s ->
    goodstmt_h aspc ispc s.
Proof.
  induction s; intros; simpl in *; auto.
  simpljoin.
  split.
  eapply IHs1; eauto.
  eapply IHs2; eauto.
  simpljoin.
  split.
  eapply IHs1; eauto.
  eapply IHs2; eauto.
  tryfalse.
Qed.

Lemma callcont_goodks:
  forall ks f s le ks' aspc ispc,
    callcont ks = Some (kcall f s le ks') ->
    goodks_h aspc ispc ks ->
    goodks_h aspc ispc ks'.
Proof.
  induction ks;intros;simpl in *;auto;tryfalse; simpljoin; auto;
    try (apply IHks with (aspc:=aspc) (ispc:=ispc) in H;auto; fail).
  inverts H;auto.
Qed.
               
Lemma init_good_tasks:
  forall cliprogs T O aspc ispc,
    init_tsk cliprogs T O ->
    good_client_code cliprogs ->
    good_task_code aspc ispc T.
Proof.
  introv Htsk Hgc.
  destruct Htsk as (Heqdom & Hgetex).
  unfolds in Hgc.
  unfold good_task_code.
  introv Hget.
  destruct c as (c & (ke & ks)).
  unfold goodcode_h.
  eapply Hgetex in Hget.
  destruct Hget as (s & f & d1 & d2 & tp & Heq & Hpu).
  inverts Heq.
  eapply Hgc in Hpu.
  simpl.
  split; auto.
  eapply GoodStmt_imp_goodstmt; eauto.
Qed.

Lemma good_task_estep_preserve:
  forall T t c ke ks m m' c' ke' aspc ispc,
    get T t = Some (c, (ke, ks)) ->
    good_task_code aspc ispc T ->
    estep c ke m c' ke' m' ->
    good_task_code aspc ispc (set T t (c', (ke', ks))).
Proof.
  introv Hget Htsk Hstep.
  lets Htsk': Htsk t (c, (ke, ks)) Hget.
  destruct Htsk' as (Heval &Hks).
  introv Hget'.
  destruct c0 as (c0 & (ke0 & ks0)).
  casetac t t0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  unfolds.
  split; auto.
  inverts Hstep; auto.
  rewrite set_a_get_a' in Hget'; auto.
  eapply Htsk; eauto.
Qed.

Lemma good_task_sstep_preserve:
  forall T t c ke ks m m' c' ks' p aspc ispc,
    get T t = Some (c, (ke, ks)) ->
    good_task_code aspc ispc T ->
    good_client_code p ->
    sstep p c ks m c' ks' m' ->
    good_task_code aspc ispc (set T t (c', (ke, ks'))).
Proof.
  introv Hget Htsk Hclt Hstep.
  lets Htsk': Htsk t (c, (ke, ks)) Hget.
  destruct Htsk' as (Heval &Hks).
  introv Hget'.
  destruct c0 as (c0 & (ke0 & ks0)).
  casetac t t0 Heq Hneq.
  {
    subst.
    rewrite set_a_get_a in Hget'.
    inverts Hget'.
    unfolds.
    inverts Hstep; simpl in Heval, Hks; simpljoin; simpl; split; auto.
    split; auto.
    eapply GoodStmt_imp_goodstmt; eauto.
    eapply callcont_goodks; eauto.
  }
  {
    rewrite set_a_get_a' in Hget'; auto.
    eapply Htsk; eauto.
  }
Qed.

Lemma good_task_cstep_preserve:
  forall T t C m m' C' p aspc ispc,
    get T t = Some C ->
    good_task_code aspc ispc T ->
    good_client_code p ->
    cstep p C m C' m' ->
    good_task_code aspc ispc (set T t C').
Proof.
  introv Hget Htsk Hclt Hstep.
  inverts Hstep.
  eapply good_task_estep_preserve; eauto.
  eapply good_task_sstep_preserve; eauto.
Qed.

Lemma good_api_stmt_spec_step_preserve:
  forall cd cd' O O' laust laust' sc aspc ispc,
    good_api_stmt aspc ispc cd ->
    spec_step sc cd O laust cd' O' laust' ->
    good_api_stmt aspc ispc cd'.
Proof.
  introv Hcd Hstep.
  destruct Hcd as [Hapi | [Hint | [Hend | Habt]]];
    [ | | simpljoin; inverts Hstep | subst; inverts Hstep].
  (* api_spec *)
  destruct Hapi as (fid & acode & ft & vl & Hapi & Hin).
  lets H__: succ_step_preserve Hin Hstep; eauto.
  unfolds.
  destruct H__ as [ | [ | ]]; eauto.
  left.
  repeat eexists; eauto.
  (* int_spec *)
  unfolds. 
  simpljoin.
  lets H__: succ_step_preserve x0 cd Hstep; eauto.
  destruct H__ as [Hsuc | [Habt | Hend]].
  -
    right; left. do 2 eexists; split; eauto.
  -
    subst. right; right; right. auto.
  -
    right; right; left.
    auto.  
Qed. 

Lemma good_task_hapistep_preserve:
  forall T p O t C C' O' laust laust' aspc ispc sc,
    get T t = Some C ->
    good_task_code aspc ispc T ->
    good_client_code p ->
    get O curtid = Some (oscurt t) ->
    hapistep (aspc, ispc, sc) C O laust C' O' laust' ->
    good_task_code aspc ispc (set T t C').
Proof.
  introv Hgetc Htsk Hclt Hgett Hstep.
  lets Htsk': Htsk t C Hgetc.
  destruct C as (c, (ke, ks)).
  destruct C' as (c', (ke', ks')).
  destruct Htsk' as (Heval &Hks).
  introv Hgetc'.
  destruct c0 as (c0 & (ke0 & ks0)).
  casetac t t0 Heq Hneq.
  2:{
    rewrite set_a_get_a' in Hgetc'; auto.
    eapply Htsk; eauto.
  }
  subst.
  rewrite set_a_get_a in Hgetc'.
  inverts Hgetc'.
  unfolds.
  inverts Hstep;
    repeat try (match goal with H: (_, _) = (_, _) |- _ => inverts H end);
    simpl in Heval, Hks; simpljoin; simpl; split; auto.
  (* hapienter_step *)
  unfolds.
  left.
  exists f r (tp,tl) (vl ++ vl').
  split; auto.
  constructors; auto.
  (* hidapi_step *)
  match goal with H: spec_step _ _ _ _ _ _ _ |- _ => rename H into Hstep end.
  simpl in Hstep.
  eapply good_api_stmt_spec_step_preserve; eauto.
Qed.

Lemma good_task_htstep_preserve:
  forall T p O t C cst C' cst' O' aust aust' aspc ispc sc,
    get T t = Some C ->
    good_task_code aspc ispc T ->
    good_client_code p ->
    get O curtid = Some (oscurt t) ->
    htstep (p, (aspc, ispc, sc)) t C cst O aust C' cst' O' aust' ->
    good_task_code aspc ispc (set T t C').
Proof.
  introv Hgetc Htsk Hclt Hgett Hstep.
  inverts Hstep; 
    try (match goal with H: (_, _) = (_, _) |- _ => inverts H end). 
  eapply good_task_cstep_preserve; eauto.
  eapply good_task_hapistep_preserve; eauto.
Qed.

Lemma hpstep_goodcode_h:
  forall pc T cst O T' cst' O' aust aust' aspc ispc,
    good_task_code aspc ispc T ->
    good_client_code pc ->
    hpstep_ok (pc, (aspc, ispc, GetHPrio)) T cst O aust T' cst' O' aust' ->
    good_task_code aspc ispc T'.
Proof.
  introv Hgt Hgc Hstep.
  inverts Hstep.
  match goal with H: hpstep _ _ _ _ _ _ _ _ _ |- _ => rename H into Hstep end.
  inverts Hstep.
  - (* htstep *)
    eapply good_task_htstep_preserve; eauto.
  - (* htistep *)
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
    inverts H4.
    unfolds.
    introv Hg.
    unfolds in Hgt.
    casetac t t0 Ht Hf.
    + subst. rewrite set_a_get_a in Hg. inverts Hg.
      unfolds.
      lets H__: Hgt H2; eauto.
      split.
      *
        unfolds. unfolds. unfolds.
        right; left. exists i l0.
        split; eauto. constructors; auto.
      * simpl. simpl in H__. auto.
    + rewrite set_a_get_a' in Hg; eauto.
  - (* hswi_step *)
    match goal with H: nabt _  |- _ => rename H into Hnabt end.
    match goal with H: get T _ = _  |- _ => rename H into Hgetc end.
    match goal with H: get _ curtid = _  |- _ => rename H into Hgett end.
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
    lets Hgt': Hgt Hgetc; eauto. 
    destruct Hgt' as (Heval & Hks).
    introv Hgetc'.
    destruct c as (c0 & (ke0 & ks0)).
    casetac t t0 Heq Hneq.
    2:{
      rewrite set_a_get_a' in Hgetc'; eauto.
    }
    subst.
    rewrite set_a_get_a in Hgetc'.
    inverts Hgetc'.
    simpl in Heval.
    simpl.
    split; eauto. 
    destruct Heval as [Hapi | [Hint | [Hend | Habt]]];
      [ | | simpljoin; tryfalse | tryfalse ].
    {
      destruct Hapi as (fid & acode & ft & vl & Hapi & Hin).
      eapply succ_step_preserve with (cd':=s) in Hin; eauto.
      2:{
        eapply spec_seq_step_end; eauto. 
        eapply spec_sched_step with (O:= set O curtid (oscurt t')) (t:= t'); eauto. 
        rewrite set_a_get_a; eauto.
        instantiate (1:=GetHPrio).
        unfold GetHPrio in *.
        simpljoin. 
        rewrite set_a_get_a'; eauto. 
        repeat eexists; eauto.
        introv Hf; tryfalse.
        eapply map_join_emp; eauto. 
      }
      unfolds.
      destruct Hin as [ | [ | ]]; eauto.
      left; repeat eexists; eauto.
    }
    {
      unfolds. right; left.
      simpljoin.
      do 2 eexists.
      split; eauto.
      unfold has_succ in *.
      destruct H0.
      -
        subst.
        right. constructors; eauto.
      -
        right.
        eapply succ_seq_cd2; eauto.
    }

    Unshelve.
    exact {| tskpt := PtNormal |}. 
Qed. 

Lemma hpstepstar_goodcode_h:
  forall pc T cst O T' cst' O' aust aust' aspc ispc,
    hpstepokstar (pc, (aspc, ispc, GetHPrio)) T cst O aust T' cst' O' aust' ->
    good_task_code aspc ispc T ->
    good_client_code pc ->
    good_task_code aspc ispc T'.
Proof.
  introv Hstep.
  inductions Hstep; intros.
  auto.
  eapply IHHstep; eauto.
  eapply hpstep_goodcode_h; eauto.
Qed.

Lemma reachable_good_tasks:
  forall cliprogs T cst O aust aspc ispc ini_st,
    good_client_code cliprogs ->
    reachable (cliprogs, (aspc, ispc, GetHPrio)) ini_st T cst O aust -> 
    good_task_code aspc ispc T.
Proof.
  introv Hgc Hr.
  destruct Hr as (pu & spc & Heq & Hr).
  inverts Heq.
  destruct Hr as (T0 & cst0 & O0 & aust0 & Hit & His & Hstep).
  lets Hgt: init_good_tasks Hit Hgc.
  eapply hpstepstar_goodcode_h; eauto.
Qed.

