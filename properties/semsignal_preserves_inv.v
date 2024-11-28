
Require Import memory.
Require Import anno_language.
Require Import anno_opsem.
Require Import aux_notations. 

Require Import succ_gen.

Require Import common_defs.

Require Import init.
Require Import sema_invs.
Require Import sem_sys.

Require Import join_lib.
Require Import seplog_lemmas.

Require Import aux_tacs. 
Require Import aux_lemmas.
Require Import sema_lemmas.

Require Import math_auto.

Require Import sema_assms.

Require Import protect. 

Set Keyed Unification. 


Lemma sem_post_exwt_succ_cond_ge_preserve:
  forall O els eid ni ns1 na1 ns0 na0 wl gau n t, 
    cond_pv1 gau els ->
    get O absecblsid = Some (absecblist els) -> 
    get els eid = Some (abssem n, wl) ->
    get gau eid = Some {| ninit := ni; nsig1 := ns1; nacq1 := na1; nsig0 := ns0; nacq0 := na0 |} -> 
    cond_pv1
      (set gau eid {| ninit := ni; nsig1 := ns1; nacq1 := na1; nsig0 := S ns0; nacq0 := na0 |}) 
      (set els eid (abssem n, remove_tid t wl)).  
Proof.
  introv Hcge Hgels Hgsem Hgau.
  match goal with
    H: cond_pv1 ?gau ?els |- cond_pv1 ?gau'_ ?els'_ => 
      eapply cond_ge_preserve0 with (gau:=gau) (els:=els) (gau':=gau'_) (els':=els'_); eauto 
  end.
  - 
    introv Hget.
    casetac eid eid0 Ht Hf.
    + subst. rewrite set_a_get_a in Hget. inverts Hget.
      eexists; eauto.  
    + rewrite set_a_get_a' in Hget; eauto.
  -
    introv Hga.
    casetac eid eid0 Ht Hf.
    +
      subst. rewrite set_a_get_a.
      eexists. split. eauto. 
      rewrite Hgau in Hga. inverts Hga.
      simpl.
      splits; auto.
    +
      rewrite set_a_get_a'; eauto.
Qed.               

Lemma gethwait_in:
  forall x ws t, 
    GetHWait x ws t -> In t ws. 
Proof.
  intros.
  unfolds in H.
  simpljoin.
  auto.  
Qed.   

Lemma join_sig_get_r_res: 
  forall a t (tls tls': TcbMod.map) p st, 
    join (sig a (p, st)) tls' tls ->
    t <> a ->
    get tls' t = get tls t.
Proof.
  intros.
  destruct (get tls t) eqn: E.
  - eapply join_get_or in E; eauto.
    destruct E as [Hf | Ht].
    + rewrite get_a_sig_a' in Hf. false.
      auto.
    + auto. 
  - eapply join_get_none_rev2; eauto. 
Qed.

Lemma sem_post_exwt_succ_n_wait_rdy_eq_S: 
  forall ts tls t p eid0 laump lau, 
    get tls t = Some (p, wait eid0) -> 
    get laump t = Some lau ->
    tskpt lau = PtPend (Vptr eid0) -> 
    atids_valid tls ts -> 
    n_wait_rdy eid0 ts (set tls t (p, rdy)) laump =
      S (n_wait_rdy eid0 ts tls laump). 
Proof.
  induction ts.
  -
    introv Hgtls Hgl Htl Hav.
    unfolds in Hav.
    destruct Hav as (_ & Ha).
    specialize (Ha t).
    unfolds in Ha.
    destruct Ha as (Hf & _).
    false. eapply in_nil. eapply Hf.
    introv Hnone.
    rewrite Hnone in Hgtls.
    false. 
  -
    introv Hgtls Hgl Htl Hav.
    lets Hdc: atids_valid_decomp Hav; eauto.
    destruct Hdc as (p_ & st_ & Hgtls_ & Hex).
    destruct Hex as (tls' & Hjo & Hav').
    do 2 rewrite n_wait_rdy_prop. 
    rewrite Hgtls_.
    assert (Hne: forall t, In t ts -> t <> a).
    {
      unfolds in Hav.
      destruct Hav as (Hds & Hav).
      lets Hf_: distinct_in_contr Hds; eauto.
      introv Hin.
      introv Heq. subst. false.                     
    }
    casetac t a Ht Hf.
    + subst. 
      rewrite set_a_get_a.
      rewrite Hgl.
      destruct st_ eqn: Est_.
      {
        rewrite Hgtls in Hgtls_.
        inverts Hgtls_.
      }
      {
        destruct lau eqn: Elau.
        simpl in Htl. subst tskpt.
        rewrite Hgtls in Hgtls_.
        inverts Hgtls_.
        rewrite beq_tid_true.
        apply eq_S.
        assert (Haeq': forall t, In t ts -> get (set tls a (p_, rdy)) t = get tls t).
        {
          introv Hin.
          eapply Hne in Hin; eauto.
          rewrite set_a_get_a'; eauto.
        }
        eapply n_wait_rdy_change_tls; eauto.
        {
          introv Hin. eapply Hne in Hin; eauto.
          rewrite set_a_get_a'; eauto. 
        }
      }
    +
      assert (Hg': get tls' t = Some (p, wait eid0)).
      {
        match goal with
          Hgtls: get tls t = Some ?e, Hjo: join ?tls0 tls' tls |- get tls' t = Some ?e' => 
            assert (Hor: get tls0 t = Some e \/ get tls' t = Some e)
        end.
        eapply join_get_or; eauto.
        destruct Hor as [Hgll | Hgrr].
        -  rewrite get_a_sig_a' in Hgll; eauto.
           false.
        - auto.
      }                  
      assert (Hrw1:
               n_wait_rdy eid0 ts (set tls t (p, rdy)) laump =
                 n_wait_rdy eid0 ts (set tls' t (p, rdy)) laump).
      {
        eapply n_wait_rdy_change_tls; eauto.
        {
          introv Hin.
          casetac t t0 Ht_ Hf_.
          - subst. do 2 rewrite set_a_get_a. auto.
          - do 2 (rewrite set_a_get_a'; eauto).  
            eapply Hne in Hin; eauto.
            eapply join_sig_get_r_res; eauto. 
        }                    
      }
      rewrite Hrw1.
      assert (Hrw2: n_wait_rdy eid0 ts tls laump = n_wait_rdy eid0 ts tls' laump).
      {
        eapply n_wait_rdy_change_tls; eauto.
        introv Hin.
        eapply Hne in Hin; eauto.
        eapply join_sig_get_r_res; eauto. 
      }
      rewrite Hrw2.
      
      rewrite set_a_get_a'; eauto.
      rewrite Hgtls_.
      destruct st_ eqn: Est_.
      destruct (get laump a) eqn: Egl.
      destruct l.
      destruct tskpt. 
      destruct vp eqn: Evp.
      {
        eapply IHts; eauto.
      }
      {
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto. 
      }
      destruct (beq_tid eid0 a0) eqn: Ebeq.
      {
        apply eq_S. 
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto.  
      }
      {
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto. 
      }
      
Qed. 

Lemma sem_post_exwt_succ_cond_aux_preserve: 
  forall O (els: EcbMod.map) (tls: TcbMod.map) ts gau laump n (p: priority) 
         t wl ni ns1 na1 ns0 na0 (st: taskstatus) eid, 
    cond_pv0 els tls ts gau laump ->
    get O abstcblsid = Some (abstcblist tls) ->
    get O absecblsid = Some (absecblist els) -> 
    wait_progpt els laump -> 
    get els eid = Some (abssem n, wl) -> 
    get tls t = Some (p, st) ->
    GetHWait tls wl t -> 
    get gau eid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0|} -> 
    atids_valid tls ts -> 
    cond_pv0
      (set els eid (abssem n, remove_tid t wl))
      (set tls t (p, rdy))
      ts
      (set gau eid {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=S ns0; nacq0:=na0 |})
      laump. 
Proof.
  introv Hca Hgtls Hgels Hwp Hge Hgt Hgw Hgg Hav.
  unfold cond_pv0 in *.
  introv Hge_.
  lets Hinwl: gethwait_in Hgw; eauto.          
  lets H0_: sem_tst_est_ Hgtls Hgels; eauto.
  specializes H0_; eauto.
  destruct H0_ as (p_ & Hg).
  rewrite Hg in Hgt. 
  inverts Hgt.
  
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hge_.
    inverts Hge_.
    lets Heq: Hca Hge; eauto.
    destruct Heq as (ga & Hgga & Heq).
    rewrite Hgg in Hgga. inverts Hgga.
    simpl in Heq.
    rewrite set_a_get_a.
    eexists.
    split; eauto.
    simpl.        
    unfolds in Hwp.
    lets Hpt: Hwp Hge Hinwl; eauto.
    simpljoin. 
    erewrite sem_post_exwt_succ_n_wait_rdy_eq_S; eauto.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hge_; eauto.
    lets H__: Hca Hge_; eauto.
    destruct H__ as (ga_ & Hgg_ & Heq_).
    eexists.
    split; eauto.
    unfolds in Hwp.
    apply gethwait_in in Hgw.
    lets Hpt: Hwp Hge Hgw; eauto.
    destruct Hpt as (lau_ & Hgl_ & Hpt_).
    match goal with
      Heq_: _ = (_ + ?e1)%nat |- _ = (_ + ?e2)%nat =>
        assert (e1 = e2)
    end.
    {
      eapply n_wait_rdy_lem; eauto.
      introv Hin0.
      casetac t t0 Htt Hff.
      - subst. rewrite set_a_get_a.
        rewrite Hg.
        rewrite Hgl_.
        destruct lau_ eqn: El_.
        simpl in Hpt_. subst tskpt.
        destruct (beq_tid eid0 eid) eqn: E'.
        eapply beq_tid_true_eq in E'; eauto; subst.
        auto. 
      - rewrite set_a_get_a'; eauto. 
    }
    congruence. 

Qed. 

Lemma sem_post_exwt_succ_wait_progpt_preserve:
  forall els eid n wl laump t, 
    get els eid = Some (abssem n, wl) -> 
    wait_progpt els laump ->
    wait_progpt (set els eid (abssem n, remove_tid t wl)) laump. 
Proof.
  introv Hge Hwp.
  unfold wait_progpt in *.
  introv Hg Hin.
  casetac eid eid0 Ht Hf.
  - subst. rewrite set_a_get_a in Hg.
    inverts Hg.
    lets H__: Hwp Hge; eauto.
    eapply in_remove_tid in Hin; eauto.
  - rewrite set_a_get_a' in Hg; eauto.
Qed.             

Lemma dtinv_sem_post_exwt_succ_preserve:
  forall v1 v2 v' O0 O0' Of O O' laump, 
    sem_post_ex_wt_succ (v1 :: v2 :: nil) O0 (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dtinv O laump ->
    dtinv O' laump.
Proof.
  introv Hsp Hjo Hjo' Hdti.
  inverts Hsp.
  simpljoin.
  inv_some.
  inv_lst.
  unfolds.
  unfolds in Hdti.
  simpljoin.
  kvext O0 abstcblsid O.
  l_rew21 (get O abstcblsid).
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  kvext_h Hjo' abstcblsid O'.
  kvext_h Hjo' absecblsid O'.
  kvext_h Hjo' gauxstid O'.
  assert (get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew21 (get O atidlsid).
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  splits.
  - (* atids_valid *) 
    eapply atids_valid_set_tcb_preserve; eauto.
  - (* cond_pv1 *)
    eapply sem_post_exwt_succ_cond_ge_preserve; eauto.
  - (* cond_pv0 *)             
    eapply sem_post_exwt_succ_cond_aux_preserve; eauto. 
  - (* wait_progpt *)            
    eapply sem_post_exwt_succ_wait_progpt_preserve; eauto.
  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex.
    casetac x16 eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false.
      apply Hnex. do 2 eexists; eauto.
    + introv Hg.
      rewrite set_a_get_a' in Hnex; eauto.
Qed.

Lemma cond_ge_sem_post_succ_put_preserve:
  forall gau els eid ni ns1 na1 ns0 na0 n wl, 
    get gau eid = Some {| ninit := ni; nsig1 := ns1; nacq1 := na1; nsig0 := ns0; nacq0 := na0 |} ->
    get els eid = Some (abssem n, wl) -> 
    Int.ltu n ($ 65535) = true -> 
    cond_pv1 gau els ->
    cond_pv1
      (set gau eid {| ninit := ni; nsig1 := S ns1; nacq1 := na1; nsig0 := ns0; nacq0 := na0 |})
      (set els eid (abssem (n +ᵢ  Int.one), wl)).
Proof.
  introv Hgg Hge Hlt Hcg.
  unfold cond_pv1 in *.
  lets H__: Hcg Hge; eauto.
  simpljoin.
  introv Hg.
  casetac eid eid0 Ht Hf.
  -
    subst. rewrite set_a_get_a in Hg. inverts Hg.
    split; auto.
    clear -Hlt.
    int auto.
    int auto.
    rewrite set_a_get_a. 
    eexists.
    split; eauto.
    simpl ninit. simpl nsig1. simpl nacq1.
    rewrite Nat2Z.inj_succ.
    rewrite H0 in Hgg.
    inverts Hgg.
    simpl in H1.
    int auto.
    int auto. 
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hg; eauto.
Qed.

Lemma dtinv_sem_post_put_succ_preserve:
  forall v1 v2 v' O0 O0' Of O O' laump, 
    sem_post_inc_succ (v1 :: v2 :: nil) O0 (v', Some O0') ->   
    join O0 Of O ->
    join O0' Of O' ->
    dtinv O laump ->
    dtinv O' laump.
Proof. 
  introv Hsp Hjo Hjo' Hdti.
  inverts Hsp.
  simpljoin.
  rem_dis.
  inv_some.
  inv_lst.
  unfold dtinv in *.
  simpljoin.
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  kvext_h Hjo' absecblsid O'.
  kvext_h Hjo' gauxstid O'.
  assert (Hgaeq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew21 (get O atidlsid).
  assert (Hgteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew21 (get O abstcblsid).
  do 4 eexists.
  split; eauto.
  split; eauto. 
  split; eauto.
  split; eauto.
  splits.
  - (* atids_valid *)
    auto.
    
  - (* cond_pv1 *)
    eapply cond_ge_sem_post_succ_put_preserve; eauto. 
    
  - (* cond_pv0 *)
    eapply cond_aux_same_laust_preserve; eauto. 

  - (* wait_progpt *)
    eapply wait_progpt_same_laust_preserve; eauto.

  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex.
    casetac x eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false.
      apply Hnex. do 2 eexists; eauto.
    + rewrite set_a_get_a' in Hnex; eauto. 

Qed. 


Set Keyed Unification. 

(* Ltac invstep1 :=  *)
(*   match goal with H: context [spec_step], H': context [spec_step] |- _ => inverts H end. *)

Ltac solve_endabt :=
  simpljoin; solve
               [ tryfalse
               | false;
                 match goal with
                   H: ~(exists _, END _ = END _) |- _ => apply H; eexists; eauto 
                 | H: ABORT <> ABORT |- _ => apply H; auto
                 end]. 

Set Printing Depth 1000.

Ltac solve_steq :=
  match goal with
    H: ~(_ /\ _ /\ _ /\ _ /\ _) |- _ => false; apply H; auto 
  end.

Ltac some_none_tac Hs :=
  match Hs with
    (pnil, ?hyp) => 
      match type of hyp with
        ?P /\ ?Q => let h1 := fresh "h" in let h2 := fresh "h" in destruct hyp as (h1 & h2); some_none_tac pnil
      | ?P \/ ?Q =>
          let h1 := fresh "h" in
          let h2 := fresh "h" in
          destruct hyp as [h1 | h2];
          [some_none_tac (pnil, h1) | some_none_tac (pnil, h2)]
      | Some _ = None => solve [false]
      (* | Some _ = Some _ => inverts hyp *)
      | _ => idtac
      end
  | pnil =>
      match goal with
        h: context [Some ?t1 = None] |- _ => some_none_tac (pnil, h)
      | h: context [Some ?t1 = Some ?t2] |- _ => some_none_tac (pnil, h) 
      | h: _ |- _ => idtac
      end
  end.
  
Ltac end_abt H tac := 
  match type of H with
    ?P /\ ?Q => let h1 := fresh in let h2 := fresh in destruct H as (h1 & h2); first [tac h1 | tac h2]
  | ?P \/ ?Q => let h1 := fresh in let h2 := fresh in destruct H as [h1 | h2]; [tac h1 | tac h2]
  | ABORT <> ABORT => solve [false]
  | ~exists vo, END ?vo_ = END vo => solve [false; apply H; eexists; eauto]
  end. 
       
Ltac end_abt_tac H := 
  match type of H with
    context [ABORT <> ABORT] => end_abt H end_abt_tac
  | context [~exists vo, END ?vo1 = END vo] => end_abt H end_abt_tac
  end.

Ltac symexe0 :=
  (* let symexe0 := idtac in  *)
  match goal with
    H: has_succ0 _ _ |- _ =>
      inverts H;
      try (
          match goal with
            H_: has_succ0 _ _ |- _ =>
              protect H_;
              try (match goal with
                     H__: spec_step _ _ _ _ _ _ _ |- _ => protect H__
                   end)
          end); symexe0
  | H: spec_step _ (spec_atm _) _ _ _ _ _ |- _ => idtac
  | H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; symexe0
  | H: context[ABORT <> ABORT] |- _ => end_abt_tac H
  | H: context[~exists vo, END ?vo1 = END vo] |- _ => end_abt_tac H
  | H: sem_post_ex_wt_succ _ _ (_, Some _) |- _ => idtac 
  | H: sem_post_inc_succ _ _ (_, Some _) |- _ => idtac
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; tryfalse; some_none_tac pnil; symexe0
  | H: ~(get ?O _ = get ?O _ /\ _ /\ _ /\ _ /\ ?lau = ?lau) |- _ => false; apply H; splits; auto; symexe0
  | H: _ :: _ = _ :: _ |- _ => inverts H; symexe0
  | H: Some _ = Some _ |- _ => inverts H; symexe0
  | H: join ?O0 ?Of ?O, H': join ?O0 ?Of ?O' |- _ =>
      assert (O = O') by (join auto); subst; symexe0  
  | _ => idtac
  end.

Ltac symexe :=
  match goal with
    H1: ProtectWrapper _, H2: ProtectWrapper _ |- _ =>
      unprotect H1; unprotect H2;
      symexe0
  | _ => symexe0
  end.

Ltac desvl0 vl :=
  match goal with
    Hhs: context[has_succ], Hsp: context[spec_step] |- _ => 
      destruct vl;
      [ simpl in Hhs; 
        lets Heq: abt_succs_contra Hhs; eauto; subst; 
        inverts Hsp | idtac ]
  end. 

Ltac des_vl :=
  match goal with
    vl: vallist |- _ => desvl0 vl
  | vl: list val |- _ => desvl0 vl
  end. 

Lemma sem_signal_preserves_inv_: 
  forall vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map),
    has_succ (semsignal vl) cd -> 
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau') -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hhs Hhsat Hstep Hneq Hct Hlau Hlau' Hsatinv.
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_succs_contra in Hhs; eauto. subst. inverts Hstep. }

  inverts Hhs.
  inverts Hstep; 
    (rewrite get_set_same in Hlau'; subst; auto; fail).
  
  repeat symexe.

  {
    rewrite get_set_same in Hlau'; auto. subst.
    eapply dtinv_sem_post_exwt_succ_preserve; eauto.
  }

  {
    rewrite get_set_same in Hlau'; auto. subst.
    eapply dtinv_sem_post_put_succ_preserve; eauto.
  }

Qed.

(* each step of the V operation preserves the global invariant
     on abstract states *) 
Lemma sem_signal_preserves_inv: 
  forall vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map),
    has_succ (semsignal vl) cd -> 
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hct Hlau Hlau' Hsatinv.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_signal_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto.   
Qed.

