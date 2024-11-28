
Require Import memory.
Require Import anno_language.
Require Import succ_gen.
Require Import init.
Require Import sema_invs.
Require Import sem_sys.

Require Import join_lib.
Require Import seplog_lemmas.
Require Import aux_tacs.

Require Import common_defs. 

Require Import aux_lemmas. 
Require Import sema_lemmas.
Require Import sema_assms.

Require Import math_auto.


Set Keyed Unification. 

Lemma cond_ge_pend_mone_preserve:
  forall els eid gaump x3 x4 x5 x6 x7 x8 x9,
    get els eid = Some (abssem x3, x4) ->
    Int.ltu Int.zero x3 = true -> 
    get gaump eid = Some {| ninit := x5; nsig1 := x6; nacq1 := x7; nsig0 := x8; nacq0 := x9 |} ->
    cond_pv1 gaump els ->
    cond_pv1
      (set gaump eid {| ninit := x5; nsig1 := x6; nacq1 := S x7; nsig0 := x8; nacq0 := x9 |}) 
      (set els eid (abssem (x3 -ᵢ Int.one), x4)).
Proof.
  introv Hge Hltu Hgg Hcg.
  unfolds in Hcg.
  unfolds.
  introv Hget'. 
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hget'. inverts Hget'.
    rewrite set_a_get_a.
    lets H__: Hcg Hge.
    simpljoin.
    split.
    int auto. int auto.
    eexists.
    split; eauto.
    simpl nacq1. simpl nsig1. simpl ninit.
    l_rew21 (get gaump eid0).
    simpl in H1.
    rewrite Nat2Z.inj_succ.
    int auto.
    int auto.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hget'; eauto.
Qed.         

Lemma dtinv_sem_pend_inst_get_succ_preserve:
  forall v1 v3 v' O0 O0' Of O O' laump, 
    sem_pend_inst_get_succ (v1 :: v3 :: nil) O0 (v', Some O0') ->
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
  unfolds.
  unfolds in Hdti.
  simpljoin.
  match goal with
    H1: join O0 Of O, H2: join _ Of O' |- _ =>
      rename H1 into Hjo; rename H2 into Hjo'
  end.
  assert (Hgtcbeq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l abstcblsid Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  rewrite <- Hgtcbeq.
  assert (Hgtseq: get O atidlsid = get O' atidlsid). 
  {
    lets H__: join_get_same_l atidlsid Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  rewrite <- Hgtseq.
  kvext_h Hjo' absecblsid O'.
  kvext_h Hjo' gauxstid O'.
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  splits.
  -
    (* atids_valid *)
    auto.
  -
    (* cond_pv1 *)
    eapply cond_ge_pend_mone_preserve; eauto. 
  -
    (* cond_pv0 *)
    eapply cond_aux_same_laust_preserve; eauto.    
  -
    (* wait_progpt *)
    eapply wait_progpt_same_laust_preserve; eauto.
  -
    (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex.
    casetac x eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false. apply Hnex. do 2 eexists; eauto.
    + rewrite set_a_get_a' in Hnex; eauto.
Qed.


Lemma cond_ge_pend_block_preserve:
  forall els eid wl gau t, 
    get els eid = Some (abssem Int.zero, wl) ->
    cond_pv1 gau els ->
    cond_pv1 gau (set els eid (abssem Int.zero, t::wl)). 
Proof.
  introv Hgeid Hcge.
  lets H__: cond_ge_preserve0 gau gau els (set els eid (abssem Int.zero, t :: wl)); eauto. 
  specializes H__; eauto.
  introv Hget.
  casetac eid eid0 Ht Hf.
  - subst. rewrite set_a_get_a in Hget.
    inverts Hget.
    eexists; eauto.
  - rewrite set_a_get_a' in Hget; eauto.
Qed. 

Lemma sem_pend_block_n_wait_rdy_eq_: 
  forall ts tls laump p t eid, 
    get laump t = Some {| tskpt := PtNormal |} -> 
    n_wait_rdy eid ts tls laump = 
      n_wait_rdy eid ts
        (set tls t (p, wait eid))
        (set laump t {| tskpt := PtPend (Vptr eid) |}). 
Proof.
  introv Hnml.
  eapply n_wait_rdy_lem; eauto.
  introv Hin0.
  casetac t t0 Hee Hne.
  - subst.
    rewrite set_a_get_a.
    rewrite Hnml.
    destruct (get tls t0).
    + destruct p0; auto. destruct t; auto. 
    + auto.
  - do 2 (rewrite set_a_get_a'; eauto).
Qed.

Lemma sem_pend_block_n_wait_rdy_eq: 
  forall ts tls laump p t eid eid', 
    get laump t = Some {| tskpt := PtNormal |} -> 
    n_wait_rdy eid ts tls laump = 
      n_wait_rdy eid ts
        (set tls t (p, wait eid'))
        (set laump t {| tskpt := PtPend (Vptr eid') |}).
Proof.
  introv Hgl.
  casetac eid eid' Ht Hf.
  - subst.
    eapply sem_pend_block_n_wait_rdy_eq_; eauto.
  -
    eapply n_wait_rdy_lem; eauto.
    introv Hin.
    casetac t t0 Htt Hff.
    + subst. rewrite set_a_get_a.
      rewrite Hgl.
      destruct (get tls t0) eqn: E.
      destruct p0. 
      destruct t; auto.
      auto.
    + rewrite set_a_get_a'; eauto.
      rewrite set_a_get_a'; eauto. 
Qed.

Lemma wait_progpt_sempend_block_preserve: 
  forall els eid n wl laump t, 
    get laump t= Some {| tskpt := PtNormal |} -> 
    get els eid = Some (abssem n, wl) ->
    wait_progpt els laump ->
    wait_progpt (set els eid (abssem n, t::wl)) (set laump t {| tskpt := PtPend (Vptr eid) |}).
Proof.
  introv Hnml Hge Hwp.
  unfold wait_progpt in *.
  introv Hg Hin.
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hg. inverts Hg.
    simpl in Hin.
    inverts Hin.
    + 
      rewrite set_a_get_a.
      eexists. split; eauto.
    +
      specializes Hwp; eauto. 
      casetac t0 t Hee Hne.
      * subst. rewrite set_a_get_a. eexists; split; eauto.
      * rewrite set_a_get_a'; eauto.
  -
    rewrite set_a_get_a' in Hg; eauto.
    lets H_: Hwp Hg Hin; eauto.
    destruct H_ as (lau & Hgl & Htl).
    casetac t t0 Hee Hne.
    + subst.
      rewrite Hnml in Hgl.
      rewrite set_a_get_a. eexists; split; eauto. inverts Hgl.
      simpl in Htl. inverts Htl.
    + rewrite set_a_get_a'; eauto. 
Qed. 

Lemma dtinv_sem_pend_block_preserve:
  forall v1 v3 v' O0 O0' t Of O O' laump laump', 
    sem_pend_block (v1 :: v3 :: nil) O0 (v', Some O0') ->
    (exists eid, v1 = Vptr eid) -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some {| tskpt := PtNormal |} ->
    laump' = set laump t {| tskpt := PtPend v1 |} ->
    join O0 Of O ->
    join O0' Of O' -> 
    dtinv O laump -> 
    dtinv O' laump'. 
Proof.
  introv Hsp Hptr Hgct Hglau Hlau' Hjo Hjo' Hdti.
  unfold dtinv in *.
  simpljoin.
  inverts Hsp.
  simpljoin.
  inv_lst.
  inv_some.
  kvext O0 curtid O. 
  l_rew21 (get O curtid).
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  kvext O0 abstcblsid O.
  l_rew21 (get O abstcblsid).
  kvext_h Hjo' abstcblsid O'.
  kvext_h Hjo' absecblsid O'.
  assert (Hgaeq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21 (get O atidlsid).
  assert (Hgxeq: get O gauxstid = get O' gauxstid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.        
  }
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
    eapply cond_ge_pend_block_preserve; eauto.

  - (* cond_pv0 *)
    unfold cond_pv0 in *.
    introv Hgsem.
    match goal with
      H: get ?x ?y = Some (abssem _, _) |- _ =>
        rename x into els; rename y into eid_
    end.
    casetac eid_ eid Ht Hf.
    + subst. rewrite set_a_get_a in Hgsem.
      inverts Hgsem.
      specializes H6; eauto.
      simpljoin.
      eexists.
      splits.
      * 
        eauto.
      *
        match goal with
          H: context [n_wait_rdy eid ?e1 ?e2 ?e3] |- _ = (_ + ?e)%nat =>
            assert (Heq: n_wait_rdy eid e1 e2 e3 = e); 
            rename e1 into ts_; rename e2 into tls_ 
        end.
        eapply sem_pend_block_n_wait_rdy_eq; eauto. 
        rewrite <- Heq.
        auto. 
    +
      rewrite set_a_get_a' in Hgsem; eauto. 
      specializes H6; eauto.
      simpljoin.
      eexists.
      split; eauto. 
      match goal with
        H: context [n_wait_rdy eid ?e1 ?e2 ?e3] |- _ = (_ + ?e)%nat =>
          assert (Heq: n_wait_rdy eid e1 e2 e3 = e); 
          rename e1 into ts_; rename e2 into tls_ 
      end.
      eapply sem_pend_block_n_wait_rdy_eq; eauto. 
      rewrite <- Heq.
      auto.
      
  - (* wait_progpt *)    
    eapply wait_progpt_sempend_block_preserve; eauto. 

  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex.
    casetac x4 eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false. apply Hnex. do 2 eexists; eauto.
    + rewrite set_a_get_a' in Hnex; eauto.    
      introv Hin_.
      casetac t t0 Ht_ Hf_.
      * subst. rewrite set_a_get_a. introv Hne. apply Hf.
        inverts Hne. auto.
      * rewrite set_a_get_a'; eauto.
        
Qed. 

Lemma cond_ge_pend_to_preserve:
  forall n els eid wl gau t, 
    get els eid = Some (abssem n, wl) ->
    cond_pv1 gau els ->
    cond_pv1 gau (set els eid (abssem n, remove_tid t wl)). 
Proof.
  introv Hgeid Hcge.
  lets H__: cond_ge_preserve0 gau gau els (set els eid (abssem n, remove_tid t wl)); eauto.    
  eapply H__; eauto.
  introv Hg.
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hg.
    inverts Hg.
    eexists; eauto.
  - rewrite set_a_get_a' in Hg; eauto.
Qed.            

Lemma wait_progpt_sempend_to_preserve: 
  forall els eid n wl laump t O,
    get O absecblsid = Some (absecblist els) -> 
    get els eid = Some (abssem n, wl) ->
    In t wl -> 
    get laump t = Some {| tskpt := PtPend (Vptr eid) |} -> 
    wait_progpt els laump ->
    wait_progpt
      (set els eid (abssem n, remove_tid t wl))
      (set laump t {| tskpt := PtNormal |}).
Proof.
  introv Hgels Hge Hin Hgl Hwp.
  unfold wait_progpt in *.
  introv Hge0 Hinwl.
  casetac eid eid0 Ht Hf.
  - 
    subst.
    rewrite set_a_get_a in Hge0.
    inverts Hge0.
    casetac t0 t Htt Hff.
    +
      subst.
      apply in_remove_tid_false in Hinwl.
      false.
    +
      rewrite set_a_get_a'; eauto. 
      lets H__: in_remove_tid Hinwl; eauto.
  -
    rewrite set_a_get_a' in Hge0; eauto.
    casetac t0 t Htt Hff.
    +
      subst.
      lets H__: no_multiple_wait Hgels Hge Hge0; eauto.
      specializes H__; eauto.
      false.
    +
      rewrite set_a_get_a'; eauto. 
Qed. 

Lemma sempend_to_n_wait_rdy_eq_:
  forall ts tls laump eid t p,
    get tls t = Some (p, wait eid) ->  
    n_wait_rdy eid ts tls laump =
      n_wait_rdy eid ts (set tls t (p, rdy)) (set laump t {| tskpt := PtNormal |}). 
Proof.
  introv Hgtls.
  eapply n_wait_rdy_lem; eauto.
  introv Hin.
  casetac t t0 Ht Hf.
  - subst.
    do 2 rewrite set_a_get_a.
    rewrite Hgtls. auto.
  -
    do 2 (rewrite set_a_get_a'; eauto).
Qed.

Lemma sempend_to_n_wait_rdy_eq:
  forall ts tls laump eid t p eid',
    get tls t = Some (p, wait eid) -> 
    n_wait_rdy eid' ts tls laump =
      n_wait_rdy eid' ts (set tls t (p, rdy)) (set laump t {| tskpt := PtNormal |}). 
Proof.
  introv Hgt.
  casetac eid' eid Ht Hf.
  - subst.
    eapply sempend_to_n_wait_rdy_eq_; eauto.
  -
    eapply n_wait_rdy_lem; eauto.
    introv Hin.
    casetac t t0 Ht_ Hf_.
    + subst.
      repeat rewrite set_a_get_a. 
      rewrite Hgt.
      auto.
    + do 2 (rewrite set_a_get_a'; eauto).
Qed. 

Lemma cond_aux_sempend_to_preserve: 
  forall els tls ts gau laump n wl t p eid, 
    cond_pv0 els tls ts gau laump ->
    get els eid = Some (abssem n, wl) ->
    get tls t = Some (p, wait eid) -> 
    cond_pv0
      (set els eid (abssem n, remove_tid t wl))
      (set tls t (p, rdy))
      ts gau 
      (set laump t {| tskpt := PtNormal |}).
Proof.
  introv Hcau Hgel Hgtl.
  unfold cond_pv0 in *.
  introv Hge.
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hge.
    inverts Hge.
    specializes Hcau; eauto.
    simpljoin. 
    eexists.
    split; eauto.

    lets Heq_: sempend_to_n_wait_rdy_eq ts laump Hgtl; eauto.
    erewrite <- Heq_.
    auto. 

  - rewrite set_a_get_a' in Hge; eauto.
    specializes Hcau; eauto.
    simpljoin.
    eexists.
    split; eauto.
    lets Heq_: sempend_to_n_wait_rdy_eq ts laump Hgtl; eauto.
    erewrite <- Heq_.
    auto. 
Qed.              

Lemma aux_lem: 
  forall ts tls t laump eid,
    ~In t ts -> 
    (fix filter (l : list tid) : list tid :=
       match l with
       | nil => nil
       | x :: l0 =>
           if
             match get tls x with
             | Some (_, rdy) =>
                 match get laump x with
                 | Some {| tskpt := PtPend (Vptr eid') |} => beq_tid eid eid'
                 | _ => false
                 end
             | _ => false
             end
           then x :: filter l0
           else filter l0
       end) ts =
      (fix filter (l : list tid) : list tid :=
         match l with
         | nil => nil
         | x :: l0 =>
             if
               match get tls x with
               | Some (_, rdy) =>
                   match get (set laump t {| tskpt := PtNormal |}) x with
                   | Some {| tskpt := PtPend (Vptr eid') |} => beq_tid eid eid'
                   | _ => false
                   end
               | _ => false
               end
             then x :: filter l0
             else filter l0
         end) ts.
Proof.
  induction ts.
  - intros. auto.
  - introv Hnin.
    assert (Hnin_: ~In t ts).
    { introv Hin. apply Hnin. simpl. right; auto. }
    assert (Hneq: a <> t).
    { introv Heq. subst. apply Hnin. simpl. left; auto. }
    destruct (get tls a) eqn: E.
    + destruct p.
      destruct t0 eqn: Et;
        destruct (get laump a) eqn: Eg.                      
      destruct l eqn: El.
      destruct tskpt eqn: Ept.
      destruct vp. 
      {
        repeat rewrite set_a_get_a'; eauto. 
        repeat rewrite Eg.  
        lets H__: IHts Hnin_; eauto. 
      }
      {
        repeat rewrite set_a_get_a'; eauto. 
        repeat rewrite Eg.  
        lets H__: IHts Hnin_; eauto. 
      }
      {
        repeat rewrite set_a_get_a'; eauto. 
        repeat rewrite Eg.  
        lets H__: IHts Hnin_; eauto. 
      }
      {
        repeat rewrite set_a_get_a'; eauto. 
        repeat rewrite Eg.  
        destruct (beq_tid eid a0) eqn: E'.
        match goal with H: _ |- _ :: ?l1 = _ :: ?l2 => cut (l1 = l2) end.
        intros. congruence.
        lets H__: IHts Hnin_; eauto.
        repeat rewrite set_a_get_a'; eauto.               
      }
      {
        repeat rewrite set_a_get_a'; eauto. 
        repeat rewrite Eg.  
        lets H__: IHts Hnin_; eauto.             
      }
      {
        repeat rewrite set_a_get_a'; eauto. 
        repeat rewrite Eg.  
        lets H__: IHts Hnin_; eauto.                         
      }
      {
        lets H__: IHts Hnin_; eauto.                               
      }
      {
        lets H__: IHts Hnin_; eauto.                         
      }
    +
      eapply IHts; eauto. 
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

Lemma sempend_block_get_cond_aux_preserve: 
  forall ts laump t tls p eid, 
    get laump t = Some {| tskpt := PtPend (Vptr eid) |} ->
    get tls t = Some (p, rdy) -> 
    atids_valid tls ts -> 
    (n_wait_rdy eid ts tls laump) =
      S (n_wait_rdy eid ts tls (set laump t {| tskpt := PtNormal |})).
Proof.
  induction ts.
  -
    introv Hgl Hgtls Hav.
    unfolds in Hav.
    destruct Hav as (Hds & Hav).
    specialize (Hav t).
    rewrite Hgtls in Hav.
    simpl in Hav.
    destruct Hav.
    false. apply H.
    introv Hf; inverts Hf.
  -
    introv Hgl Hgtls Hav.
    lets Hdecomp: atids_valid_decomp Hav; eauto.
    destruct Hdecomp as (p0 & st0 & Hgtls_ & Hex).
    destruct Hex as (tls' & Hjo & Hav').
    casetac a t Ht Hf.
    +
      subst.
      rewrite Hgtls_ in Hgtls; inverts Hgtls.
      unfold n_wait_rdy.
      unfold filter. 
      repeat rewrite Hgtls_.
      repeat rewrite Hgl.
      repeat (rewrite set_a_get_a).
      assert (~In t ts).
      {
        destruct Hav as (Hds & Hav_).
        lets H__: distinct_in_contr Hds; eauto. 
      }
      simpl length.
      asserts_rewrite (beq_tid eid eid = true).
      { rewrite beq_tid_true. auto. }
      rewrite aux_lem with (t:=t); eauto.
    +
      assert (Hg': get tls' t = Some (p, rdy)).
      {
        eapply join_get_or with (a:=t) in Hjo; eauto.
        destruct Hjo as [Hl | Hr].
        rewrite get_a_sig_a' in Hl; auto.
        tryfalse.
        auto.
      }

      lets Hih: IHts Hgl Hg' Hav'; eauto.
      assert (Haeq: forall t, In t ts -> get tls t = get tls' t).
      {
        introv Hin.
        assert (Hneq: t0 <> a).
        {
          unfolds in Hav.
          destruct Hav as (Hds & Hav).
          lets Hf_: distinct_in_contr Hds; eauto.
          introv Heq. subst. false. 
        }
        eapply map_join_get_none; eauto. 
        join auto.
      }
      rewrite n_wait_rdy_change_tls with (tls':=tls) in Hih; eauto.
      assert (Hrw:
               n_wait_rdy eid ts tls' (set laump t {| tskpt := PtNormal |}) =
                 n_wait_rdy eid ts tls (set laump t {| tskpt := PtNormal |})).
      { eapply n_wait_rdy_change_tls; eauto. }
      rewrite Hrw in Hih.
      do 2 erewrite n_wait_rdy_prop.
      destruct (get tls a) eqn: Egtls.
      destruct p1.
      destruct t0 eqn: Et.
      destruct (get laump a) eqn: Egl.
      destruct l.
      destruct tskpt eqn: Ept.
      destruct vp. 
      {
        rewrite set_a_get_a'; eauto.
        rewrite Egl.
        auto with arith.
      }
      {
        rewrite set_a_get_a'; eauto.
        rewrite Egl.
        auto with arith.
      }
      {
        rewrite set_a_get_a'; eauto.
        rewrite Egl.
        auto with arith. 
      }
      destruct (beq_tid eid a0) eqn: E'.
      {
        rewrite set_a_get_a'; eauto.
        rewrite Egl.
        rewrite E'. 
        auto with arith.
      }
      {
        rewrite set_a_get_a'; eauto.
        rewrite Egl.
        rewrite E'.
        auto with arith.
      }
      {
        rewrite set_a_get_a'; eauto. 
        rewrite Egl. 
        auto with arith. 
      }
      {
        rewrite set_a_get_a'; eauto.
        rewrite Egl.
        auto with arith.
      }
      {
        auto.
      }
      {
        auto.
      }
      
Qed.                   

Lemma wait_progpt_sem_block_get_preserve: 
  forall O tls els laump t eid_ p,   
    wait_progpt els laump ->
    get O abstcblsid = Some (abstcblist tls) -> 
    get O absecblsid = Some (absecblist els) -> 
    get tls t = Some (p, rdy) -> 
    get laump t = Some {| tskpt := PtPend (Vptr eid_) |} ->
    wait_progpt els (set laump t {| tskpt := PtNormal |}). 
Proof. 
  introv Hwp Hge_ Hgt Hgtls Hgl.
  unfold wait_progpt in *.
  introv Hge Hin.
  lets H__: Hwp Hge; eauto.
  casetac t t0 Ht Hf.
  - subst.
    lets H_: sem_tst_est_ Hin; eauto.
    destruct H_ as (p_ & Hgt_).
    rewrite Hgtls in Hgt_. inverts Hgt_.
  - rewrite set_a_get_a'; eauto. 
Qed.             

Lemma dtinv_sem_block_get_preserve:
  forall v1 v3 v' O0 O0' O O' Of laump laump' t eid, 
    sem_pend_block_get_succ (v1 :: v3 :: nil) O0 (v', Some O0') -> 
    get O curtid = Some (oscurt t) -> 
    v1 = Vptr eid -> 
    get laump t = Some {| tskpt := PtPend v1|} ->
    laump' = set laump t {| tskpt := PtNormal |} ->
    join O0 Of O ->
    join O0' Of O' -> 
    dtinv O laump -> 
    dtinv O' laump'. 
Proof.
  introv Hspbg Hgct Hgv1 Hgl Hl' Hjo Hjo' Hdti.
  unfold dtinv in *.
  unfolds in Hspbg.
  destruct Hspbg as (eid_ & Hspbg).
  simpljoin.
  rem_dis.
  inv_some.
  inv_lst.
  kvext O0 abstcblsid O.
  l_rew21 (get O abstcblsid).
  kvext O0 curtid O.
  l_rew21 (get O curtid).
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  assert (Hgteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgaeq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Hgeeq: get O absecblsid = get O' absecblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  kvext_h Hjo' gauxstid O'.
  l_rew21 (get O abstcblsid).
  l_rew21 (get O absecblsid).
  l_rew21 (get O atidlsid).
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  splits.
  - auto. 
  - (* cond_pv1 *)
    match goal with
      H: cond_pv1 ?gau_ ?els_ |- cond_pv1 ?gau'_ ?els' => 
        eapply cond_ge_preserve0 with (gau:=gau_) (gau':=gau'_); eauto
    end.
    introv Hgg. 
    casetac eid eid_ Ht Hf.
    +
      subst. rewrite set_a_get_a. eexists. split; simpl; eauto.
      match goal with H1: get ?t eid_ = _, Hgg: get _ eid_ = _ |- _ => rewrite H1 in Hgg; inverts Hgg end.
      simpl. splits; auto.
    +
      rewrite set_a_get_a'; eauto.
  - (* cond_pv0 *)
    unfold cond_pv0 in *.
    introv Hge.
    match goal with
      H: forall _, _ |- _ => lets H__: H Hge; eauto
    end.
    simpljoin. 

    casetac eid_ eid Ht Hf.
    + 
      subst.
      rewrite set_a_get_a.
      eexists. split; simpl; eauto.
      simpl.
      match goal with
        H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2
      end.
      simpl in H1.

      lets H__: sempend_block_get_cond_aux_preserve Hgl; eauto.
      specializes H__; eauto.
      rewrite H__ in H1. clear H__.
      rewrite H1.
      auto with arith.
    +
      rewrite set_a_get_a'; eauto.
      eexists.
      split; eauto.
      match goal with
        H: _ = (_ + ?e1)%nat |- (_ = _ + ?e2)%nat => assert (e1 = e2)
      end.
      {
        eapply n_wait_rdy_lem; eauto.
        {
          introv Hin_.
          destruct (get x t0) eqn: E.
          -
            destruct p.
            destruct t1 eqn: Et1. 
            + 
              casetac t t0 Htt Hff.
              * subst. rewrite set_a_get_a. rewrite Hgl.
                destruct (beq_tid eid eid_) eqn: EE.
                ** apply beq_tid_true_eq in EE. subst. false.
                ** auto.
              * rewrite set_a_get_a'; eauto.                 
            +
              auto.
          -
            auto. 
        }
      }
      congruence. 

  - (* wait_progpt *)
    
    eapply wait_progpt_sem_block_get_preserve; eauto. 

  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex Hin.
    casetac t t0 Ht Hf.
    + subst. rewrite set_a_get_a.
      introv Hf. inverts Hf.
    + rewrite set_a_get_a'; eauto.

Qed.
