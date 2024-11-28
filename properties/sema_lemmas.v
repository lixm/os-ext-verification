
Require Import base_tac. 
Require Import memory. 
Require Import anno_language.
Require Import aux_notations.

Require Import common_defs. 
Require Import succ_gen.

Require Import sem_sys.
Require Import sema_invs.

Require Import aux_tacs. 

Lemma n_wait_rdy_lem: 
  forall ts tls tls' aust aust' eid, 
    (forall t,
        In t ts -> 
        (match (get tls t) with
         | Some (_, rdy) =>
             match get aust t with | Some {| tskpt := PtPend (Vptr eid') |} => beq_tid eid eid'  | _ => false end
         | _ => false
         end) =
          (match (get tls' t) with
           | Some (_, rdy) =>
               match get aust' t with | Some {| tskpt := PtPend (Vptr eid') |} => beq_tid eid eid' | _ => false end
           | _ => false
           end))
    -> 
      n_wait_rdy eid ts tls aust = n_wait_rdy eid ts tls' aust'. 
Proof.
  inductions ts.
  - intros. unfolds. simpl. auto.
  - intros.
    unfold n_wait_rdy.
    simpl.
    assert (H00:=H).
    specialize (H a).
    specializes H; eauto.
    { simpl. left; auto. }
    destruct (get tls a) eqn: E; 
      destruct (get tls' a) eqn: E'; tryfalse.    
    destruct p.
    destruct p0.
    destruct t; destruct t0; tryfalse.
    destruct (get aust a) eqn: Ea;
      destruct (get aust' a) eqn: Ea'; tryfalse. 
    destruct l eqn: El; destruct l0 eqn: El0; tryfalse.
    destruct tskpt eqn: Et; destruct tskpt0 eqn: Et0; tryfalse.
    destruct vp eqn: Evp; destruct vp0 eqn: Evp0; tryfalse;  
      try (
          eapply IHts; eauto; 
          introv Hin'; 
          specializes H00; eauto; 
          simpl; right; auto); 
      try (
          match type of H with
            beq_tid _ _ =  _ => rewrite H
          | _ = beq_tid _ _ => rewrite <- H
          end; 
          eapply IHts; eauto; 
          introv Hin'; 
          specializes H00; eauto; 
          simpl; right; auto).

    subst vp0.
    subst vp.
    {
      repeat rewrite H.
      destruct (beq_tid eid a1) eqn: EE.
      simpl. apply eq_S.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
    }

    {
      destruct vp.
      simpl.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto. 
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      repeat rewrite H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }      
    }

    {
      destruct vp.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.      
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.      
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      rewrite <- H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }      
    }

    {
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }      
    }    
    
    {
      destruct l eqn: El; tryfalse.
      destruct tskpt eqn: et; tryfalse.
      destruct vp. 
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      repeat rewrite H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      repeat rewrite H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
    }
    
    {
      destruct l eqn: El; tryfalse.
      destruct tskpt eqn: et; tryfalse.
      destruct vp.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }              
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }              
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }              
      repeat rewrite <- H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }              
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                    
    }
    
    {
      eapply IHts; eauto.
      introv Hin'. 
      specializes H00; eauto.
      { simpl. right; auto. }              
    }

    {
      destruct (get aust a) eqn: Ea; tryfalse.
      destruct l eqn: El; tryfalse. 
      destruct tskpt eqn: Et; tryfalse.
      destruct vp.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. } 
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      repeat rewrite H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }      
    }

    {
      destruct (get aust' a) eqn: Ea'; tryfalse.
      destruct l eqn: El; tryfalse.
      destruct tskpt eqn: Et; tryfalse.
      destruct vp. 
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. } 
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      repeat rewrite <- H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }      
    }
    
    {
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                                           
    }
    
    {
      destruct p.
      destruct t eqn: Et; tryfalse.
      destruct (get aust a) eqn: Ea; tryfalse.
      destruct l eqn: El; tryfalse.
      destruct tskpt eqn: Etk; tryfalse.
      destruct vp. 
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      repeat rewrite H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }      
    }
    {
      destruct p.
      destruct t eqn: Et; tryfalse.
      destruct (get aust' a) eqn: Ea; tryfalse.
      destruct l eqn: El; tryfalse.
      destruct tskpt eqn: Etk; tryfalse.
      destruct vp. 
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                                                         
      repeat rewrite <- H.
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }                             
    }

    {
      eapply IHts; eauto.
      introv Hin'.
      specializes H00; eauto.
      { simpl. right; auto. }
    }
Qed.

Lemma n_wait_rdy_prop: 
  forall ts a laump tls eid,
    n_wait_rdy eid (a :: ts) tls laump =
      if 
        match get tls a with
        | Some (_, rdy) =>
            match get laump a with
            | Some {| tskpt := PtPend (Vptr eid') |} => beq_tid eid eid'
            | _ => false
            end
        | _ => false 
        end
      then S (n_wait_rdy eid ts tls laump)
      else  n_wait_rdy eid ts tls laump. 
Proof.
  intros.
  unfold n_wait_rdy at 1.
  simpl filter.
  destruct (get tls a) eqn: Egtls.
  destruct p.
  destruct t eqn: Et.
  destruct (get laump a) eqn: Egl.
  destruct l.
  destruct tskpt eqn: Ept.
  destruct vp.  
  { simpl. unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
  destruct (beq_tid eid a0) eqn: E'.
  { unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
  { unfold n_wait_rdy. auto. }
Qed.

Lemma n_wait_rdy_change_tls:
  forall ts tls tls' laump eid, 
    (forall t, In t ts -> get tls' t = get tls t) ->
    n_wait_rdy eid ts tls laump = n_wait_rdy eid ts tls' laump. 
Proof.
  induction ts.
  -
    introv Heq.
    unfolds.
    simpl. auto.
  -
    introv Ha.
    unfolds.
    simpl.
    lets H__: Ha a; eauto. 
    specializes H__; eauto.
    unfolds. left; auto.
    repeat rewrite H__.
    assert (Ha': forall t, In t ts -> get tls' t = get tls t).
    {
      introv Hin.
      eapply Ha; eauto.
      simpl. right; auto.
    }
    lets Hih: IHts laump Ha'; eauto.
    unfolds in Hih.
    
    destruct (get tls a) eqn: Egtls.
    destruct p.
    destruct t eqn: Et.
    destruct (get laump a) eqn: Egl.
    destruct l.
    destruct tskpt eqn: Ept.
    destruct vp. 
    simpl.
    { rewrite Hih. auto. }
    { rewrite Hih. auto. }
    { rewrite Hih. auto. }
    destruct (beq_tid eid a0) eqn: E.
    simpl.
    { rewrite Hih. auto. }
    { rewrite Hih. auto. }                    
    { rewrite Hih. auto. }                    
    { rewrite Hih. auto. }                    
    { rewrite Hih. auto. }                    
    { rewrite Hih. auto. }                    
Qed.                     

Lemma cond_ge_preserve0:
  forall gau gau' els els', 
    (forall eid n wl',
        get els' eid = Some (abssem n, wl') ->
        (exists wl, get els eid = Some (abssem n, wl))) ->
    (forall eid ga, 
        get gau eid = Some ga -> 
        exists ga', 
          get gau' eid = Some ga' /\ 
            (ninit ga = ninit ga' /\ nsig1 ga = nsig1 ga' /\ nacq1 ga = nacq1 ga')) ->
    cond_pv1 gau els ->
    cond_pv1 gau' els'.
Proof.
  introv Hsimpl Hgimpl Hcge.
  unfold cond_pv1 in *.
  introv Hge'.
  lets Hge: Hsimpl Hge'; eauto.
  destruct Hge as (wl & Hge).
  lets Hgg: Hcge Hge; eauto.
  simpljoin.
  split; auto.  
  specializes Hgimpl; eauto.
  simpljoin. 
  eexists.
  split; eauto.
  congruence.
Qed. 

Set Keyed Unification. 
Lemma cond_aux_preserve0:
  forall els els' (gaump gaump': GAuxStMod.map) n wl n' wl' gau gau' ts tls aust eid,
    get els eid = Some (abssem n, wl) -> 
    els' = set els eid (abssem n', wl') ->
    get gaump eid = Some gau ->
    gaump' = set gaump eid gau' ->
    nacq0 gau' = nacq0 gau ->
    nsig0 gau' = nsig0 gau ->
    cond_pv0 els tls ts gaump aust ->
    cond_pv0 els' tls ts gaump' aust. 
Proof.
  introv Hge Hels' Hggmp Hsgmp Hacq0e Hsig0e Hca.
  unfold cond_pv0 in *.
  introv Hge'.
  lets H__: Hca Hge; eauto. 
  simpljoin. 
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hge'.
    inverts Hge'.
    rewrite set_a_get_a. 
    eexists.
    split; eauto.
    rewrite H in Hggmp. inverts Hggmp.
    congruence.
  - rewrite set_a_get_a' in Hge'; eauto.
    rewrite set_a_get_a'; eauto.
Qed.

Lemma cond_aux_same_laust_preserve:
  forall els gaump n wl n' wl' gau gau' ts tls aust eid,
    get els eid = Some (abssem n, wl) -> 
    get gaump eid = Some gau -> 
    nacq0 gau' = nacq0 gau ->
    nsig0 gau' = nsig0 gau ->
    cond_pv0 els tls ts gaump aust ->
    cond_pv0 (set els eid (abssem n', wl')) tls ts (set gaump eid gau') aust. 
Proof.
  intros.
  eapply cond_aux_preserve0; eauto. 
Qed.

Lemma wait_progpt_same_laust_preserve:  
  forall els els' aust eid n n' wl, 
    wait_progpt els aust ->
    get els eid = Some (abssem n, wl) ->
    els' = set els eid (abssem n', wl) -> 
    wait_progpt els' aust. 
Proof.
  introv Hwp Hge He'.
  unfold wait_progpt in *.
  introv Hge' Hin.
  subst.
  casetac eid eid0 Ht Hf.
  - subst. rewrite set_a_get_a in Hge'. inverts Hge'.
    specializes Hwp; eauto.
  - rewrite set_a_get_a' in Hge'; eauto.
Qed.        

