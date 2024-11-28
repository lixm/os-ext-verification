
Require Import memory.
Require Import anno_language.
Require Import anno_opsem.

Require Import init.
Require Import sem_sys.
Require Import succ_gen.

Require Import common_defs. 
Require Import sema_invs.

Require Import join_lib.
Require Import seplog_lemmas.
Require Import math_auto.
Require Import protect. 

Require Import aux_tacs.
Require Import aux_lemmas.
Require Import sema_lemmas.
Require Import sema_wait_lemmas.

Require Import sema_assms.

Require Import aux_notations.

Set Keyed Unification. 

Ltac invstep1 := 
  match goal with H: context [spec_step], H': context [spec_step] |- _ => inverts H end.

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

(* Definition no_unfold_lst  := *)
(*   (pnil, sem_pend_inst_get_succ, sem_pend_block, sem_pend_block_get_succ). *)

(* Ltac notin_no_unfold_lst lst f := *)
(*   match lst with *)
(*     (?lst', ?f') => unify f' f *)
(*   | (?lst', _) => notin_no_unfold_lst lst' f *)
(*   | pnil => fail *)
(*   end. *)

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
  | H: sem_pend_inst_get_succ _ _ (_, Some _) |- _ => idtac 
  | H: sem_pend_block _ _ (_, Some _) |- _ => idtac
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

Lemma sem_wait_preserves_inv_: 
  forall vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map),
    has_succ (semwait vl) cd -> 
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
    eapply dtinv_sem_pend_inst_get_succ_preserve; eauto.
  }
  {
    mttac spec_step invtac.
    symexe.
  }
  {
    mttac spec_step invtac.
    symexe.
    inverts H1. (* sem_pend_block;; spec_set_lst *) 
    inverts H6. (* spec_set_lst *) 
    inverts H11. (* sem_pend_block *) 
    2: {
      mttac spec_step ltac: (fun H=> clear H).
      symexe.
    }
    2: {
      mttac spec_step ltac: (fun H=> clear H).
      mttac spec_step ltac: (fun H=> clear H).
      symexe. 
    }
    2: {
      mttac spec_step invtac.
      mttac spec_step ltac: (fun H=> clear H).
      symexe.
      mttac spec_step ltac: (fun H=> clear H).
      symexe.
    }
    mttac spec_step invtac.
    simpl in Hhsat. unfolds in Hhsat. subst lau'0.
    eapply dtinv_sem_pend_block_preserve; eauto.
    mttac sem_pend_block ltac: (fun H => unfolds in H).
    simpljoin. inv_lst. eexists; eauto.
  }
  {
    mttac spec_step invtac.
    symexe. 
  }
  {
    mttac spec_step invtac.
    symexe. 
    mttac spec_step ltac: (fun H=> clear H).
    symexe.
    mttac spec_step ltac: (fun H=> clear H).
    symexe. 
  }
  {
    mttac spec_step invtac.
    symexe.
    inverts H1.
    inverts H6.
    inverts H10.
    2: {
      mttac spec_step ltac: (fun H=> clear H).
      symexe.
    }
    2: {
      mttac spec_step ltac: (fun H=> clear H).
      mttac spec_step ltac: (fun H=> clear H).
      symexe. 
    }
    2: {
      mttac spec_step invtac.
      mttac spec_step ltac: (fun H=> clear H).
      symexe.
      mttac spec_step ltac: (fun H=> clear H).
      symexe.
    }
    mttac spec_step invtac.
    simpl in Hhsat. unfolds in Hhsat. subst lau'0.
    assert (H: exists eid, v0 = Vptr eid).
    { mttac sem_pend_block_get_succ 
        ltac:(fun H=> assert (H__:=H); unfolds in H__; simpljoin; inv_lst).
      eexists; eauto. }
    simpljoin. 
    eapply dtinv_sem_block_get_preserve; eauto.
  }
  {
    mttac spec_step invtac.
    symexe. 
  }
  {
    mttac spec_step invtac.
    symexe.
    mttac spec_step ltac: (fun H=> clear H).
    symexe.
    mttac spec_step ltac: (fun H=> clear H).
    mttac spec_step ltac: (fun H=> clear H).
    symexe.
  }
Qed. 

(* each atomic step of the P operation preserves the global invariant
     on abstract states *) 
Lemma sem_wait_preserves_inv: 
  forall vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map),
    has_succ (semwait vl) cd -> 
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
  - eapply sem_wait_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto.   
Qed.
  
