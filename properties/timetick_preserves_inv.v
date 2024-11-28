
Require Import memory.
Require Import anno_language.
Require Import anno_opsem.

(* Require Import init. *)
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


Lemma timetick_preserves_inv_: 
  forall cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map),
    has_succ timetick cd -> 
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
  introv Hhs Hstep Hneq xHct Hlau Hlau' Hsatinv.

  inverts Hhs.
  inverts Hstep; 
    (rewrite get_set_same in Hlau'; subst; auto; fail).
  
  repeat symexe.
Qed.  

(* each atomic step of the tick handler preserves the
     global invariant on abstract states *) 
Lemma timetick_preserves_inv: 
  forall cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map),
    has_succ timetick cd -> 
    spec_step sc cd O lau cd' O' lau' -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hsuc Hsp Hgt Hgl Hsl Hdti.
  assert (Hor: 
      ~(get O abstcblsid = get O' abstcblsid /\
          get O absecblsid = get O' absecblsid /\
          get O gauxstid = get O' gauxstid /\
          get O atidlsid = get O' atidlsid /\ 
          lau = lau') \/
        (get O abstcblsid = get O' abstcblsid /\
           get O absecblsid = get O' absecblsid /\
           get O gauxstid = get O' gauxstid /\
           get O atidlsid = get O' atidlsid /\ 
           lau = lau')
    ) by tauto.
  destruct Hor as [Hn | Hy].
  - eapply timetick_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto.   
Qed.

