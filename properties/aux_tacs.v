
Require Import base_tac.
Require Import memory.
Require Import anno_language.
Require Import anno_opsem. 
Require Import seplog_lemmas.


Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].


Ltac l_rew21 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H2 in H1; inverts H1
  end.

Ltac l_rew12 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H1 in H2; inverts H2
  end.


Ltac inv_op r := 
  match goal with H: context [r] |- _ => inverts H; simpljoin end.

Ltac inv_some :=
  match goal with H: Some _ = Some _ |- _ => inverts H end.

Ltac invstep0 := 
  match goal with H: spec_step _ _ _ _ _ _ _ |- _ => inverts H end.

Ltac invstep :=
  match goal with
    H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; invstep
  | H: ?r _ _ _ |- _ => inverts H; simpljoin    
  end.

Ltac solve_steq :=
  match goal with
    H: ~(_ /\ _ /\ _ /\ _) |- _ => false; apply H; auto 
  end.

Ltac inv_lst :=
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.

Ltac rem_dis :=
  match goal with
    H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse
  end.

Ltac assert_oeq :=
  match goal with
    H: join _ _ ?O, H': join _ _ ?O' |- _ => assert (O = O') by (join auto); subst  
  end.
       

Ltac rewsimp :=
  match goal with
    H: _ |- context [get (set _ ?k1 _) ?k2] =>
      unify k1 k2; rewrite set_a_get_a
  | H: _ |- context [get (set _ ?k1 _) ?k2] =>
      rewrite set_a_get_a'; [idtac | let Hff:=fresh in introv Hff; inverts Hff]
  | _ => idtac
  end.

Ltac kvext_h_ hyp k constr mp :=
  match type of hyp with
    context [constr ?x] => assert (get mp k = Some (constr x))
  end;
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext_h hyp k mp :=
  match type of hyp with
    context [set _ k ?v] => assert (get mp k = Some v)
  end; 
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext_h0 hyp k mp :=
  match type of hyp with
    context [set _ k ?v] => assert (get mp k = Some v)
  end; 
  [ eapply join_get_get_l; eauto | idtac ].

Ltac kvext mp0 k mp :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (get mp k = v)
  end;
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext0 mp0 k mp :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (get mp k = v)
  end; 
  [ eapply join_get_get_l; eauto | idtac ].

Ltac invtac H := inverts H.

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 
