Require Import include_frm.
Require Import base_tac.
Require Import sep_auto.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import Lia.

Set Nested Proofs Allowed.


(*-----------------------------------------------------------------------------------*)
(* low level data struct assertion used in os_tcb                                    *)
(*-----------------------------------------------------------------------------------*)
(* tcb vallist *)
Definition V_OSTCBNext     (vl:vallist) := nth_val 0 vl.
Definition V_OSTCBPrev     (vl:vallist) := nth_val 1 vl.
Definition V_OSTCBEventPtr (vl:vallist) := nth_val 2 vl.
Definition V_OSTCBMsg      (vl:vallist) := nth_val 3 vl.
Definition V_OSTCBDly      (vl:vallist) := nth_val 4 vl.
Definition V_OSTCBStat     (vl:vallist) := nth_val 5 vl.
Definition V_OSTCBPrio     (vl:vallist) := nth_val 6 vl.
Definition V_OSTCBX        (vl:vallist) := nth_val 7 vl.
Definition V_OSTCBY        (vl:vallist) := nth_val 8 vl.
Definition V_OSTCBBitX     (vl:vallist) := nth_val 9 vl.
Definition V_OSTCBBitY     (vl:vallist) := nth_val 10 vl.
Definition V_OSTCBflag     (vl:vallist) := nth_val 11 vl.

Definition V_OSTskLoc__ (vl:vallist) := nth_val 12 vl.
Definition V_OSTskPtr__ (vl:vallist) := nth_val 13 vl.

Open Scope code_scope.
Definition OS_TCB_flag : type := 
  STRUCT os_tcb_flag ­{
                  ⌞OSTCBNext @ STRUCT os_tcb ⋆;
                  OSTCBPrev @ STRUCT os_tcb ⋆ ;
                  OSTCBEventPtr @ OS_EVENT ∗ ; 
                  OSTCBMsg @ Void ∗ ;
                  OSTCBDly @ Int16u ;
                  OSTCBStat @ Int8u ;
                  OSTCBPrio @ Int8u ;
                  OSTCBX @ Int8u ;
                  OSTCBY @ Int8u ; 
                  OSTCBBitX @ Int8u;
                  OSTCBBitY @ Int8u
                  (*OSTCBMutexOwn @ OS_EVENT ∗*) ⌟
         }­.

Close Scope code_scope.

Open Scope Z_scope.
Open Scope int_scope.

Lemma join_sig_eq_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a b m1 m2 m3 x1 x2,
    usePerm = true ->
    isRw a = false ->
    isRw b = false ->
    join (sig l a) x1 m1 ->
    join (sig l b) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
  intros.
  let i := calc_ins_for_context in
  infer' i l; crush.
Qed.  
  
Lemma join_sig_eq :
  forall l a b m1 m2 m3 x1 x2,
    join (sig l (false, a)) x1 m1 ->
    join (sig l (false, b)) x2 m2 ->
    join m1 m2 m3 ->
    a = b.
  intros.
  assert ((false, a) = (false, b)).
  {
    eapply join_sig_eq_auto; ica.
  }
  inverts H2; auto.
Qed.  

Lemma ptomvallistr_disjoint_vl_eq :
  forall vl1 vl2 l m1 m2 m3,
    ptomvallist l false vl1 m1 ->
    ptomvallist  l  false  vl2 m2 ->
    length vl1 = length vl2 ->
    join m1 m2 m3 ->
    vl1 = vl2.
Proof.
  inductions vl1; intros.
  destruct vl2; auto.
  simpl in H1; inversion H1.

  destruct vl2.
  simpl in H1; inversion H1.

  simpl in H1; inverts H1.
  simpl in H; destruct l.

  do 3 destruct H; destruct H1.
  simpl in H0; do 3 destruct H0; destruct H5.

  unfold ptomval in H1, H5; substs.
  assert(a = m).
  eapply join_sig_eq; eauto.

  substs.
  assert(vl1 = vl2).
  assert(exists mx, join x0 x2 mx).
  geat.
  destruct H1.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m3:=x) (l:=(b,o+1)); auto.
  substs; auto.
Qed.

Lemma join_sig_false_sig_true_auto :
  forall (A B T : Type) (MC : PermMap A B T) l a m1 m2 m x1 x2 x,
    usePerm = true ->
    isRw a = false ->
    join m1 m2 m ->
    join (sig l a) x1 m1 ->
    join (sig l a) x2 m2 ->
    join x1 x2 x ->
    join (sig l (flip a)) x m.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.
  
  
Lemma join_sig_false_sig_true :
  forall l a m1 m2 m x1 x2 x,
    join m1 m2 m ->
    join (sig l (false, a)) x1 m1 ->
    join (sig l (false, a)) x2 m2 ->
    join x1 x2 x ->
    join (sig l (true, a)) x m.
Proof.
  intros.
  change (join (sig l (flip (false, a))) x m).
  eapply join_sig_false_sig_true_auto; ica.
Qed.
  
Lemma ptomvallistr_ptomvallist :
  forall vl l m1 m2 m3,
    ptomvallist l false vl m1 ->
    ptomvallist l false vl m2 ->
    join m1 m2 m3 ->
    ptomvallist l true  vl m3.
Proof.
  inductions vl; intros.
  simpl in *; substs.
  geat.

  destruct l.
  unfold ptomvallist in H, H0; fold ptomvallist in H, H0.
  do 3 destruct H; destruct H2.
  do 3 destruct H0; destruct H4.
  unfold ptomval  in *.
  
  substs.
  assert(exists m, join x0 x2 m).
  geat.
  destruct H2.
  unfold ptomvallist; fold ptomvallist.
  exists (sig (b, o) (true, a)) x.
  split.

  eapply join_sig_false_sig_true; eauto.
  split.
  unfolds; auto.
  lets Hx: IHvl H3 H5 H2; auto.
Qed.

Lemma byte_repr_int_unsigned_eq :
  forall i1 i2,
    Int.unsigned i1 <= Byte.max_unsigned ->
    Int.unsigned i2 <= Byte.max_unsigned ->
    Byte.repr (Int.unsigned i1) = Byte.repr (Int.unsigned i2) ->
    i1 = i2.
Proof.
  intros.
  assert(Byte.unsigned (Byte.repr (Int.unsigned i1)) = Byte.unsigned (Byte.repr (Int.unsigned i2))).
  rewrite H1; auto.
  do 2 rewrite Byte.unsigned_repr in H2.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i2)).
  rewrite H2; auto.
  do 2 rewrite Int.repr_unsigned in H3.
  auto.
  split; auto.
  pose proof Int.unsigned_range i2.
  destruct H3; auto.
  split; auto.
  pose proof Int.unsigned_range i1.
  destruct H3; auto.
  split; auto.
  pose proof Int.unsigned_range i1.
  destruct H3; auto.
Qed.

Lemma byte_repr_eq :
  forall z1 z2,
    0 <= z1 <= Byte.max_unsigned ->
    0 <= z2 <= Byte.max_unsigned ->
    Byte.repr z1 = Byte.repr z2 ->
    z1 = z2.
Proof.
  intros.
  assert(Byte.unsigned (Byte.repr z1) = Byte.unsigned (Byte.repr z2)).
  rewrite H1; auto.
  do 2 rewrite Byte.unsigned_repr in H2; auto.
Qed.

Lemma div_256_byte_repr_eq :
  forall z1 z2,
    z1 / 256 = z2 / 256 ->
    Byte.repr z1 = Byte.repr z2 ->
    z1 = z2.
Proof.
  intros.
  assert (Byte.unsigned (Byte.repr z1) = Byte.unsigned (Byte.repr z2)).
  rewrite H0; auto.
  do 2 rewrite Byte.unsigned_repr_eq in H1.
  unfold Byte.modulus in H1.
  unfold two_power_nat in H1; simpl in H1.
  clear H0.
  assert(256 <> 0) by lia.
  pose proof Z.div_mod z1 256 H0.
  pose proof Z.div_mod z2 256 H0.
  rewrite H in H2.
  rewrite H1 in H2.
  rewrite <- H2 in H3.
  auto.
Qed.

Lemma z_le_int16_max_div_256_byte_max :
  forall z,
    z <= Int16.max_unsigned ->
    z / 256  <= Byte.max_unsigned.
Proof.
  intros.
  unfold Int16.max_unsigned in H.
  simpl in H.
  unfold Byte.max_unsigned; simpl.
  
  replace 255 with (65535 / 256).
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma zero_le_int_unsigned_div_256 :
  forall i,
    0 <= Int.unsigned i / 256.
Proof.
  intros.
  pose proof Int.unsigned_range i.
  destruct H.
  replace 0 with (0 / 256).
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma zero_le_int_unsigned_div_256_256_256 :
  forall i,
    0 <= Int.unsigned i / 256 / 256 / 256.
Proof.
  intros.
  pose proof Int.unsigned_range i.
  destruct H.
  replace 0 with (0 / 256 / 256 / 256).
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma z_le_int_max_div_256_256_256_byte_max :
  forall z,
    z <= Int.max_unsigned ->
    z / 256 / 256 / 256 <= Byte.max_unsigned.
Proof.
  intros.
  unfold Int.max_unsigned in H.
  simpl in H.
  unfold Byte.max_unsigned; simpl.
  
  replace 255 with (4294967295 / 256 / 256 / 256).
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  apply Z.div_le_mono.
  lia.
  auto.
  compute; auto.
Qed.

Lemma rule_type_val_match_encode_val_eq :
  forall t v1 v2,
    rule_type_val_match t v1 = true ->
    rule_type_val_match t v2 = true ->
    encode_val t v1 = encode_val t v2 ->
    v1 = v2.
Proof.
  intros.
  destruct t, v1, v2;
    simpl in H, H0; tryfalse;
    auto;
    simpl in H1; try (destruct a); try (destruct a0); tryfalse.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inversion H1; substs.
  
  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.    
  apply byte_repr_int_unsigned_eq in H3; substs; auto.
  apply Z.leb_le in eq1.
  auto.
  apply Z.leb_le in eq2.
  auto.

  remember (Byte.repr (Int.unsigned i)) as X1.
  remember (Byte.repr (Int.unsigned i / 256)) as X2.
  remember (Byte.repr (Int.unsigned i0)) as Y1.
  remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts H1; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.
  
  apply byte_repr_eq in H3.

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H1; auto.
  do 2 rewrite Int.repr_unsigned in H4.
  substs; auto.
  
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  remember (Byte.repr (Int.unsigned i)) as X1.
  remember (Byte.repr (Int.unsigned i / 256)) as X2.
  remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3.
  remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4.    
  remember (Byte.repr (Int.unsigned i0)) as Y1.
  remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3.
  remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts H1; substs.

  apply byte_repr_eq in H5.
  lets Hx: div_256_byte_repr_eq H5 H4.
  lets Hx1: div_256_byte_repr_eq Hx H3.
  lets Hx2: div_256_byte_repr_eq Hx1 H2.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite Hx2; auto.
  do 2 rewrite Int.repr_unsigned in H1; substs; auto.

  split.
  apply zero_le_int_unsigned_div_256_256_256.

  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.

  split.
  apply zero_le_int_unsigned_div_256_256_256.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.

  inverts H1; substs; auto.
  inverts H1; substs; auto.
Qed.

(******************************************************************************)
(** ugly begin **)
(** paste from inv_prop, in order to proof node_OS_TCB_dup_false **)
Ltac simpl_map1 :=
  match goal with
    | H:exists _, _ |- _ => destruct H; simpl_map1
    | H:_ /\ _ |- _ => destruct H; simpl_map1

    | H: emposabst _ |- _ => unfold emposabst in H; subst; simpl_map1

    | H:join empenv _ _ |- _ => apply map_join_comm in H; apply map_join_emp' in H; subst; simpl_map1
    | H:join _ empenv _
      |- _ =>
      apply map_join_emp' in H; subst; simpl_map1
    | |- join empenv _ _ => apply map_join_comm; apply map_join_emp; simpl_map1
    | |- join _ empenv _ => apply map_join_emp; simpl_map1
    | H:join ?a ?b ?ab |- join ?b ?a ?ab => apply map_join_comm; auto
    | H:(_, _) = (_, _) |- _ => inversion H; clear H; simpl_map1
    | H:?x = ?x |- _ => clear H; simpl_map1
    | |- ?x = ?x => reflexivity
    | |- join _ ?a ?a => apply map_join_comm; simpl_map1
    | |- join ?a _ ?a => apply map_join_emp; simpl_map1
    | |- empenv = _ => reflexivity; simpl_map1
    | |- _ = empenv => reflexivity; simpl_map1
    | H:True |- _ => clear H; simpl_map1
    | |- True => auto
    | _ => try (progress subst; simpl_map1)
  end.

Ltac simpljoin1 := repeat progress simpl_map1.

Lemma struct_type_vallist_match_os_tcb_flag :
  forall v, struct_type_vallist_match OS_TCB_flag v ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: nil.
Proof.
  intros.
  unfold OS_TCB_flag in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  destruct v7; simpljoin1; tryfalse.
  destruct v8; simpljoin1; tryfalse.
  destruct v9; simpljoin1; tryfalse.
  destruct v10; simpljoin1; tryfalse.
  do 11 eexists; eauto.
Qed.

(** in order to prove node_os_tcb_dup_false, I must move lots lemmas and definitions from ucos_common,
    Very Very Ugly!!!!
    This file should be all of definitions of os invariant, not the auxiliary lemmas!
 **)
Definition array_struct t :=
  (exists t1 n, t = Tarray t1 n) \/ (exists id dl, t = Tstruct id dl) \/ ( t = Tvoid).

Lemma type_encode_nnil :
  forall t v,  ~array_struct t  -> encode_val t v <> nil.
Proof.
  inductions t; unfold encode_val in *;
  try solve [destruct v; simpl in *; intuition (try destruct a; tryfalse)].
  intros.
  false.
  apply H.
  branch 3; eauto.
  intros.
  false.
  apply H.
  branch 1; 
    do 2 eexists; eauto.
  intros.
  false.
  apply H.
  branch 2; 
    do 2 eexists; eauto.
Qed.

Lemma ptomval_nnil_neq_auto :
  forall (A B T : Type) (MC : PermMap A B T) x1 x2 m b1 b2 a1 a2 x4 x0,
    usePerm = true ->
    join x1 x2 m ->
    isRw b1 = true ->
    isRw b2 = true ->
    join (sig a1 b1) x4 x1 ->
    join (sig a2 b2) x0 x2 ->
    a1 <> a2.
  intros.
  let l := calc_ins in
  infer' l a1; crush.
Qed.

Lemma ptomval_nnil_neq:
  forall v1 v2 x y  x1 x2 m,
    v1 <> nil ->
    v2 <> nil ->
    join x1 x2 m ->
    ptomvallist x true v1 x1 ->
    ptomvallist y true v2 x2 ->
    x <> y.
Proof.
  introv Hn1 Hn2 Hj  Hpto1 Hpto2.
  destruct v1; destruct v2; tryfalse.
  unfolds in Hpto1.
  unfolds in Hpto2.
  destruct x.
  destruct y.
  simp join.
  unfold ptomval in *.
  subst.
  eapply ptomval_nnil_neq_auto with (b1 := (true, m0)) (b2 := (true, m1)); auto.
  exact Hj.
  eauto.
  eauto.
Qed.

Lemma pv_false :
  forall s x y t1 t2 v1 v2 P,
   ~array_struct t1 ->
      ~ array_struct t2 ->
    s  |= PV  x @ t1 |-> v1 ** PV y  @ t2 |-> v2 ** P-> x <> y.
Proof.
  introv Ht1 Ht2 H.
  sep lift 3%nat in H.
  assert (x = y \/ x <> y) by tauto.
  destruct H0; auto; subst y.
  remember ( PV x @ t1 |-> v1 ** PV x @ t2 |-> v2) as Hs.
  sep destroy H.
  subst.
  destruct_s x1.
  simpl in H1.
  simp join.
  unfolds in H4.
  unfolds in H5.
  simp join.
  remember (addrval_to_addr x)  as xx.
  lets Hneq1 : type_encode_nnil v1 Ht1.
  lets Hneq2 : type_encode_nnil v2 Ht2.
  lets Hz :  ptomval_nnil_neq H5 H4; eauto.
Qed.

Lemma node_OS_TCB_dup_false :
  forall p a1 a2 P s,
    s |= node p a1 OS_TCB_flag ** node p a2 OS_TCB_flag ** P ->
    False.
Proof.
  unfold node.
  intros.
  sep normal in H.
  sep destruct H.
  sep split in H.
  heat.

  eapply struct_type_vallist_match_os_tcb_flag in H3.
  eapply struct_type_vallist_match_os_tcb_flag in H2.
  heat.
  inverts H1.
  
  unfold Astruct in H.
  unfold OS_TCB_flag in H.
  unfold Astruct' in H.
  sep normal in H.
  sep lift 5%nat in H.
  sep lift 16%nat in H.

  (* ** ac: Check pv_false. *)
  remember (x,
            Int.add
              (Int.add
                 (Int.add
                    (Int.add Int.zero
                       (Int.repr
                          (Z.of_nat (typelen (Tcom_ptr os_tcb)))))
                    (Int.repr
                       (Z.of_nat (typelen (Tcom_ptr os_tcb)))))
                 (Int.repr (Z.of_nat (typelen (Tptr OS_EVENT)))))
              (Int.repr (Z.of_nat (typelen (Tptr Tvoid))))) as xx.

  assert (xx <> xx).
  {
    eapply pv_false.
    3: eauto.
    unfold not.
    intros.
    unfold array_struct in H0.
    destruct H0 as [? | [? | ?]]; heat; inverts H0.
    
    unfold not.
    intros.
    unfold array_struct in H0.
    destruct H0 as [? | [? | ?]]; heat; inverts H0.
  }
  tryfalse.
Qed.
(** ugly end **)
(******************************************************************************)
Require Import sep_join_lemmas.

Lemma join_sig_false_true :
  forall l a,
    join (sig l (false, a)) (sig l (false, a)) (sig l (true, a)).
Proof.
  intros.
  change (join (sig l (false, a)) (sig l (false, a)) (sig l (flip (false, a)))).
  eapply join_false_is_true_auto; ica.
Qed.

Lemma join_split :
  forall (m1:mem) m2 m m11 m12 m21 m22,
    join m1 m2 m ->
    join m11 m12 m1 ->
    join m21 m22 m2 ->
    exists mx1 mx2, join m11 m21 mx1 /\ join m12 m22 mx2 /\ join mx1 mx2 m.
  intros.
  geat.
Qed.  

Lemma ptomvallist_split :
  forall vl l m,
    ptomvallist l true  vl m ->
    exists m1 m2, ptomvallist l false vl m1 /\ ptomvallist  l false  vl m2 /\ join m1 m2 m.
Proof.
  inductions vl; intros.
  simpl in H; substs.
  simpl.
  do 2 eexists; splits; eauto.
  geat.

  unfold ptomvallist in H; fold ptomvallist in H; destruct l.
  simpljoin.
  unfold ptomvallist; fold ptomvallist.

  unfold ptomval in H0.
  
  lets Hx: join_sig_false_true (b, o) a.
  lets Hx1: IHvl H1.
  simpljoin.
  
  lets Hx2: join_split H Hx H4.
  simpljoin.
  unfold ptomval.
  exists x x3.
  split.
  do 2 eexists; splits; eauto.
  split; auto.
  do 2 eexists;  eauto.
Qed.

Lemma read_only_split_vptr:
  forall s x t v P,
    s |= GV x @ Tptr t |-> Vptr v ** P ->
    s |= (GV x @ Tptr t |-r-> Vptr v) **
      (GV x @ Tptr t |-r-> Vptr v) ** P.
Proof.
  intros.
  destruct_s s.
  simpl in H.
  simpljoin.
  unfold mapstoval in H9.
  simpljoin.
  
  lets Hx: ptomvallist_split H1.
  simpljoin.
  simpl.
  assert(x8 = x0).
  geat.
  substs.
  
  assert(exists xx, join x2 xx m /\ join x5 x1 xx).
  geat.
  destruct H9.
  destruct H9.
  exists x2 x6 m x3 x4 o.
  splits; eauto.
  exists x13 empmem x2 x2 empabst empabst; exists x3.
  splits; eauto.
  geat.
  unfold emposabst in *.
  substs.
  geat.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds.
  eexists; splits; eauto.
  unfolds; auto.

  exists x5 x1 x6 empabst o o.
  splits; eauto.
  unfold emposabst in *.
  substs.
  geat.
  geat.

  exists x13 empmem x5 x5 empabst empabst; exists empabst.
  splits; eauto.
  geat.
  geat.
  eexists; splits; eauto.
  unfolds; auto.
  unfolds; eexists; splits; eauto.
  unfolds; auto.
  unfold emposabst in *; subst.
  assert(x4 = o).
  geat.
  substs; auto.
Qed.

Lemma ptomvalr_join_eq :
  forall l v1 v2 m1 m2 m3,
    ptomval l false v1 m1 -> ptomval l false v2 m2 ->
    join m1 m2 m3 -> v1 = v2.
Proof.
  intros.
  unfold ptomval in *.
  substs.
  unfold join in H1.
  simpl in H1.
  unfold HalfPermMap.join in H1.
  destruct H1.
  pose proof H l.
  unfold sig in H1; simpl in H1.
  pose proof map_get_sig l (false, v1).
  unfold get in H2; simpl in H2.
  unfold HalfPermMap.get in H2.
  unfold sig in H2; simpl in H2.
  rewrite H2 in H1.
  pose proof map_get_sig l (false, v2).
  unfold get in H3; simpl in H3.
  unfold HalfPermMap.get in H3.
  unfold sig in H3; simpl in H3.
  rewrite H3 in H1.
  auto.
Qed.
(* end *)


Local Open Scope int_scope.
Local Open Scope Z_scope.


Definition RL_TCBblk_P vl := 
  exists prio x y bitx bity stat, 
    V_OSTCBPrio vl = Some (Vint32 prio) /\
      V_OSTCBX vl = Some (Vint32 x) /\ V_OSTCBY vl = Some (Vint32 y) /\
      V_OSTCBBitX vl = Some (Vint32 bitx) /\ V_OSTCBBitY vl = Some (Vint32 bity) /\
      V_OSTCBStat vl = Some (Vint32 stat) /\
      0 <= Int.unsigned prio < 64 /\
      prio &ᵢ ($ 7) = x /\
      prio >>ᵢ ($ 3) = y /\
      ($ 1) <<ᵢ x = bitx /\ ($ 1) <<ᵢ y = bity /\
      (
        (stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SEM) (* \/  *)
        (* stat = ($ OS_STAT_Q) \/  stat = ($ OS_STAT_MBOX) \/  *)
        (* stat = ($ OS_STAT_MUTEX) \/ stat = ($ OS_STAT_POSTQ) *)
        )
        /\
          exists eptr, V_OSTCBEventPtr vl = Some eptr /\ (stat = ($ OS_STAT_RDY) -> eptr = Vnull)
      ) .


Definition prio_in_tbl (prio:int32) (tbl:vallist) :=
  forall x y z,
    x = prio &ᵢ ($ 7) -> y = Int.shru prio  ($ 3) ->
    nth_val (nat_of_Z (Int.unsigned y)) tbl = Some (Vint32 z) -> 
    z &ᵢ (($ 1) <<ᵢ x) = (($ 1) <<ᵢ x).

Definition prio_not_in_tbl (prio:int32) (tbl:vallist) :=
  forall x y z,
    x = prio &ᵢ ($ 7) -> y = Int.shru prio ($ 3) ->
    nth_val (nat_of_Z (Int.unsigned y)) tbl = Some (Vint32 z) -> 
    z &ᵢ (($ 1) <<ᵢ x) = $ 0.

(* TCB is ready: tcb_blk's prio is in tbl, and tcb_blk's dly is 0 *)
Definition RdyTCBblk vl rtbl (prio : priority) := 
  V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_in_tbl prio rtbl .

Definition RLH_RdyI_P vl rtbl abstcb := 
  forall prio,
    RdyTCBblk vl rtbl prio ->
    V_OSTCBStat vl = Some (V$ OS_STAT_RDY) /\
      (* V_OSTCBDly vl = Some (V$ 0) /\ *)
      abstcb = (prio, rdy).

Definition RHL_RdyI_P  vl rtbl abstcb := 
  forall prio,
    abstcb = (prio,rdy) -> 
    (RdyTCBblk vl rtbl prio/\ 
       V_OSTCBStat vl = Some (V$ OS_STAT_RDY) (* /\  *)
       (* V_OSTCBDly vl = Some (V$ 0) *)).

Definition WaitTCBblk vl rtbl (prio : priority) :=
  V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_not_in_tbl prio rtbl. 

(* Definition WaitTCBblk vl rtbl (prio : priority) t:=  *)
(*   V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_not_in_tbl prio rtbl /\  *)
(*   V_OSTCBDly vl = Some (Vint32 t). *)


(* Definition RLH_Wait_P vl rtbl abstcb :=  *)
(*   forall prio t,  WaitTCBblk vl rtbl prio t -> *)
(*                   V_OSTCBStat vl = Some (V$ OS_STAT_RDY) -> *)
(*                   Int.ltu Int.zero t = true  /\ *)
(*                   exists (m:msg), abstcb = (prio,wait os_stat_time t,m). *)


(* Definition RHL_Wait_P vl rtbl abstcb :=  *)
(*   forall prio t (m:msg), abstcb = (prio,wait os_stat_time t,m)-> *)
(*                          WaitTCBblk vl rtbl prio t /\ *)
(*                          Int.ltu Int.zero t = true  /\ *)
(*                          V_OSTCBStat vl = Some (V$ OS_STAT_RDY). *)

(* wait for semaphores *) 
Definition RLH_WaitS_P vl rtbl abstcb := 
  forall prio eid,
    WaitTCBblk vl rtbl prio ->
    V_OSTCBStat vl = Some (V$ OS_STAT_SEM) ->
    V_OSTCBEventPtr vl = Some (Vptr eid) ->
    abstcb = (prio, wait eid). 

Definition RHL_WaitS_P vl rtbl abstcb := 
  forall prio eid, 
    abstcb = (prio, wait eid) -> 
    (WaitTCBblk vl rtbl prio /\
       V_OSTCBEventPtr vl = Some (Vptr eid)/\
       V_OSTCBStat vl = Some (V$ OS_STAT_SEM)).


Definition RLH_TCB_Status_Wait_P vl rtbl abstcb :=
  RLH_WaitS_P vl rtbl abstcb. 

Definition RHL_TCB_Status_Wait_P vl rtbl abstcb :=
  RHL_WaitS_P vl rtbl abstcb. 

Definition R_TCB_Status_P vl rtbl abstcb :=
  RLH_RdyI_P vl rtbl abstcb /\
  RHL_RdyI_P vl rtbl abstcb /\
  RLH_TCB_Status_Wait_P vl rtbl abstcb /\ 
  RHL_TCB_Status_Wait_P vl rtbl abstcb.


(* Low tcbmsg <-> High tcbmsg *)

Definition TCBNode_P vl  (rtbl: vallist) (abstcb: priority * taskstatus) :=  
  match abstcb with
  | (p, st) => 
      V_OSTCBPrio vl = Some (Vint32 p) /\ 
        RL_TCBblk_P vl /\ 
        R_TCB_Status_P vl rtbl abstcb 
  end.

Notation TcbJoin := joinsig. 
  
Fixpoint TCBList_P (v: val) (l:list vallist) (rtbl : vallist) (tcbls : TcbMod.map) {struct l} : Prop := 
  match l with
  | nil =>  tcbls = emp 
  | vl :: l' =>
      exists tid v' tcbls' abstcb,  
      v = Vptr tid /\
        V_OSTCBNext vl = Some v' /\
        TcbJoin tid abstcb tcbls' tcbls/\
        TCBNode_P vl rtbl abstcb /\ 
        TCBList_P v' l' rtbl tcbls'
  end.                                   

Notation flag_off := (Int.repr 24%Z). 

Fixpoint dllsegflag (head tailnext : val) (l:list vallist) (next: vallist -> option val) := 
  match l with
  | nil => [| head = tailnext |]  ** [|l = nil|]
  | vl::l' =>
      (
        EX a vn,
        [|head = Vptr a|] **
          [|next vl = Some vn|] ** 
          PV (get_off_addr a flag_off) @ Tint8 |-r-> (Vint32 (Int.repr 1%Z)) **
                                                       dllsegflag vn tailnext l' next
      )
  end.

Definition tcbdllflag head l := dllsegflag head Vnull l V_OSTCBNext.

Definition tcbdllseg  (head headprev tail tailnext : val) (l : list vallist) :=
  dllseg  head headprev tail tailnext l OS_TCB_flag  V_OSTCBPrev V_OSTCBNext .


Definition AOSTCBList_old
  (p1 p2: val) (l1 l2:list vallist) (rtbl : vallist) (hcurt:addrval)(tcbls : TcbMod.map) :=
  EX tail1 tail2 tcbls1 tcbls2,
    (GV OSTCBList @ (Tptr OS_TCB) |-> p1) **
      tcbdllseg p1 Vnull tail1 p2 l1 ** 
      (GV OSTCBCur @ (Tptr OS_TCB) |-> p2) **
      tcbdllseg  p2 tail1 tail2 Vnull l2 **
      [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
      [| join tcbls1 tcbls2 tcbls|] **
      [| TCBList_P p1 l1 rtbl tcbls1 |] **
      [| TCBList_P p2 l2 rtbl tcbls2 |].


Notation loc_off := (Int.repr 25%Z).
Notation ptr_off := (Int.repr 26%Z).

Fixpoint sllsegfreeflag (head tailnext : val) (l : list vallist)
        (next : vallist -> option val) {struct l} : asrt :=
   match l with
  | nil => [|head = tailnext|]
  | vl :: l' =>
    (
      EX a vn v1 v2, 
       [|head = Vptr a|] **
       [|next vl = Some vn|] **
       PV (get_off_addr a flag_off) @ Tint8 |-> (Vint32 (Int.repr 0%Z)) ** 
       PV (get_off_addr a loc_off) @ Tint8 |-> v1 ** 
       PV (get_off_addr a ptr_off) @ (Tptr OS_EVENT) |-> v2 ** 
       sllsegfreeflag vn tailnext l' next 
    ) 
  end.

Definition sllfreeflag head l := sllsegfreeflag head Vnull l V_OSTCBNext.


Definition TCBFree_Not_Eq p ct l:=
  [| p <> Vptr ct |]
    ** sll p l OS_TCB_flag V_OSTCBNext ** sllfreeflag p l.

Definition prio_not_in_tcbls p (tcbls:TcbMod.map) :=
  ~ exists t st, get tcbls t = Some (p, st). 

Definition TCBFree_Eq p ct l tcbls:=
  EX l' vl p',
  [| p = Vptr ct /\ l = vl :: l' /\ V_OSTCBNext vl = Some p' |] **
    Astruct ct OS_TCB_flag vl **
    [| struct_type_vallist_match OS_TCB_flag vl /\
         RL_TCBblk_P vl /\
         exists prio, V_OSTCBPrio vl = Some (Vint32 prio) /\
                        (*prio_not_in_tbl prio rtbl /\*) prio_not_in_tcbls prio tcbls |] **
  PV (get_off_addr ct flag_off)@Tint8 |-r-> (Vint32 (Int.repr 0%Z)) **
  (EX v1 v2,  
      PV (get_off_addr ct loc_off) @ Tint8 |-r-> v1 ** 
      PV (get_off_addr ct ptr_off) @ (Tptr OS_EVENT) |-r-> v2 
  ) **
  sll p' l' OS_TCB_flag V_OSTCBNext **
  sllfreeflag p' l'. 


Definition AOSTCBFreeList (p:val) (l:list vallist)  :=
  (GV OSTCBFreeList @ (Tptr OS_TCB) |-> p)
    ** sll p l OS_TCB_flag  V_OSTCBNext **  sllfreeflag p l.


Definition AOSTCBFreeList' (p:val) (l:list vallist) (ct:addrval) tcbls:=
  (GV OSTCBFreeList @ (Tptr OS_TCB) |-> p) **  (TCBFree_Not_Eq p ct l  \\// TCBFree_Eq p ct l tcbls).


(* OSRdyTbl & OSRdyGrp *)
Definition AOSRdyTbl (vl:vallist) := 
  GAarray OSRdyTbl (Tarray Tint8 (nat_of_Z OS_RDY_TBL_SIZE)) vl **  
          [| array_type_vallist_match Tint8 vl /\ length vl = (nat_of_Z OS_RDY_TBL_SIZE)|]. 

Definition AOSRdyGrp (v:val) := GV OSRdyGrp @ Tint8 |-> v ** [| rule_type_val_match Tint8 v = true |].

(* OSUnMapTbl & OSMapTbl *)
Definition OSMapVallist :=
  V$1::V$2::V$4::V$8::V$16::V$32::V$64::V$128::nil.

Definition AOSMapTbl :=
  GAarray OSMapTbl (Tarray Tint8 8) OSMapVallist.

Definition OSUnMapVallist :=
  V$0::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$6::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$7::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$6::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$5::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::
   V$4::V$0::V$1::V$0::V$2::V$0::V$1::V$0::V$3::V$0::V$1::V$0::V$2::V$0::V$1::V$0::nil.

Definition AOSUnMapTbl :=
  GAarray OSUnMapTbl (Tarray Tint8 256) OSUnMapVallist.

Definition RL_RTbl_PrioTbl_P rtbl ptbl vhold:= 
  forall p,
    0 <= Int.unsigned p < 64 ->
    prio_in_tbl p rtbl -> 
    exists tid,
      nth_val (Z.to_nat (Int.unsigned p)) ptbl = Some (Vptr tid) /\ tid <> vhold. 


Definition R_Prio_No_Dup (tcbls : TcbMod.map) :=
  forall tid tid' prio st prio' st',
    tid <> tid' ->
    get tcbls tid = Some (prio, st) ->
    get tcbls tid' = Some (prio', st') ->
    prio <> prio'.
              

Definition R_PrioTbl_P (ptbl : vallist) (tcbls : TcbMod.map) (vhold:addrval):=
  (forall prio tcbid,
      (0<=Int.unsigned prio<64) ->
      nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) ->
      tcbid <> vhold ->
      exists st, get tcbls tcbid = Some (prio, st)) /\ 
    (forall tcbid prio st,
        get tcbls tcbid = Some (prio, st) ->
        nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) /\ tcbid <> vhold) /\
    R_Prio_No_Dup tcbls.

Definition R_PrioTbl_P' (ptbl : vallist) (tcbls : TcbMod.map) (vhold:addrval):=
  (forall prio1 prio2 tcbid, 
     (0<=Int.unsigned prio1<64) ->
     nth_val (nat_of_Z (Int.unsigned prio1)) ptbl = Some (Vptr tcbid) ->
     (0<=Int.unsigned prio2<64) ->
     nth_val (nat_of_Z (Int.unsigned prio2)) ptbl = Some (Vptr tcbid) ->
     tcbid <> vhold ->
     exists pt st, get tcbls tcbid = Some (pt,st) /\ (pt = prio1 \/ pt = prio2)) /\ 
  (forall tcbid prio st,
     get tcbls tcbid = Some (prio, st) -> 
     nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) /\ tcbid <> vhold) /\
  R_Prio_No_Dup tcbls.

Lemma R_PrioTbl_Eq:
  forall ptbl tcbls vhold, R_PrioTbl_P ptbl tcbls vhold <-> R_PrioTbl_P' ptbl tcbls vhold.
Proof.
  intros.
  split.
  -
    unfold R_PrioTbl_P. unfold R_PrioTbl_P'.
    intros.
    destruct H.
    split.
    2: auto.
    intros. clear H0.
    apply H in H2; auto.
    simpljoin1. exists prio1 x. split. auto. left. auto.
  -
    unfold R_PrioTbl_P. unfold R_PrioTbl_P'.
    intros.
    destruct H.
    split; auto. clear H0.
    intros.
    lets H00: H H0 H1 H0 H1 H2.
    simpljoin1. exists x0. 
    destruct H4; subst; auto.
Qed.     
  
(* OSTCBPrioTbl *)

(* new add *)

(* Definition RLH_PrioTbl_P (ptbl : vallist) (ptls : PtbMod.map) (vhold:addrval):= *)
(* (forall prio, *)
(*       ~ (0<=Int.unsigned prio <64) -> *)
(*         get ptls prio = None) /\ *)
(* (forall prio, *)
(*       (0<=Int.unsigned prio <64) -> *)
(*       nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some Vnull -> *)
(*         get ptls prio = Some Null) /\ *)
(* (forall prio, *)
(*       (0<=Int.unsigned prio <64) -> *)
(*       nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr vhold) -> *)
(*         get ptls prio = Some Holder) /\ *)
(* (forall prio tcbid, *)
(*       (0<=Int.unsigned prio <64) -> *)
(*       nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) -> *)
(*       tcbid <> vhold -> *)
(*         get ptls prio = Some (Valid_Addr tcbid)). *)

(* Definition RHL_PrioTbl_P (ptbl : vallist) (ptls : PtbMod.map) (vhold:addrval):= *)
(* (forall prio, *)
(*         get ptls prio = None -> *)
(*         ~ (0<=Int.unsigned prio <64)) /\ *)
(* (forall prio, *)
(*         get ptls prio = Some Null -> *)
(*         (0<=Int.unsigned prio <64) /\ *)
(*       nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some Vnull) /\ *)
(* (forall prio, *)
(*         get ptls prio = Some Holder -> *)
(*         (0<=Int.unsigned prio <64) /\ *)
(*       nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr vhold) ) /\ *)
(* (forall prio tcbid, *)
(*         get ptls prio = Some (Valid_Addr tcbid) -> *)
(*         (0<=Int.unsigned prio <64) /\ *)
(*       nth_val (nat_of_Z (Int.unsigned prio)) ptbl = Some (Vptr tcbid) /\ *)
(*       tcbid <> vhold). *)

(* Definition RH_PrioTbl_P (ptbl : vallist) (ptls : PtbMod.map) (vhold:addrval):= *)
(* RLH_PrioTbl_P ptbl ptls vhold /\ RHL_PrioTbl_P ptbl ptls vhold. *)

(* end of new add *)

(* Notation HPriotls ptls:= (Aabsdata absptlsid (absptls  ptls)). *)

(* OSTCBPrioTbl *)

Definition AOSTCBPrioTbl
  (vl:vallist) (rtbl:vallist) (tcbls:TcbMod.map) (* (ptls : PtbMod.map) *) (vhold:addrval) :=  
  GAarray OSTCBPrioTbl (Tarray (Tptr OS_TCB) 64) vl **
  (G& OSPlaceHolder @ Tint8 == vhold ** (EX v, PV vhold @ Tint8 |-> v)) **
  [| array_type_vallist_match (Tptr OS_TCB) vl /\ length vl = 64%nat |] **
  [|RL_RTbl_PrioTbl_P rtbl vl vhold|] ** [| R_PrioTbl_P vl tcbls vhold|]. 
  (* ** [| RH_PrioTbl_P vl ptls vhold |] ** HPriotls ptls.  *)

Definition AOSTime (t:val) := GV OSTime @ Tint32 |-> t.  

(* OSIntNesting *)
Definition AOSIntNesting := EX v,GV OSIntNesting @ Tint32 |-> Vint32 v.

(*-----------------------------------------------------------------------------------*)
(* relation in low level                                                             *)
(*-----------------------------------------------------------------------------------*)
(* Low tbl grp *)

Definition RL_Tbl_Grp_P (tbl:vallist) (grp:val):= 
  (forall n v v', (0<=n<8)%nat -> nth_val n tbl = Some (Vint32 v) -> grp = Vint32 v' ->
                 ((v' &ᵢ (($ 1) <<ᵢ ($ (Z_of_nat n))) = $0 <-> v = $0) /\ 
                  (v' &ᵢ (($ 1) <<ᵢ ($ (Z_of_nat n))) = (($ 1) <<ᵢ ($ (Z_of_nat n))) <->
                   Int.ltu ($ 0) v = true ))) .

(* OSRdyTbl & OSRdyGrp *)
Definition AOSRdyTblGrp (vl:vallist) (v:val) :=
  AOSRdyTbl vl ** AOSRdyGrp v ** [|RL_Tbl_Grp_P vl v /\ prio_in_tbl (Int.repr OS_IDLE_PRIO) vl|].

(* high level assertion *)
Notation HTCBList tcbls:= (Aabsdata abstcblsid (abstcblist tcbls)).

Notation HTime t := (Aabsdata ostmid (ostm t)).

Notation HCurTCB tid:= (Aabsdata curtid (oscurt tid)).

Notation HECBList ecbls:= (Aabsdata absecblsid (absecblist  ecbls)).

Definition AGVars:=
  (GV OSRunning @ (Tint8) |-> Vint32 (Int.repr 1)) ** 
  (EX v, GV OSPrioHighRdy @ (Tint8) |-> Vint32 v ** [| Int.unsigned v <= 63 |]) ** 
  (EX v, GV OSCtxSwCtr @ (Tint32) |-> Vint32 v) ** 
  (EX v,GV OSTCBHighRdy  @ (Tptr OS_TCB) |-> Vptr v) **  
  (EX v, GV OSPrioCur @ (Tint8) |-> Vint32 v ** [| Int.unsigned v <= 63 |])  **
  (EX v, GV OSIntExitY @ (Tint8) |-> Vint32 v).

Definition RH_CurTCB ct (tcbls:TcbMod.map) := exists p st, get tcbls ct = Some (p, st) (*/\ isrdy st*). 
(*-----------------------------------------------------------------------------------*)
(* relation of low level and high level                                              *)
(*-----------------------------------------------------------------------------------*)


(*-----------------------------------------------------------------------------------*)
(* os_event vallist                                                                  *)
(*-----------------------------------------------------------------------------------*)
Definition V_OSEventType (vl:vallist) := nth_val 0 vl.
Definition V_OSEventGrp  (vl:vallist) := nth_val 1 vl.
Definition V_OSEventCnt  (vl:vallist) := nth_val 2 vl.
Definition V_OSEventPtr  (vl:vallist) := nth_val 3 vl.
Definition V_OSEventListPtr (vl:vallist) := nth_val 5 vl.
(* Definition V_OSPostEventGrp  (vl:vallist) := nth_val 6 vl. *)

(*-----------------------------------------------------------------------------------*)
(* os_q vallist                                                                      *)
(*-----------------------------------------------------------------------------------*)
Definition V_OSQPtr      (vl:vallist) := nth_val 0 vl.
Definition V_OSQStart    (vl:vallist) := nth_val 1 vl.
Definition V_OSQEnd      (vl:vallist) := nth_val 2 vl.
Definition V_OSQIn       (vl:vallist) := nth_val 3 vl.
Definition V_OSQOut      (vl:vallist) := nth_val 4 vl.
Definition V_OSQSize     (vl:vallist) := nth_val 5 vl.
Definition V_OSQEntries  (vl:vallist) := nth_val 6 vl.
Definition V_qfreeblk    (vl:vallist) := nth_val 7 vl.

(*-----------------------------------------------------------------------------------*)
(* os_q_freeblk vallist                                                              *)
(*-----------------------------------------------------------------------------------*)
Definition V_nextblk     (vl:vallist) := nth_val 0 vl.

(*-----------------------------------------------------------------------------------*)
(* os_q_ptr vallist                                                                  *)
(*-----------------------------------------------------------------------------------*)
Definition V_next        (vl:vallist) := nth_val 0 vl.
Definition V_qeventptr   (vl:vallist) := nth_val 1 vl.


(*-----------------------------------------------------------------------------------*)
(* low level data struct assertion used in os_q                                      *)
(*-----------------------------------------------------------------------------------*)
Open Scope int_scope.


Definition EVENT_TBL_INIT_VL:= 
  Vint32 (Int.zero) :: 
  Vint32 (Int.zero):: 
  Vint32 (Int.zero)::
  Vint32 (Int.zero):: 
  Vint32 (Int.zero)::
  Vint32 (Int.zero)::
  Vint32 (Int.zero)::
  Vint32 (Int.zero)::nil.


Definition id_addrval' (v : val) (id :var) (t : type):=
     match v with
     | Vptr av => id_addrval av id t
     | _ => None
    end.


Fixpoint ecbf_sllseg (head tailnext : val)  (l:list vallist) (t:type) (next: vallist -> option val):=
  match l with
    | nil => [| head = tailnext |]
    | vl::l' => EX  vn ltbl vla,
                [|next vl = Some vn|] **
                node head vl t ** 
                [| id_addrval' head OSEventTbl OS_EVENT = Some ltbl |] ** 
                Aarray ltbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) vla **
                [| V_OSEventType vl = Some (V$OS_EVENT_TYPE_UNUSED) |] ** (* added by CNU *)
                ecbf_sllseg vn tailnext l' t next
  end.

Definition ecbf_sll := 
  fun (head : val) (l : list vallist) (t : type) (next : vallist -> option val) =>
    ecbf_sllseg head Vnull l t next.

Definition sll head l t next := sllseg head Vnull l t next.

Definition AOSEventFreeList p (l:list vallist) :=
  GV OSEventFreeList @ (Tptr OS_EVENT) |-> p ** 
     ecbf_sll p l OS_EVENT V_OSEventListPtr. 

Notation beq_addrval := beq_tid.

Definition beq_val (v1:val) (v2:val) :=
  match v1, v2 with
    | Vundef, Vundef => true
    | Vnull, Vnull => true
    | Vint32 i1, Vint32 i2 => Int.eq i1 i2
    | Vptr p1, Vptr p2 => beq_addrval p1 p2
    | _, _ => false
  end.

Fixpoint ptr_in_ecbsllseg (p:val) (head:val) (l:list vallist) : Prop :=
  match l with
  | nil => False
  | h::l' =>
    match head with
      Vnull => False
    | Vptr a => 
      if (beq_val p head)
      then True
      else
        match (V_OSEventListPtr h) with 
        | None => False
        | Some next => ptr_in_ecbsllseg p next l'
        end
    | _ => False
    end
  end. 

Definition ptr_in_ecblist := ptr_in_ecbsllseg.  

Close Scope Z_scope.

Definition EventCtr := (vallist * vallist)%type.  

Open Scope Z_scope.

Definition RH_ECB_P (absecb : absecb.B) := 
  match absecb with
    |(ed, waitset) => 
     match ed with
       | abssem z => 
         (Int.ltu Int.zero z = true -> waitset = nil) /\
         (waitset <> nil -> Int.eq Int.zero z = true)
     end
  end.

Definition offset_zero (l:addrval) := exists b, l = (b,Int.zero).

Definition AOSEventTbl letbl etbl := 
  Aarray letbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) etbl 
         ** [| array_type_vallist_match Tint8 etbl |].

(* Definition AOSPostEventTbl lpetbl petbl :=  *)
(*   Aarray lpetbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) petbl  *)
(*          ** [| array_type_vallist_match Tint8 petbl |]. *)

Definition AOSEvent losevent osevent etbl :=
  EX letbl egrp,
    node losevent osevent OS_EVENT 
      ** AOSEventTbl letbl etbl ** 
      [| id_addrval' losevent OSEventTbl OS_EVENT = Some letbl |] ** 
      [| V_OSEventGrp osevent = Some egrp |] ** [|RL_Tbl_Grp_P etbl egrp|]. 

Fixpoint vallist_post (first:nat) (vl:vallist) :=
  match first with
    | 0%nat => vl
    | S n => match vl with 
               | nil => nil
               | v::vl' => vallist_post n vl'
             end
  end.

Fixpoint vallist_pre (last:nat) (vl:vallist):= 
  match last with
    | 0%nat=> nil
    | S n => match vl with
               | nil => nil
               | v::vl' => v::(vallist_pre n vl')
             end
  end.

Definition vallist_seg (first last:nat) (vl:vallist) :=
  vallist_post first (vallist_pre last vl).

Fixpoint isptr_list vl:=
  match vl with
    | nil => True
    | v::vl' => isptr v /\ isptr_list vl'
  end.

(* Low msgtbl <-> High msgl *)

Definition  RLH_ECBData_P (lecb: EventData) (hecb:absecb.B) :=
  match lecb , hecb with
    | (DSem n1), (abssem n2, waitset) => 
      n1 = n2 /\ RH_ECB_P hecb
  end.

Definition RH_TCBList_ECBList_SEM_P (ecbls: EcbMod.map) (tcbls: TcbMod.map) (ct: tid) :=  
  (forall eid n wls tid,
      (get ecbls eid = Some (abssem n, wls) /\ In tid wls) ->
      (exists prio, get tcbls tid = Some (prio, wait eid)))
  /\ 
    (forall p tid eid,
        get tcbls tid = Some (p, wait eid) -> 
        (exists n wls, get ecbls eid = Some (abssem n, wls) /\ In tid wls)).

(* copy from abs_op.v *)
Definition prio_available prio tls:=
  forall t p x, get tls t = Some (p, x) -> Int.eq prio p = false.


Definition RH_TCBList_ECBList_P ecbls tcbls ct:=
  RH_TCBList_ECBList_SEM_P ecbls tcbls ct. 




(*-----------------------------------------------------------------------------------*)
(* Low qptrlist <-----> High mqls                                                    *)
(*-----------------------------------------------------------------------------------*)



Definition AEventData := 
  fun (osevent : vallist) (d : EventData) =>
    match d with
    | DSem z =>
        [|V_OSEventType osevent = Some (V$OS_EVENT_TYPE_SEM)|] **
          [| V_OSEventCnt osevent = Some (Vint32 z) |] **
          [| Int.ltu z (Int.repr 65536) = true |] 
    end.

Definition AEventNode:=
  fun (v : val) (osevent etbl: vallist) (d : EventData) =>
    AOSEvent v osevent etbl ** AEventData osevent d.


Fixpoint evsllseg (head  tailnext : val) (vl:list EventCtr)
         (ecbls : list EventData) {struct vl}: asrt :=
  match vl with
    | nil => [|head = tailnext /\ ecbls = nil|]
    | l::vl'=>
      match ecbls with
        | nil => Afalse
        | enode :: ecbls' =>
          match l with
            | (osevent, etbl) =>
              EX vn, 
                 [|V_OSEventListPtr osevent = Some vn|] **
                 AEventNode head osevent etbl enode **  
                 evsllseg vn tailnext vl' ecbls'
          end
      end
  end. 


Definition PrioWaitInQ prio etbl := 
  exists x y z,  
    0<=prio<64 /\
      x = Int.and ($ prio) ($ 7) /\ y = Int.shru ($ prio) ($ 3) /\
      nth_val (nat_of_Z (Int.unsigned y)) etbl = Some (Vint32 z) /\
      Int.and z (Int.shl Int.one x) = (Int.shl Int.one x).


Definition RLH_ECB_ETbl_SEM_P (l:addrval) (ecb : EventCtr) tcbls :=
  match ecb with
    | (osevent, etbl) =>  
      forall prio, PrioWaitInQ prio etbl ->
                   V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_SEM)) ->
                   (exists tid,
                      get tcbls tid = Some ((Int.repr prio), wait l)) 
  end.

Definition RHL_ECB_ETbl_SEM_P (l:addrval) (ecb : EventCtr)  tcbls :=
  match ecb with
  | (osevent, etbl) => 
      forall prio tid,
        get tcbls tid = Some (prio, wait l) -> 
        PrioWaitInQ (Int.unsigned prio) etbl /\ V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_SEM))
  end.


Definition RLH_ECB_ETbl_P l ecb tcbls := 
  RLH_ECB_ETbl_SEM_P l ecb tcbls. 

Definition RHL_ECB_ETbl_P l ecb tcbls := 
  RHL_ECB_ETbl_SEM_P l ecb tcbls. 


Definition Event_Type_P osevent :=
  V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_SEM)). 


Definition R_ECB_ETbl_P (l:addrval) (ecb : EventCtr)  tcbls :=
  RLH_ECB_ETbl_P l ecb tcbls /\
  RHL_ECB_ETbl_P l ecb tcbls /\
  Event_Type_P (fst ecb).

Fixpoint ECBList_P (v tl: val) (l:list EventCtr) (ecbls : list EventData) (mqls: EcbMod.map) 
         (tcbls : TcbMod.map) 
         {struct l} : Prop :=
  match l with
    | nil =>  ecbls=nil /\ mqls = emp /\ v = tl
    | vl :: l' =>  
      exists qid,
        v = Vptr qid /\ R_ECB_ETbl_P  qid vl tcbls /\ 
        match ecbls with
          | nil => False
          | enode ::ecbls' =>
            match vl with
              | (osevent, etbl) => 
                exists  absmq mqls' v', 
                  V_OSEventListPtr osevent = Some v' /\
                  joinsig qid absmq mqls' mqls /\
                  RLH_ECBData_P enode absmq /\
                  ECBList_P v' tl l' ecbls' mqls' tcbls 
          end
      end
  end.

Definition AECBList
  (l : list EventCtr) (ecbls : list EventData)   (els: EcbMod.map) (tcbls : TcbMod.map)
  : asrt := 
  (EX p, (GV OSEventList @ (Tptr OS_EVENT) |-> p **  
            evsllseg p Vnull l ecbls) **[| ECBList_P p Vnull l ecbls els tcbls|]). 

(*-----------------------------------------------------------------------------------*)
(* Inv used in certifying OS *)
(*-----------------------------------------------------------------------------------*)
Definition isr_is_prop isr is:=
  forall (x:hid), ~(List.In x is) -> isr x =false.

Definition A_isr_is_prop := EX isr is, Aisr isr ** Ais is ** [|isr_is_prop isr is|].  

Fixpoint ptr_in_tcbdllseg (p:val) (head:val) (l:list vallist) : Prop :=
  match l with
    | nil => False
    | h::l' =>
      if (beq_val p head)
      then True
      else
        match (V_OSTCBNext h) with
          | None => False
          | Some next => ptr_in_tcbdllseg p next l'
        end
  end.

Definition tcblist (head headprev tail tailnext:val) (l:list vallist) (rtbl:vallist) (tcbls:TcbMod.map) :=
  tcbdllseg head headprev tail tailnext l ** [|TCBList_P head l rtbl tcbls|].

(*used in the new inv, hide the tcbdllseg*)
Definition ptr_in_tcblist := ptr_in_tcbdllseg.

(*ptrs of the dll does not change*)
Definition same_prev_next (vl1 vl2 : vallist) : Prop :=
  match (V_OSTCBNext vl1), (V_OSTCBNext vl2) with
    | (Some p1), (Some p2) =>
      p1 = p2 /\
      match (V_OSTCBPrev vl1), (V_OSTCBPrev vl2) with
        | (Some p3), (Some p4) => p3 = p4
        | _, _ => False
      end
    | _, _ => False
  end.

Definition TCB_Not_In ct head tcbl :=
 [|(~ptr_in_tcblist ct head tcbl) /\ exists a, ct = Vptr (a,Int.zero)|].


(* AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree ** *)
Definition AOSTCBList' (p1 p2: val) (l1 l2:list vallist) (rtbl : vallist)
           (hcurt:addrval)(tcbls : TcbMod.map) (pf : val) :=
  (
    EX tail1 tail2 tcbls1 tcbls2,
    (GV OSTCBList @ (Tptr OS_TCB) |-> p1) **
    tcbdllseg p1 Vnull tail1 p2 l1 ** 
    (GV OSTCBCur @ (Tptr OS_TCB) |-r-> p2) **
    tcbdllseg  p2 tail1 tail2 Vnull l2 **
    [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
    [| join tcbls1 tcbls2 tcbls|] **
    [| TCBList_P p1 l1 rtbl tcbls1 |]**
    [| TCBList_P p2 l2 rtbl tcbls2 |]**
    tcbdllflag p1 (l1 ++ l2) **
    [|p2 <> pf|]
  ) \\//
  (
    EX tail,
    (
      GV OSTCBList @ (Tptr OS_TCB) |-> p1 **
      GV OSTCBCur @ (Tptr OS_TCB) |-r-> p2 **
      tcblist p1 Vnull tail Vnull (l1++l2) rtbl tcbls **
      TCB_Not_In p2 p1 (l1 ++ l2) **
      tcbdllflag p1 (l1 ++ l2) **
      [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
      [|p2 = pf|]
    )
  ) .
  

Definition isflag (v : val) := v = Vint32 (Int.repr 1%Z) \/ v = Vint32 (Int.repr 0%Z).

Definition isloc (v: val) :=
  (
    v = Vint32 (Int.repr __Loc_normal) \/
    v = Vint32 (Int.repr __Loc_objcre) \/
    v = Vint32 (Int.repr __Loc_objdel)  
  ).

Definition OSLInv t lg :=
  EX v loc ptr,  
    PV (get_off_addr t flag_off) @ Tint8 |-r-> v **
    PV (get_off_addr t loc_off) @ Tint8 |-r-> loc ** 
    PV (get_off_addr t ptr_off) @ (Tptr OS_EVENT) |-r-> ptr ** 
    [| lg = logic_val  v :: logic_val loc :: logic_val ptr :: nil /\ 
         isflag v /\ isloc loc /\ isptr ptr |].   
  
Definition AOSTCBList (p1 p2: val) (l1 l2:list vallist) (rtbl : vallist) (hcurt:addrval)(tcbls : TcbMod.map) := 
  EX tail1 tail2 tcbls1 tcbls2,
    (GV OSTCBList @ (Tptr OS_TCB) |-> p1) **
      tcbdllseg p1 Vnull tail1 p2 l1 ** 
      (GV OSTCBCur @ (Tptr OS_TCB) |-r-> p2) **
      tcbdllseg  p2 tail1 tail2 Vnull l2 **
      [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** 
      [| join tcbls1 tcbls2 tcbls|] **
      [| TCBList_P p1 l1 rtbl tcbls1 |]**
      [| TCBList_P p2 l2 rtbl tcbls2 |].



(*******************************************************************************)
(********************* DEFINITIONS ABOUT SERVICE OBJ *********************)
(*******************************************************************************)

Definition objaux_node a v1 v2 := 
      PV (get_off_addr a loc_off) @ Tint8 |-r-> v1 **  
      PV (get_off_addr a ptr_off) @ (Tptr OS_EVENT) |-r-> v2 ** 
      [| rule_type_val_match Tint8 v1 = true |] ** 
      [| rule_type_val_match (Tptr OS_EVENT) v2 = true |]. 

Fixpoint llsegobjaux 
         (head tailnext: val) 
         (l: list vallist)
         (locmp: AuxLocMod.map) 
         (ptrmp: AuxPtrMod.map)  
         (next: vallist->option val) :=
  match l with
    nil => [| head = tailnext |]  ** [| l = nil |] ** [| locmp = emp /\ ptrmp = emp |]  
  | vl :: l' => (
    EX a vn v1 v2 locmp' ptrmp',
      [| head = Vptr a |] **
      [| next vl = Some vn |] ** 
      objaux_node a v1 v2 ** 
      [| joinsig a v1 locmp' locmp |] ** 
      [| joinsig a v2 ptrmp' ptrmp |] ** 
      llsegobjaux vn tailnext l' locmp' ptrmp' next 
    )
  end. 

(*
   - The following definition generates the assertion for the corresopndence between
      the abstract and concrete representations of the auxiliary variables for the
      current program locations and the currently handled ECBs for the tasks.
      On the concrete level, the auxiliary variables for the current program location
      and the currently handled ECB of each task are stored in the task control block (TCB)
      for the task.
    - The parameter **tcbh** represents the head pointer for the linked list of TCBs.
    - The parameter **vll** is a list. Each element of this list is another list that represents
       the values for the members of a specific TCB. 
 *) 
Definition tcbllsegobjaux
  (tcbh: val) (vll: list vallist) (locmp: AuxLocMod.map) (ptrmp: AuxPtrMod.map) :=  
  llsegobjaux tcbh Vnull vll locmp ptrmp V_OSTCBNext.   



(* The following function is used to generate the representation predicates
     for the service objects *) 
Definition AObjArr (vll :list vallist) := 
 EX l, GV obj_arr @ (Tptr service_obj_t) |-> (Vptr l) **
  Aarray_new l (Tarray service_obj_t (nat_of_Z (MAX_OBJ_NUM))) vll ** 
  [| new_array_type_vallist_match service_obj_t vll /\ length vll = (nat_of_Z MAX_OBJ_NUM)|]. 

(*-----------------------------------------------------------------------------------*)
(*  members of a service object                                                                       *)
(*-----------------------------------------------------------------------------------*)
Definition V_ObjAttr (vl:vallist) := nth_val 0 vl.
Definition V_ObjPtr (vl:vallist) := nth_val 1 vl.  

(* If a service object contains a valid reference to a kernel object,
     then the referenced kernel object is active (allocated and initialized). *) 
Definition RH_OBJ_ECB_P (ecbls: EcbMod.map) (sobjs: ObjMod.map) := 
  forall idx oid att, 
    get sobjs idx = Some (objid oid, att) ->
    exists n wls, get ecbls oid = Some (abssem n, wls).  

(* The following definition is an invariant condition that describes the 
     correspondence between the abstract representation (absobj) and 
     the concrete representation (vl) of a service object. *)   
Definition RHL_OBJ_P vl (absobj: obj_id * int32) (vhold: addrval) := 
  forall oid att, 
    absobj = (oid, att) ->
    (
      V_ObjAttr vl = Some (Vint32 att) /\ 
        (
          (exists id, oid = objid id /\ V_ObjPtr vl = Some (Vptr id) /\ id <> vhold) \/ 
            (oid = objholder /\ V_ObjPtr vl = Some (Vptr vhold)) \/
            (oid = objnull /\ V_ObjPtr vl = Some Vnull) 
        )
    ).

(* The following definition is an invariant condition that describes the
     correspondence between the abstract and concrete representations
     of all service objects. *) 
Fixpoint ObjArray_P (v: val) (l: list vallist) (objs: ObjMod.map) (vhold: addrval) 
  {struct l} : Prop :=
  match l with
  | nil => objs = emp 
  | vl :: l' => (
                 exists idx objs' absobj v',
                   v = Vint32 idx /\
                     v' = Vint32 (Int.add idx Int.one) /\
                     joinsig idx absobj objs' objs /\ 
                     RHL_OBJ_P vl absobj vhold /\
                     ObjArray_P v' l' objs'  vhold 
               )
  end.

Definition AObjs objl absobjs ecbls (vhold: addrval) :=  
  AObjArr objl **  
    [| ObjArray_P (Vint32 Int.zero) objl absobjs vhold |] **
    [| RH_OBJ_ECB_P ecbls absobjs |]. 

Notation HObjs objs := (Aabsdata absobjsid (absobjs objs)). 


Require Import seplog_pattern_tacs. 

Definition obj_ref objs ptr := exists idx att, get objs idx = Some (objid ptr, att).  

(* There is at most one service object that references the same kernel object. *) 
Definition objref_distinct objs :=
  forall ptr idx1 idx2 att1 att2, 
    get objs idx1 = Some (objid ptr, att1) ->
    get objs idx2 = Some (objid ptr, att2) -> 
    idx1 = idx2. 


(* The pointer **ptr** points to an active kernel object
      (specifically, a kernel semaphore). *)  
Definition is_kobj ecbls ptr := exists n wl, get ecbls ptr = Some (abssem n, wl).


(* There is at most one task that is attempting at creating service objects based on
     the same underlying ECB (kernel object). *)
Definition objcre_nodup (locmp: AuxLocMod.map) (ptrmp: AuxPtrMod.map) :=
  forall t1 t2 ptr1 ptr2,
    t1 <> t2 -> 
    get locmp t1 = Some (Vint32 (Int.repr __Loc_objcre)) -> 
    get locmp t2 = Some (Vint32 (Int.repr __Loc_objcre)) ->
    get ptrmp t1 = Some (Vptr ptr1) -> 
    get ptrmp t2 = Some (Vptr ptr2) ->   
    ptr1 <> ptr2.  


(* There is at most one task that is attempting to delete the underlying ECB
     for (kernel object) a service object. *) 
Definition objdel_nodup (locmp: AuxLocMod.map) (ptrmp: AuxPtrMod.map) :=
  forall t1 t2 ptr1 ptr2,
    t1 <> t2 -> 
    get locmp t1 = Some (Vint32 (Int.repr __Loc_objdel)) ->
    get locmp t2 = Some (Vint32 (Int.repr __Loc_objdel)) ->
    get ptrmp t1 = Some (Vptr ptr1) -> 
    get ptrmp t2 = Some (Vptr ptr2) -> 
    ptr1 <> ptr2. 


(*
  - The following definition is the main invariant condition that depends on
     the current program points and the currently handled ECB by the tasks.
  - The current program point and the currently handled ECB by each task
     are represented using auxiliary variables with fractional permission.
  - The parameter **locmp** is an abstract representation of the correspondence
     between tasks and their current program locations.
  - The parameter **ptrmp** is an abstract representation of the correspondence
     between tasks and their currentnly handled ECBs.
 *) 
Definition OBJ_AUX_P
  (locmp: AuxLocMod.map) (ptrmp: AuxPtrMod.map) ecbls fecbh fecbvl (objs: ObjMod.map)  := 
  
  forall (t: tid) (ptr: addrval), 
    get ptrmp t = Some (Vptr ptr) ->
    (
      (get locmp t = Some (Vint32 (Int.repr __Loc_objcre)) /\  
         (~ptr_in_ecblist (Vptr ptr) fecbh fecbvl) /\ 
         (~obj_ref objs ptr) /\
         is_kobj ecbls ptr) 
      \/
        (get locmp t = Some (Vint32 (Int.repr __Loc_normal)) /\
           (is_kobj ecbls ptr \/ ptr_in_ecblist (Vptr ptr) fecbh fecbvl))
      \/
        (get locmp t = Some (Vint32 (Int.repr __Loc_objdel)) /\ 
          is_kobj ecbls ptr /\
          (~exists t,
               get locmp t = Some (Vint32 (Int.repr __Loc_objcre)) 
               /\ get ptrmp t = Some (Vptr ptr))
         /\ (~obj_ref objs ptr))
    ). 

Parameter vhold_addr : addrval.

(* The following definition collects the invariant conditions relevant for the
     service objects. *) 
Definition AOBJ objl absobjs ecbls (vhold: addrval) tcblh tcbvl fecbh fecbvl  :=
  EX locmp ptrmp,
      HObjs absobjs **
      AObjs objl absobjs ecbls vhold ** 
      [| vhold = vhold_addr |] ** 
      [| OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl absobjs |] ** 
      [| objcre_nodup locmp ptrmp |] ** 
      [| objdel_nodup locmp ptrmp |] **  
      [| objref_distinct absobjs |] ** 
      tcbllsegobjaux tcblh tcbvl locmp ptrmp. 



Definition OldOSInvWL' ct lg:=
  EX eventl msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) t vhold
         ptfree lfree fecbh (* ptls *), 
          AOSEventFreeList fecbh eventl ** 
          AECBList ectrl msgql ecbls  tcbls ** (* msgq *)
          AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls (* ptls  *)vhold ** 
          AOSIntNesting ** (* tables *)
          AOSTCBList_old p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
          AOSTCBFreeList ptfree lfree**
          AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
          HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct **  AGVars **
          (EX objl absobjs, AOBJ objl absobjs ecbls vhold p1 (tcbl1 ++ (tcbcur::tcbl2)) fecbh eventl) **  
          [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
          [| RH_CurTCB ct tcbls|] **
          A_isr_is_prop **
          tcbdllflag p1 (tcbl1 ++ (tcbcur::tcbl2)) ** LINV OSLInv ct lg.

Definition OldOSInvWL ct lg:=
  EX eventl msgql ectrl ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls (tcbls:TcbMod.map) t vhold
         ptfree lfree fecbh (* ptls *), 
          AOSEventFreeList fecbh eventl ** 
          AECBList ectrl msgql ecbls  tcbls ** (* msgq *)
          AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls (* ptls  *)vhold ** 
          AOSIntNesting ** (* tables *)
          AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
          AOSTCBFreeList ptfree lfree**
          AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
          HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct **  AGVars **
          (EX objl absobjs, AOBJ objl absobjs ecbls vhold p1 (tcbl1 ++ (tcbcur::tcbl2)) fecbh eventl) **  
          [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
          [| RH_CurTCB ct tcbls|] **
          A_isr_is_prop **
          tcbdllflag p1 (tcbl1 ++ (tcbcur::tcbl2)) ** p_local OSLInv ct lg.


(* The complete definition for the global invariant.
     Here, the line with AOBJ is for the service objects.
     The other conditions are for the originally performed formal verification
     for the uC/OS-II microkernel. *) 
Definition OSInv :=
  EX eventl msgql ectrl
    ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls t ct vhold ptfree lfree fecbh (* ptls *), 
       AOSEventFreeList fecbh eventl ** 
       AECBList ectrl msgql ecbls  tcbls ** (* msgq *)
       AOSMapTbl ** AOSUnMapTbl ** AOSTCBPrioTbl ptbl rtbl tcbls (* ptls  *)vhold ** 
       AOSIntNesting ** (* tables *)
       AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
       AOSTCBFreeList' ptfree lfree ct tcbls**
       AOSRdyTblGrp rtbl rgrp ** AOSTime (Vint32 t) **(* tcblist & rdy table *)
       HECBList ecbls ** HTCBList tcbls ** HTime t ** HCurTCB ct **  AGVars **
       (EX objl absobjs, AOBJ objl absobjs ecbls vhold p1 (tcbl1 ++ (tcbcur::tcbl2)) fecbh eventl) **  
       [| RH_TCBList_ECBList_P ecbls tcbls ct|] **
       A_isr_is_prop.


Definition atoy_inv' := (EX i, GV OSIntToyCount@ (Tint32) |-> Vint32 i).  
Definition atoy_inv := atoy_inv' ** A_isr_is_prop.  

Definition aemp_isr_is := Aemp ** A_isr_is_prop. 

Fixpoint eq_dllflag l1 l2:=
  match l1,l2 with
    | nil,nil => True
    | vl1::l1',vl2::l2' =>
      V_OSTCBNext vl1 = V_OSTCBNext vl2 /\ V_OSTCBflag vl1 = V_OSTCBflag vl2 /\ eq_dllflag l1' l2'
    | _,_ => False
  end.


Lemma eq_dllflag_refl: forall l, eq_dllflag l l.
Proof.
  induction l.
  simpl;auto.
  simpl.
  splits;auto.
Qed.

Lemma tcbdllflag_hold_middle:
  forall l1 l2 node node',
    eq_dllflag (node::nil) (node'::nil) -> eq_dllflag (l1++node::l2) (l1++node'::l2).
Proof.
  induction l1.
  intros.
  simpl in H.
  simpl.
  destruct H.
  destruct H0.
  splits;auto.
  apply eq_dllflag_refl.
  intros.
  simpl.
  splits;auto.
Qed.

Lemma tcbdllflag_hold:
  forall l1 P head l2,
    eq_dllflag l1 l2 ->
    tcbdllflag head l1 ** P ==> tcbdllflag head l2 ** P.  
Proof.
  unfold tcbdllflag.
  inductions l1.
  intros.
  simpl in H.
  unfold tcbdllflag in *.
  destruct l2; tryfalse.
  auto.
  intros.
  destruct l2.
  simpl in H; tryfalse.
  unfold dllsegflag in *; fold dllsegflag in *.
  simpl in H.
  simpljoin.
  sep normal in H0.
  sep normal.
  sep destruct H0.
  exists x x0.
  sep cancel 1%nat 1%nat.
  sep split in H0.
  sep split; auto.
  sep cancel 1%nat 1%nat.
  eapply IHl1; eauto.
  rewrite H in H3.
  auto.
Qed.

Lemma disj_split:
  forall s p q r, (s |= (p \\// q) ** r <-> s |= (p ** r) \\// (q ** r)). 
Proof.
  split.
  intros.
  simpl in H.
  simpljoin.
  destruct H3.
  left.
  do 6 eexists.
  splits; eauto.
  right.
  do 6 eexists.
  splits; eauto.
  intros.
  destruct H.
  sep cancel 2%nat 2%nat.
  left; auto.
  sep cancel 2%nat 2%nat.
  right; auto.
Qed.


(* ** ac: Locate PV_combine_ro_frm. *)
Import sep_combine_lemmas.

Lemma read_only_merge_all:
  forall s x t v1 v2 P,
    rule_type_val_match t v1 = true->
    rule_type_val_match t v2 = true->
    s |= (PV x @  t |-r->  v1) **
      (PV x @  t |-r->  v2) ** P  ->
    s |= PV x @  t |-> v1 ** P /\ v1 = v2.                                       
Proof.
  (* ** ac: Print rule_type_val_match. *)
  intros.
  (* ** ac: Check PV_combine_ro_frm. *)
  eapply PV_combine_ro_frm in H1.
  sep split in H1.
  split.
  auto.
  lets Hx : rule_type_val_match_encode_val_eq H H0 H2.
  auto.
Qed.

Lemma rule_type_val_match_encode_val_length_eq :
  forall t v1 v2 vl1 vl2,
    rule_type_val_match t v1 = true ->
    rule_type_val_match t v2 = true ->
    encode_val t v1 = vl1 ->
    encode_val t v2 = vl2 ->
    length vl1 = length vl2.
Proof.
  intros.
  destruct t, v1, v2;
    simpl in H, H0; tryfalse;
    simpl in H1, H2; try(destruct a); try (destruct a0); substs; auto.
Qed.

Lemma read_only_merge_vptr:
  forall s x t1 t2 v1 v2 P,
    s |= (GV x @ Tptr t1 |-r-> Vptr v1) ** (GV x @ Tptr t2 |-r-> Vptr v2) ** P  -> 
    s |= GV x @ Tptr t1 |-> Vptr v1 ** P /\ v1 = v2.                                       
Proof.
  intros.
  destruct_s s.
  simpl in H.
  simpljoin.
  unfold emposabst in *; substs.
  rewrite H13 in H22.
  inverts H22.

  unfold mapstoval in H14, H23.
  simpljoin.

  assert(length (encode_val (Tptr t1) (Vptr v2)) = length (encode_val (Tptr t1) (Vptr v1))).
  {
    eapply rule_type_val_match_encode_val_length_eq; eauto.
    simpl; auto.
    simpl; auto.
  }
  (* ** ac: Print ptomvallist. *)
  (* ** ac: Print encode_val. *)
  assert(x21 = x6).
  geat.
  assert(x14 = x0).
  geat.
  assert(x4 = o).
  geat.
  assert(x10 = x4).
  geat.
  substs.

  assert(exists xx, join x0 x6 xx).
  clear - H0 H5.
  geat.
  destruct H1.

  symmetry in H.


  Lemma ptomvallist_false_sub_vl_eq :
    forall vl1 vl2 l m1 m2 m,
      ptomvallist l false vl1 m1 ->
      ptomvallist l false vl2 m2 ->
      length vl1 = length vl2 ->
      Maps.sub m1 m -> Maps.sub m2 m ->
      vl1 = vl2.
  Proof.
    inductions vl1; intros.
    destruct vl2; auto.
    simpl in H1; inversion H1.
    
    destruct vl2.
    simpl in H1; inversion H1.

    simpl in H1; inverts H1.
    simpl in H; destruct l.

    do 3 destruct H; destruct H1.
    simpl in H0; do 3 destruct H0; destruct H6.

    unfold ptomval in H1, H6; substs.
    assert(a = m0).
    unfolds in H2; destruct H2.
    unfolds in H3; destruct H3.
    lets Hx1: HalfPermMap.map_join_assoc H H1.
    lets Hx2: HalfPermMap.map_join_assoc H0 H2.
    simpljoin.

    Require Import mem_join_lemmas.
    
    lets Hx: mem_join_sig_eq H6 H3; auto.
    substs.
    assert(vl1 = vl2).
    assert(Maps.sub x0 m).
    unfold Maps.sub.
    unfold Maps.sub in H2.
    geat.
    assert(Maps.sub x2 m).
    unfold Maps.sub.
    unfold Maps.sub in H3.
    geat.
    apply IHvl1 with (m1:=x0) (m2:=x2) (m:=m) (l:=(b,o+1)); auto.
    substs; auto.
  Qed.
  
  assert ((encode_val (Tptr t1) (Vptr v1)) = (encode_val (Tptr t1) (Vptr v2))).
  {
    eapply ptomvallist_false_sub_vl_eq; eauto.
    instantiate (1:= x2).
    unfold Maps.sub.
    exists x6.
    auto.
    unfold Maps.sub.
    clear - H1.
    geat.
  } 

  assert(Vptr v1 = Vptr v2).
  {
    eapply rule_type_val_match_encode_val_eq; eauto.
    simpl; auto.
    simpl; auto.
  }
  inverts H8.

  simpl.
  split; auto.
  exists x2 x7 m empabst o o.
  splits; auto.
  jeauto2.
  clear - H5 H0 H1.
  geat.
  do 7 eexists.
  splits; auto.
  Focus 3.
  eexists.
  splits; auto.
  eauto.
  unfolds; auto.
  jeauto2.
  jeauto2.
  (* ** ac: Check os_inv.ptomvallistr_ptomvallist. *)
  unfolds.
  eexists.
  split; auto.
  eapply ptomvallistr_ptomvallist.
  exact H4.
  exact H3.
  eauto.
  unfolds; auto.
Qed.


Lemma tcbfreelist_disj_tcblist:
  forall pfree fls  ct x y l s P,
    s |= AOSTCBFreeList pfree fls ** tcbdllseg (Vptr ct) x y Vnull l ** P 
    -> pfree <> (Vptr ct).
Proof.
  intros.
  intro; substs.

  destruct l.
  unfold tcbdllseg in H.
  simpl dllseg in H; sep split in H; tryfalse.

  destruct fls.
  unfold AOSTCBFreeList in H.
  unfold assertion.sll in H.
  simpl sllseg in H.
  sep split in H; tryfalse.

  unfold AOSTCBFreeList in H.
  unfold assertion.sll in H.
  unfold tcbdllseg in H.
  unfold sllseg in H; fold sllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H.
  do 2 destruct H.
  sep split in H.
  sep lifts (1::3::nil)%nat in H.
  apply node_OS_TCB_dup_false in H; tryfalse.
Qed.

Lemma flag_merege_false :
  forall a P s,
    s |= PV a @ Tint8 |-r-> (V$ 1) ** PV a @ Tint8 |-r-> (V$ 0) ** P -> False. 
Proof.
  intros.
  destruct_s s.
  simpl in H.
  repeat (let a:= fresh in destruct H as [a H]).
  destruct H10; unfolds in H22.
  destruct H21; unfolds in H23.
  substs.
  unfolds in H10; destruct H10; destruct H2.
  unfolds in H21; destruct H21; destruct H5.
  apply map_join_comm in H7.
  apply map_join_comm in H18.

  pose proof map_join_assoc H18 H7.
  do 2 destruct H8.
  substs.
  simpl in H3.
  simpl in H6.
  destruct (addrval_to_addr a).
  destruct H6; destruct H2; destruct H2; destruct H5.
  destruct H3; destruct H3; destruct H3; destruct H13.
  substs.
  pose proof map_join_emp x.
  pose proof map_join_deter H2 H6; substs.
  pose proof map_join_emp x2.
  pose proof map_join_deter H3 H11; substs.
  clear H6 H18 H2 H11 H7 H3.
  
  lets Hx: ptomvalr_join_eq H5 H13 H10.
  inverts Hx.
Qed.

Lemma read_only_merge_vptreq:
  forall s x t v P,
      s |= (GV x @ Tptr t |-r-> Vptr v) **
        (GV x @ Tptr t |-r-> Vptr v) ** P  <->
      s |= GV x @ Tptr t |-> Vptr v ** P .                                       
Proof.
  intros.
  split; intros.
  lets Hx: read_only_merge_vptr H; destruct Hx; auto.
  apply read_only_split_vptr; auto.
Qed.


Lemma inv_change':
  forall P t lg',
    OSInv ** p_local OSLInv t (logic_val (V$1) :: lg') ** P <==> OldOSInvWL' t (logic_val (V$1) :: lg') ** P.
Proof.
  intros.
  split.
  intros.
  sep cancel 3%nat 2%nat.
  unfold OldOSInvWL'.
  unfold OSInv in H.

  (* *)
  unfold AOBJ in H .
  unfold AOBJ.

  sep normal in H.
  sep destruct H.
  sep_lifts_trms_in H AOSTCBList'.
  unfold AOSTCBList' in H.
  apply disj_split in H.
  destruct H.
  sep normal in H.

  unfold p_local in H.
  unfold CurTid in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold init_lg in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destructs H0.
  inverts H0.
  destruct H1.
  subst x4.
  sep_lifts_skp_in H ((OSTCBCur, _N_ 1), (OSTCBCur, _N_ 0)). 
  (* sep lifts (9::6::nil)%nat in H. *)
  apply read_only_merge_vptr in H.
  destruct H as (H & Ha).
  subst x13.
  unfold LINV. unfold OSLInv.
  sep semiauto.
  2: {
    unfold1 TCBList_P in H4.
    simpljoin.
    unfolds.
    clear H.
    (* destruct x25 as [[]].  *)
    match goal with
      xx : priority * taskstatus |- _ =>
      destruct xx as [[]]
    end. 
    unfold get, sig, join in *; simpl in *.
    unfold get, sig, join in *; simpl in *.
    do 2 eexists.
    eapply TcbMod.join_get_r.
    eauto.
    eapply TcbMod.join_get_l.
    eauto.
    eapply TcbMod.get_a_sig_a.
    inverts H1.
    apply CltEnvMod.beq_refl.
  }

  unfold AOSTCBList_old.
  sep normal.
  sep eexists.
  sep semiauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel tcbdllflag.
  sep cancel AOSEventFreeList.
  sep cancel AECBList.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp.

  sep cancel AObjs.
  sep cancel tcbllsegobjaux.
  
  unfold AOSTCBFreeList' in H.
  unfold AOSTCBFreeList.
  sep cancel (Agvarmapsto OSTCBFreeList).
  destruct H.
  unfold TCBFree_Not_Eq in H.
  sep auto.
  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H1.
  tryfalse.
  eauto.
  eauto.
  auto.

  eauto. (* objref_distinct *) 
  auto.
  auto.
  auto.
  
  unfold p_local in H.
  unfold CurTid in H.
  unfold LINV in H.
  unfold OSLInv in H.
  unfold TCB_Not_In in H.
  sep normal in H.
  sep destruct H.
  sep split in H.

  inverts H0.
  destruct H1.
  destruct H1.
  subst x4.
  sep_lifts_skp_in H ((OSTCBCur, _N_ 1), (OSTCBCur, _N_ 0)).   
  (* sep lifts (8::6::nil)%nat in H. *) 
  apply read_only_merge_vptr in H.
  destruct H as (H & Ha).
  subst t.
  sep_lift_context_in H tcblist.
  (* sep lift 7%nat in H. *)
  inverts H11.  (* equation about logic_val *) 
  sep lift 3%nat in H. (* flag_off *) 
  subst x14.
  unfold AOSTCBFreeList' in H.
  destruct H2.
  inverts H2.
  sep normal in H.
  sep_lift_context_in H Adisj.
  (* sep lift 26%nat in H. *)
  apply disj_split in H.
  destruct H.
  unfold TCBFree_Not_Eq in H.
  sep normal in H.
  sep split in H.
  tryfalse.
  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  destruct H2.
  destruct H11; subst.
  sep_lifts_skp_in H ((flag_off, _N_ 1), (flag_off, _N_ 0)). 
  (* sep lifts (9::6::nil)%nat in H. *)
  eapply flag_merege_false in H.
  tryfalse.
  
  (****)
  intros.
  sep cancel 2%nat 3%nat.
  unfold OSInv, p_local, CurTid, LINV, OSLInv.
  unfold OldOSInvWL' in H.
  unfold AOSTCBList_old in H.
  
  unfold LINV, OSLInv, init_lg in H.
  sep semiauto.
  sep_lift_context AOSTCBList'.
  (* sep lift 14%nat. *)
  unfold AOSTCBList'.
  eapply disj_split.
  left.
  sep normal.
  subst x4.
  sep_lifts_skp_in H (AOSTCBFreeList, (tcbdllseg, _N_ 1)). 
  (* sep_lifts_trms_in H (AOSTCBFreeList, _N_ 10). *)
  lets Hxx : tcbfreelist_disj_tcblist H.
  sep semiauto.
  sep cancel AOSEventFreeList.
  sep cancel AECBList.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp.
  sep cancel 2%nat 4%nat.
  sep cancel (Agvarmapsto OSTCBList).
  (* sep cancel 6%nat 1%nat. *)
  sep cancel tcbdllflag.
  (* sep lift 6%nat. *)
  (* sep lift 7%nat in H.  *)
  sep_lift_context_in H (Agvarmapsto OSTCBCur).
  apply read_only_merge_vptreq in H.
  unfold AOSTCBFreeList in H.
  (* sep lift 11%nat. *)
  unfold AOSTCBFreeList'.
  sep_lift_context Adisj.
  (* sep lift 2%nat. *)
  eapply disj_split.
  left.
  unfold TCBFree_Not_Eq.

  
  sep auto.
  auto.
  eauto.
  eauto.
  eauto.
  auto.
  auto.
  splits; auto.
Qed.


Lemma inv_change_old:
  forall P t lg,
    OldOSInvWL t lg ** P <==> OldOSInvWL' t lg  ** P.
Proof.
  intros.
  unfold OldOSInvWL in *.
  unfold OldOSInvWL' in *.
  split;intros.
  sep semiauto.
  unfold p_local in *.
  unfold CurTid in *.
  unfold AOSTCBList in *.
  unfold AOSTCBList_old in *.
  sep normal in H.
  sep destruct H.
  sep lift 4%nat in H.
  sep split in H.
  simpljoin.
  apply read_only_merge_vptr in H.
  destruct H.
  sep auto;eauto.
  sep semiauto.
  unfold p_local in *.
  unfold AOSTCBList in *.
  unfold AOSTCBList_old in *.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  sep split in H.
  simpljoin.
  apply read_only_merge_vptreq in H.
  unfold CurTid.
  sep auto;eauto.
Qed.

Lemma inv_change:
    forall P t lg',
      OSInv ** p_local OSLInv t (logic_val (V$1) :: lg') ** P <==> OldOSInvWL t (logic_val (V$1) :: lg')  ** P. 
Proof.
  intros.
  unfold OSInv,OldOSInvWL.
  unfold AOSTCBList.
  split;intros.
  apply inv_change' in H.
  apply inv_change_old;auto.
  apply inv_change'.
  apply inv_change_old;auto.
Qed.

Import DeprecatedTactic.
Lemma noabs_oslinv:
  NoAbs OSLInv.
Proof.
  unfolds.
  intros.
  unfold CurLINV in *.
  unfold LINV in *.
  unfold CurTid in *.
  unfold satp in *.
  intros.
  lets Hx:H aop.
  clear H.
  sep normal in Hx.
  sep destruct Hx.
  sep normal.
  exists x x0.
  simpl in Hx.
  simpl.
  mytac.
  do 6 eexists;splits;eauto.
  instantiate (2:=emp).
  clear.
  join auto.
  do 7 eexists;splits;eauto.
  join auto.
  eexists;splits;eauto.
  unfolds;auto.
  unfolds;auto.
  do 6 eexists;splits;eauto.
  instantiate (2:=emp).
  join auto.


  destruct t.
  simpl in *.
  exists x26. exists x27. exists x28. 
  do 6 eexists. 
  splits; eauto.
  join auto.
  split. auto. join auto.
  exists x35. exists x36. eexists. 
  do 3 eexists.
  splits; eauto.
  join auto.
  split. auto. join auto.
  exists x41. exists x42. eexists.
  do 3 eexists.
  splits; eauto.
  join auto.
  split. auto. unfolds; auto. unfolds; auto. 
  exists x20. exists x21.
  do 4 eexists.
  splits; auto.
  instantiate (1:=O').
  join auto.
  split; auto. 
  splits; auto. 
  unfolds; auto. 

Qed.

  
Close Scope int_scope.
Close Scope Z_scope.
