
Require Import include_frm.
Require Import base_tac.
Require Import os_inv.
Require Import os_code_defs.
Require Import abs_op.
Require Import sep_auto.
Require Import Maps.

Require Import mem_join_lemmas.
Require Import lemmas_for_inv_prop.

(* lemmas specific on memory(HalfPermMap) *)

Lemma mem_sub_sig_eq :
  forall l a b p (m:mem),
    sub (sig l (p, a)) m ->
    sub (sig l (p, b)) m ->
    a = b.
Proof.
  unfold sub; intros.
  destruct H, H0.
  eapply mem_join_sig_eq; eauto.
Qed.


Ltac destruct_get :=
  let a := fresh in
  match goal with
  | H : (match ?X with | Some _ => _ | None => _ end) |- _ => destruct X eqn : a; tryfalse; destruct_get
  | _ => idtac
  end.

Lemma osabst_join_sig_eq :
  forall l a b (o:osabst) o1 o2,
    join (sig l a) o1 o ->
    join (sig l b) o2 o ->
    a = b.
Proof.
  intros.
  pose proof H l.
  pose proof H0 l.
  rewrite OSAbstMod.get_sig_some in *.
  destruct_get.
  substs; auto.
Qed.


Lemma osabst_sub_sig_eq :
  forall l a b (o:osabst),
    sub (sig l a) o ->
    sub (sig l b) o ->
    a = b.
Proof.
  unfold sub; intros.
  destruct H, H0.
  eapply osabst_join_sig_eq; eauto.
Qed.

Lemma mem_join_sig_sub_eq :
  forall a b l p m1 m1' m2 m2' (m:mem),
    join (sig l (p, a)) m1 m2 ->
    join (sig l (p, b)) m1' m2' ->
    sub m2 m -> sub m2' m ->
    a = b.
Proof.
  unfold sub; intros.
  destruct H1, H2.
  lets Hx1: HalfPermMap.map_join_assoc H H1.
  lets Hx2: HalfPermMap.map_join_assoc H0 H2.
  destruct Hx1; destruct H3.
  destruct Hx2; destruct H5.
  lets Hx: mem_join_sig_eq H3 H5; auto.
Qed.
(* end *)


(* lemmas on PermMap *)
Lemma join_sub_l {A B T:Type} {MC: PermMap A B T} :
  forall m1 m2 m,
    join m1 m2 m -> sub m1 m.
Proof.
  intros.
  unfold sub.
  eexists; eauto.
Qed.

Lemma join_sub_r {A B T: Type} {MC: PermMap A B T} :
  forall m1 m2 m,
    join m1 m2 m -> sub m2 m.
Proof.
  intros.
  unfold sub.
  eexists.
  apply map_join_comm in H; eauto.
Qed.

Lemma sub_trans {A B T: Type} {MC: PermMap A B T} :
  forall m1 m2 m3,
    sub m1 m2 -> sub m2 m3 -> sub m1 m3.
Proof.
  unfold sub; intros.
  geat.
Qed.

Lemma join_unique {A B T: Type} {MC: PermMap A B T} :
  forall m1 m2 m m',
    join m1 m2 m -> join m1 m2 m' -> m = m'.
Proof.
  intros.
  geat.
Qed.

Lemma eq_join_eq {A B T: Type} {MC: PermMap A B T} :
  forall m1 m1' m2 m2' M M',
    join m1 m2 M ->
    join m1' m2' M' ->
    m1 = m1' -> m2 = m2' ->
    M = M'.
Proof.
  intros; substs.
  eapply join_unique; eauto.
Qed.
(* end *)

 
(*--- auxiliary lemmas ------*)
Lemma sat_sep_conj_elim1 :
  forall e e0 M i l O a P Q,
    (e, e0, M, i, l, O, a) |= P ** Q ->
    exists M1 M2 O1 O2, join M1 M2 M /\ join O1 O2 O /\
                        (e, e0, M1, i, l, O1, a) |= P /\
                        (e, e0, M2, i, l, O2, a) |= Q. 
Proof.
  intros.
  simpl in H; simpljoin.
  do 4 eexists; repeat (split; eauto).
Qed.

Lemma isptr_ecbf_sll :
  forall s head eventl t next,
    s |= ecbf_sll head eventl  t next -> isptr head.
Proof.
  intros.
  unfold ecbf_sll in H.
  destruct eventl.
  simpl in H; simpljoin.
  unfolds; auto.
  unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  destruct_s s.
  simpl in H; simpljoin.
  unfolds; right.
  eauto.
Qed.

Lemma isptr_ecbf_sllseg :
  forall s head eventl t next,
    s |= ecbf_sllseg head Vnull eventl t next -> isptr head.
Proof.
  intros.
  unfold ecbf_sllseg in H.
  destruct eventl.
  simpl in H; simpljoin.
  unfolds; auto.
  unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  destruct_s s.
  simpl in H; simpljoin.
  unfolds; right.
  eauto.
Qed.

Lemma sll_isptr :
  forall vl s head t next,
    s |= sll head vl t next -> isptr head.
Proof.
  inductions vl; intros.
  simpl in H; simpljoin; unfolds; auto.
  simpl in H; simpljoin.
  unfolds; right; eauto.
Qed.

Lemma evsllseg_isptr :
  forall ectrl head msgql s,
    s |= evsllseg head Vnull ectrl msgql -> isptr head.
Proof.
  inductions ectrl; intros.
  - 
    simpl in H; simpljoin; unfolds; auto.
  -
    simpl in H; destruct a; destruct msgql; tryfalse; simpl in H; simpljoin. 
    unfolds; right; eauto.
Qed.

Lemma ecbfsllseg_head_isptr:
  forall l v1 t n P s, 
    s |= ecbf_sllseg v1 Vnull  l t n  ** P  -> isptr v1.                              
Proof.
  inductions l ; intros; simpl in *; tryfalse; simpljoin; 
  unfolds; simpl; eauto.
Qed.

Lemma ecbfsll_head_isptr: forall v l  t n P s, s |= ecbf_sll v l  t n ** P -> isptr v.                                                    
Proof.
  unfold ecbf_sll.
  intros.
  eapply ecbfsllseg_head_isptr.
  eauto.
Qed.

Lemma evsllseg_head_isptr:  
  forall s head l x P, s|= evsllseg head Vnull l x ** P  -> isptr head.
Proof.
  introv Hsat.
  destruct l; simpl evsllseg in *.
  sep split in Hsat.
  simpljoin.
  subst; unfolds; auto.
  destruct x.
  simpl in Hsat; tryfalse.
  sep destruct  Hsat.
  sep split in Hsat.
  simpljoin.
  tryfalse.
  destruct e.
  unfold AEventNode in Hsat.
  destruct e0. 
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  sep destroy Hsat.
  simpljoin.
  unfolds; auto.
  right.
  eexists; eauto.
Qed.
(* end *)


(* tactics *)
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

Ltac mem_join_sub_solver :=
  match goal with
    | H: join ?m _ ?X |- sub ?m ?M =>
      apply join_sub_l in H; apply sub_trans with (m2:=X); auto; mem_join_sub_solver
    | H: join _ ?m ?X |- sub ?m ?M =>
      apply join_sub_r in H; apply sub_trans with (m2:=X); auto; mem_join_sub_solver
  end.

Ltac elim_sep_conj1 H head_H := 
  let a := fresh in
  apply sat_sep_conj_elim1 in H; do 4 destruct H; destruct H as [a H];
  let b := fresh in destruct H as [b H];
  let c := fresh in destruct H as [head_H H].

Ltac mem_sig_eq_solver M := let Hx:= fresh in
  match goal with
    | |- sig ?l1 (?p, ?v1) = sig ?l2 (?p, ?v2) =>
      assert(sub (sig l1 (p, v1)) M) as _H1 by mem_join_sub_solver;
        assert(sub (sig l2 (p, v2)) M) as _H2 by mem_join_sub_solver;
        lets Hx: mem_sub_sig_eq _H1 _H2; rewrite Hx; auto
  end.

Ltac mem_eq_solver1 M :=
  eapply eq_join_eq; eauto; [mem_sig_eq_solver M |try (mem_eq_solver1 M)]; mem_sig_eq_solver M.

Ltac mem_eq_solver2 :=
  match goal with
  | H1: join ?m1 ?m2 ?M1, H2: join ?m3 ?m4 ?M2 |- ?M1 = ?M2 =>
    eapply eq_join_eq; eauto; mem_eq_solver2
  | _ => idtac
  end.

Ltac simpl_sat H :=
  unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.


Ltac mem_eq_solver' MM :=
  eapply eq_join_eq; eauto;[
    match goal with
      | H: forall M : mem, sub ?m1 M -> sub ?m2 M -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (M:= MM)
    end;  mem_join_sub_solver | try (mem_eq_solver' MM)].

Ltac mem_eq_solver MM := try (mem_eq_solver' MM);
    match goal with
      | H: forall M : mem, sub ?m1 M -> sub ?m2 M -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (M:= MM)
    end;  mem_join_sub_solver.

Ltac osabst_eq_solver' OO :=
  eapply eq_join_eq; eauto;[
    match goal with
      | H: forall o0 : osabst, sub ?m1 o0 -> sub ?m2 o0 -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (o0:= OO)
    end;  mem_join_sub_solver | try (osabst_eq_solver' OO)].

Ltac osabst_eq_solver OO := try (osabst_eq_solver' OO);
    match goal with
      | H: forall o0 : osabst, sub ?m1 o0 -> sub ?m2 o0 -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (o0:=OO)
    end;  mem_join_sub_solver.

Ltac un_eq_event_type_solver :=
  match goal with
    | H1: Some _ = Some _ , H2: Some _ = Some _ |- _ =>
      rewrite H1 in H2; inverts H2
  end.

(* end *)
 

(*lemmas*)
Lemma mapstoval_true_vptr_eq :
  forall l a x x' m m' M,
    mapstoval l (Tptr a) true (Vptr x) m -> mapstoval l (Tptr a) true (Vptr x') m' ->
    sub m M -> sub m' M ->
    x = x' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H1, H2; destruct x, x'; simpl in H3, H4; destruct l; simpljoin1.
  unfold ptomval in *; substs.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (true, Pointer b i 0)) M).
  mem_join_sub_solver.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (true, Pointer b0 i0 0)) M).
  mem_join_sub_solver.

  lets Hx: mem_sub_sig_eq H3 H5; inverts Hx.
  split; auto.
  clear H5 H3.
  repeat (eapply eq_join_eq; eauto).
Qed.

Lemma mapstoval_false_vptr_eq :
  forall l a x x' m m' M,
    mapstoval l (Tptr a) false (Vptr x) m -> mapstoval l (Tptr a) false (Vptr x') m' ->
    sub m M -> sub m' M ->
    x = x' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H1, H2; destruct x, x'; simpl in H3, H4; destruct l; simpljoin1.
  unfold ptomval in *; substs.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (false, Pointer b i 0)) M).
  mem_join_sub_solver.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (false, Pointer b0 i0 0)) M).
  mem_join_sub_solver.

  lets Hx: mem_sub_sig_eq H3 H5; inverts Hx.
  split; auto.
  clear H5 H3.
  repeat (eapply eq_join_eq; eauto).
Qed.


Lemma ptomvallist_true_mem_eq :
  forall vl l m m' M,
    sub m M -> sub m' M ->
    ptomvallist l true vl m -> ptomvallist l true vl m' ->
    m = m'.
Proof.
  inductions vl; intros.
  simpl in H1, H2; substs; auto.
  simpl in H1, H2; destruct l; simpljoin1.
  unfold ptomval in H3, H5; substs.
  eapply eq_join_eq; eauto.
  eapply IHvl with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma ptomvallist_false_mem_eq :
  forall vl l m m' M,
    sub m M -> sub m' M ->
    ptomvallist l false vl m -> ptomvallist l false vl m' ->
    m = m'.
Proof.
  inductions vl; intros.
  simpl in H1, H2; substs; auto.
  simpl in H1, H2; destruct l; simpljoin1.
  unfold ptomval in H3, H5; substs.
  eapply eq_join_eq; eauto.
  eapply IHvl with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma mapstoval_true_mem_eq :
  forall l t v v' m m' M,
    sub m M -> sub m' M ->
    mapstoval l t true v m -> mapstoval l t true v' m' -> m = m'.
Proof.
  unfold mapstoval; intros; destruct l; simpljoin1.
  destruct t, v, v'; try (destruct a); try(destruct a0); simpl in H3, H4;
  unfold ptomval in H3, H4; simpljoin1;
  try solve [repeat (eapply eq_join_eq; eauto)];
  try solve [lets Hx: mem_join_sig_sub_eq H1 H2 H H0; tryfalse];
  try solve [lets Hx: mem_sub_sig_eq H H0; tryfalse];
  try solve [mem_eq_solver1 M];
  try solve [eapply ptomvallist_true_mem_eq; eauto].
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
Qed.

Lemma mapstoval_false_mem_eq :
  forall l t v v' m m' M,
    sub m M -> sub m' M ->
    mapstoval l t false v m -> mapstoval l t false v' m' -> m = m'.
Proof. 
  unfold mapstoval; intros; destruct l; simpljoin1.
  destruct t, v, v'; try (destruct a); try(destruct a0); simpl in H3, H4;
  unfold ptomval in H3, H4; simpljoin1;
  try solve [repeat (eapply eq_join_eq; eauto)];
  try solve [lets Hx: mem_join_sig_sub_eq H1 H2 H H0; tryfalse];
  try solve [lets Hx: mem_sub_sig_eq H H0; tryfalse];
  try solve [mem_eq_solver1 M];
  try solve [eapply ptomvallist_false_mem_eq; eauto].
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
Qed.

Fixpoint struct_atom_val_eq' (vl vl':vallist) (d:decllist) :=
  match vl with
    | nil =>
      match vl' with
        | nil => True
        | _ :: _ => False
      end
    | v1 :: t1 =>
      match vl' with
        | nil => False
        | v2 :: t2 =>
          match d with
            | dnil => False
            | dcons id (Tstruct _ _) td => struct_atom_val_eq' t1 t2 td
            | dcons id (Tarray _ _) td => struct_atom_val_eq' t1 t2 td
            | dcons id _ td => v1 = v2 /\ struct_atom_val_eq' t1 t2 td
          end
      end
  end.

Definition struct_atom_val_eq vl vl' t :=
  match t with
    | Tstruct id dl => struct_atom_val_eq' vl vl' dl
    | _ => False
  end.


Local Open Scope Z_scope.
Lemma ptomvallist_true_sub_vl_eq :
  forall vl1 vl2 l m1 m2 m,
    ptomvallist l true vl1 m1 ->
    ptomvallist l true vl2 m2 ->
    length vl1 = length vl2 ->
    sub m1 m -> sub m2 m ->
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
  lets Hx: mem_join_sig_eq H6 H3; auto.
  substs.
  assert(vl1 = vl2).
  assert(sub x0 m).
  unfold sub.
  unfold sub in H2.
  geat.
  assert(sub x2 m).
  unfold sub.
  unfold sub in H3.
  geat.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m:=m) (l:=(b,o+1)); auto.
  substs; auto.
Qed.

Lemma ptomvallist_false_sub_vl_eq :
  forall vl1 vl2 l m1 m2 m,
    ptomvallist l false vl1 m1 ->
    ptomvallist l false vl2 m2 ->
    length vl1 = length vl2 ->
    sub m1 m -> sub m2 m ->
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
  lets Hx: mem_join_sig_eq H6 H3; auto.
  substs.
  assert(vl1 = vl2).
  assert(sub x0 m).
  unfold sub.
  unfold sub in H2.
  geat.
  assert(sub x2 m).
  unfold sub.
  unfold sub in H3.
  geat.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m:=m) (l:=(b,o+1)); auto.
  substs; auto.
Qed.


Lemma mapstoval_true_rule_type_val_match_eq :
  forall l t v v' m m' M,
    rule_type_val_match t v = true -> rule_type_val_match t v' = true ->
    mapstoval l t true v m -> mapstoval l t true v' m' ->
    sub m M -> sub m' M ->
    v = v' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H1, H2; simpljoin1.
  destruct t; destruct v; destruct v'; simpl in H, H0; tryfalse;
  simpl encode_val in H5, H6; try(destruct a); try(destruct a0);
  try solve [split; auto; eapply ptomvallist_true_mem_eq; eauto];
  try solve [lets Hx: ptomvallist_true_sub_vl_eq H5 H6 H4 H3; [simpl; auto | inverts Hx]].

  assert(i = i0).
  simpl in H5, H6; destruct l; unfold ptomval in *; simpljoin1.
  lets Hx: mem_sub_sig_eq H3 H4.

  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.
  apply Zle_is_le_bool in eq1; apply Zle_is_le_bool in eq2.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inverts Hx; substs.
  lets Hx1: byte_repr_int_unsigned_eq eq1 eq2 H1; auto.
  substs.
  split; eauto.
  eapply ptomvallist_true_mem_eq; eauto.
  
  lets Hx: ptomvallist_true_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts Hx; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.

  apply byte_repr_eq in H2.  

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H7; auto.
  do 2 rewrite Int.repr_unsigned in H8; substs.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  lets Hx: ptomvallist_true_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3;
    remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts Hx; substs.
  apply byte_repr_eq in H8.
  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H10; substs.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  
  lets Hx: ptomvallist_true_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.

  lets Hx: ptomvallist_true_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.
Qed.


Lemma mapstoval_false_rule_type_val_match_eq :
  forall l t v v' m m' M,
    rule_type_val_match t v = true -> rule_type_val_match t v' = true ->
    mapstoval l t false v m -> mapstoval l t false v' m' ->
    sub m M -> sub m' M ->
    v = v' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H1, H2; simpljoin1.
  destruct t; destruct v; destruct v'; simpl in H, H0; tryfalse;
  simpl encode_val in H5, H6; try(destruct a); try(destruct a0);
  try solve [split; auto; eapply ptomvallist_false_mem_eq; eauto];
  try solve [lets Hx: ptomvallist_false_sub_vl_eq H5 H6 H4 H3; [simpl; auto | inverts Hx]].

  assert(i = i0).
  simpl in H5, H6; destruct l; unfold ptomval in *; simpljoin1.
  lets Hx: mem_sub_sig_eq H3 H4.

  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.
  apply Zle_is_le_bool in eq1; apply Zle_is_le_bool in eq2.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inverts Hx; substs.
  lets Hx1: byte_repr_int_unsigned_eq eq1 eq2 H1; auto.
  substs.
  split; eauto.
  eapply ptomvallist_false_mem_eq; eauto.
  
  lets Hx: ptomvallist_false_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts Hx; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.

  apply byte_repr_eq in H2.  

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H7; auto.
  do 2 rewrite Int.repr_unsigned in H8; substs.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  lets Hx: ptomvallist_false_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3;
    remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts Hx; substs.
  apply byte_repr_eq in H8.
  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H10; substs.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  
  lets Hx: ptomvallist_false_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.

  lets Hx: ptomvallist_false_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.
Qed.


Lemma Astruct'_vl_eq :
  forall vl vl' d l e e0 M1 M2 M i lo o1 o2 a,
    struct_type_vallist_match' d vl -> struct_type_vallist_match' d vl' ->
    (e, e0, M1, i, lo, o1, a) |= Astruct' l d vl ->
    (e, e0, M2, i, lo, o2, a) |= Astruct' l d vl' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq' vl vl' d.
Proof.
  inductions vl; intros.
  destruct vl'; destruct d; simpl in H3, H4; tryfalse; auto.
  
  destruct vl'; destruct d; simpl in H3, H4; tryfalse;
  simpl in H, H0.

  destruct l; destruct t; simpl in H1, H2; simpljoin1;
  try solve [
        assert(sub x M) as _H1 by mem_join_sub_solver;
        assert(sub x5 M) as _H2 by mem_join_sub_solver;
        lets Hx1': mapstoval_true_rule_type_val_match_eq H H0 H14 H8 _H2; lets Hx1 : Hx1' _H1;
        assert(sub x0 M) as _H3 by mem_join_sub_solver;
        assert(sub x6 M) as _H4 by mem_join_sub_solver;
        lets Hx2': IHvl H18 H17 H15 H9 _H4; lets Hx2: Hx2' _H3; simpljoin1;
        simpl; auto;
        simpljoin1
      ];
  try solve [simpl; eapply IHvl; eauto].
Qed.

(* new add *)
Lemma Aarray'_vl_eq :
  forall vl vl' d l e e0 M1 M2 M i lo o1 o2 a n,
    array_type_vallist_match d vl -> array_type_vallist_match d vl' ->
    (e, e0, M1, i, lo, o1, a) |= Aarray' l n d vl ->
    (e, e0, M2, i, lo, o2, a) |= Aarray' l n d vl' ->
    sub M1 M -> sub M2 M ->
    vl = vl'.
Proof.
  inductions vl; induction n; intros.
  destruct vl'; simpl in H1, H2; tryfalse; auto.
  
  destruct vl';simpl in H1, H2; tryfalse;
  simpl in H, H0.
  destruct vl'; simpl in H1, H2; tryfalse; auto.
  destruct vl'; simpl in H1, H2; tryfalse; auto.
  destruct l.
  simpl in H, H0; simpljoin1.

  simpl in H1, H2; simpljoin1.
  assert(sub x M) as _H1 by mem_join_sub_solver;
  assert(sub x5 M) as _H2 by mem_join_sub_solver.
  lets Hx1': mapstoval_true_rule_type_val_match_eq H H0 H16 H10 _H2; lets Hx1 : Hx1' _H1.
  assert(sub x0 M) as _H3 by mem_join_sub_solver;
  assert(sub x6 M) as _H4 by mem_join_sub_solver.
  assert (vl = vl').
  eapply IHvl; eauto.
  destruct Hx1; substs.
  auto.
Qed.


Lemma node_vl_eq :
  forall vl vl' head t M1 M2 M o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= node head vl t ->
    (e, e0, M2, i, l, o2, a) |= node head vl' t ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq vl vl' t.
Proof.
  intros.
  unfold node in H, H0.
  destruct H, H0; simpl in H, H0; simpljoin1.
  unfold Astruct in H7, H15.
  destruct t; tryfalse; inverts H6; simpl in H10, H18.
  simpl.
  eapply Astruct'_vl_eq; eauto.
Qed.

Lemma struct_type_vallist_match_os_event : 
forall v,
 struct_type_vallist_match os_ucos_h.OS_EVENT v ->
 exists v1 v2 v3 v4 v5 v6, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: nil.
Proof.
  intros.
  unfold os_ucos_h.OS_EVENT in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  do 6 eexists; eauto.
Qed.

Lemma osabst_eq_join_eq :
  forall m1 m1' m2 m2' M M',
    OSAbstMod.join m1 m2 M ->
    OSAbstMod.join m1' m2' M' ->
    m1 = m1' -> m2 = m2' ->
    M = M'.
Proof.
  intros; substs.
  eapply OSAbstMod.join_unique; eauto.
Qed.

Lemma AOSEvent_osevent_eq :
  forall osevent osevent' etbl etbl' l e e0 M1 M2 M i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AOSEvent l osevent etbl ->
    (e, e0, M2, i, lo, o2, a) |= AOSEvent l osevent' etbl' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT.
Proof.
  unfold AOSEvent; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  eapply node_vl_eq with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma AEventNode_osevent_eq :
  forall v osevent osevent' etbl etbl' d d' e e0 M1 M2 M i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AEventNode v osevent etbl d ->
    (e, e0, M2, i, lo, o2, a) |= AEventNode v osevent' etbl' d' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT.
Proof.
  unfold AEventNode; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  eapply AOSEvent_osevent_eq with (M:=M); eauto; mem_join_sub_solver.
Qed.
(*end*)


(* main lemma ?*)
Lemma a_isr_is: inv_isr_prop A_isr_is_prop.
Proof.
  unfold inv_isr_prop;unfold A_isr_is_prop.
  splits;intros;destruct s as [[]]; destruct t as [[[[]]]];destruct l as [[]].
  unfold isr_is_prop in H;simpl in H; simpljoin1.
  simpl;simpljoin1.
  do 8 eexists;splits;simpljoin1.
  eapply map_join_emp.
  eapply map_join_emp.
  split; eauto.
  split; auto.
  unfolds; auto.

  do 6 eexists;splits;simpljoin1.
  eapply map_join_emp.
  eapply map_join_emp.
  splits; eauto.
  unfolds; auto.

  unfold isr_is_prop.
  intros.
  apply H9 in H.
  unfold isrupd.
  destruct ( beq_nat i x1 );auto.

  unfolds; auto.
  
  (*-----------------------*)
  unfold isr_is_prop in H;simpl in H;simpljoin1.
  simpl.
  do 8 eexists;splits;simpljoin1.
  eapply map_join_emp.
  eapply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists;splits; eauto.
  eapply map_join_emp.
  eapply map_join_emp.
  splits; eauto.
  unfolds; auto.

  unfold isr_is_prop.
  intros.
  unfold isrupd.
  remember ( beq_nat i x1) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H9.
  intro.
  destruct H.
  right;auto.
  unfolds; auto.
  
  (*----------------------------*)
  unfold isr_is_prop in H;simpl in H; simpljoin1.
  simpl; eauto.
  do 8 eexists;splits; eauto.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.

  do 6 eexists;splits;simpljoin1.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.
  unfold isr_is_prop.
  simpl in H0, H1.
  intros.
  
  assert (x1=i\/x1<>i) by tauto.
  destruct H2.
  subst;auto.
  subst x0.
  apply H11.
  intro.
  destruct H.
  simpl in H1.
  destruct H1;tryfalse.
  auto.
  unfolds; auto.
  
  (*----------------------*)
  unfold isr_is_prop in H;simpl in H; simpljoin1.
  simpl;  eauto.
  do 8 eexists;splits; eauto.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.
  
  do 6 eexists;splits;simpljoin1.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.
  unfold isr_is_prop.
  intros.
  simpl in H0.
  subst x.
  unfold empisr.
  auto.
  unfolds; auto.
Qed.


(*---- osabst emp lemmas ----*)
Lemma Astruct'_osabst_emp :
  forall vl e e0 M i l o a0 lo d,
    (e, e0, M, i, lo, o, a0) |= Astruct' l d vl ->
    o = empabst.
Proof.
  inductions vl; intros.
  destruct d; simpl in H; simpljoin1; tryfalse.
  destruct d; simpl in H; tryfalse.
  destruct t; destruct l; simpl in H; simpljoin1; eapply IHvl; eauto.
Qed.

Lemma Astruct_osabst_emp :
  forall e e0 M i l o a lo t vl,
    (e, e0, M, i, lo, o, a) |= Astruct l t vl ->
    o = empabst.
Proof.
  intros.
  unfold Astruct in H; destruct t; tryfalse.
  eapply Astruct'_osabst_emp; eauto.
Qed.

Lemma node_osabst_emp :
  forall head a t e e0 M i l o a0,
    (e, e0, M, i, l, o, a0) |= node head a t ->
    o = empabst.
Proof.
  intros.
  unfold node in H; sep pure.
  eapply Astruct_osabst_emp; eauto.
Qed.

Lemma Aarray'_osabst_emp :
  forall vl l n t e e0 M i lo o a0 ,
    (e, e0, M, i, lo, o, a0) |= Aarray' l n t vl ->
    o = empabst.
Proof.
  inductions vl; intros.
  destruct n; simpl in H; simpljoin1; tryfalse.
  destruct n; simpl in H; tryfalse.
  destruct l; simpl in H; simpljoin1.
  eapply IHvl; eauto.
Qed.

Lemma Aarray_osabst_emp :
  forall vl l t e e0 M i lo o a0 ,
    (e, e0, M, i, lo, o, a0) |= Aarray l t vl ->
    o = empabst.
Proof.
  intros.
  unfold Aarray in H; destruct t; tryfalse.
  eapply Aarray'_osabst_emp; eauto.
Qed.

Lemma ecbf_sllseg_osabst_emp :
  forall eventl e e0 M i l o a head tail t next,
    (e, e0, M, i, l, o, a) |= ecbf_sllseg head tail eventl t next ->
    o = empabst.
Proof.
  inductions eventl; intros.
  simpl in H; simpljoin1.
  
  unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  simpl_sat H; simpljoin1.
  
  eapply node_osabst_emp in H8; substs.
  eapply Aarray_osabst_emp in H18; eauto; substs.
  
  lets Hx: IHeventl H24; substs. (* change H24 -> H34 *)
  clear - H7 H17. (* add H27 *)
  apply OSAbstMod.extensionality; intros.
  simpljoin1. (* new add *)
Qed.

Lemma ecbf_sll_osabst_emp :
  forall eventl e e0 M i l o a head t next,
    (e, e0, M, i, l, o, a) |= ecbf_sll head eventl t next ->
    o = empabst.
Proof.
  intros; unfold ecbf_sll in H.
  apply ecbf_sllseg_osabst_emp in H; auto.
Qed.

Lemma sllseg_osabst_emp :
  forall osql e e0 M i l o a head tail t next,
    (e, e0, M, i, l, o, a) |= sllseg head tail osql t next ->
    o = empabst.
Proof.
  inductions osql; intros.
  simpl in H; simpljoin1.
  
  unfold sllseg in H; fold sllseg in H.
  simpl_sat H; simpljoin1.
  
  eapply node_osabst_emp in H13; substs.
  
  lets Hx: IHosql H14; substs.
  clear - H12.
  apply OSAbstMod.extensionality; intros.
  pose proof H12 a.
  rewrite OSAbstMod.emp_sem in H.
  destruct(OSAbstMod.get o a); tryfalse.
  rewrite OSAbstMod.emp_sem; auto.
Qed.

Lemma sll_osabst_emp :
  forall osql e e0 M i l o a head t next,
    (e, e0, M, i, l, o, a) |= sll head osql t next ->
    o = empabst.
Proof.
  intros; unfold sll in H.
  apply sllseg_osabst_emp in H; auto.
Qed.

Lemma AEventData_osabst_emp :
  forall osevent d e e0 M i lo o a,
    (e, e0, M, i, lo, o, a) |= AEventData osevent d ->
    o = empabst.
Proof.
  unfold AEventData; intros.
  destruct d; try solve [simpl in H; simpljoin1].
Qed.

Lemma AOSEvent_osabst_emp :
  forall l osevent etbl e e0 M i lo o a,
    (e, e0, M, i, lo, o, a) |= AOSEvent l osevent etbl ->
    o = empabst.
Proof.
  unfold AOSEvent; intros.
  simpl_sat H; simpljoin1.
  eapply node_osabst_emp in H3.
  unfold AOSEventTbl in H8.
  simpl_sat H8; simpljoin1.
  eapply Aarray_osabst_emp in H6.
  auto. 
Qed.

Lemma AEventNode_osabst_emp :
  forall v osevent etbl d e e0 M i lo o a,
    (e, e0, M, i, lo, o, a) |= AEventNode v osevent etbl d ->
    o = empabst.
Proof.
  unfold AEventNode; intros.
  simpl_sat H; simpljoin1.
  apply AOSEvent_osabst_emp in H3; apply AEventData_osabst_emp in H4.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H2 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a0); tryfalse; auto.
Qed.

Lemma evsllseg_osabst_emp :
  forall ectrl msgql head tail e e0 M i lo o a,
    (e, e0, M, i, lo, o, a) |= evsllseg head tail ectrl msgql ->
    o = empabst.
Proof.
  inductions ectrl; intros.
  simpl in H; simpljoin1.
  unfold evsllseg in H; fold evsllseg in H; destruct msgql; tryfalse; destruct a.
  simpl_sat H; simpljoin1.
  apply AEventNode_osabst_emp in H8.
  eapply IHectrl in H9; substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H7 a.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a); tryfalse; auto.
Qed.

(* end *)


(*---- precise lemmas -----*)

Lemma precise'2precise:
  forall M1 M2 o1 o2,
    (forall M: mem, sub M1 M -> sub M2 M -> M1 = M2) /\ 
      (forall o: osabst, sub o1 o ->  sub o2 o -> o1 = o2)
    -> 
      (forall M o, sub M1 M -> sub M2 M -> sub o1 o ->  sub o2 o -> M1 = M2 /\ o1 = o2).
Proof. intros. destruct H. split. eapply H;eauto. eapply H4;eauto. Qed.

Lemma Astruct'_precise' :
  forall vl vl' l d M1 M2 o1 o2 e e0 i lo a,
    struct_type_vallist_match' d vl ->
    struct_type_vallist_match' d vl' ->
    (e, e0, M1, i, lo, o1, a) |= Astruct' l d vl ->
    (e, e0, M2, i, lo, o2, a) |= Astruct' l d vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
          sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros; inductions vl.
  destruct vl'.
  destruct d; simpl in H1, H2; simpljoin1; auto; tryfalse.
  destruct d; simpl in H1, H2; simpljoin1; auto; tryfalse.
  destruct vl'.
  destruct d; simpl in H1, H2; simpljoin1; auto; tryfalse.
  
  destruct d; simpl in H, H0; tryfalse.
  destruct l.
  destruct t; simpljoin1;
  try solve [lets Hx: IHvl H H0 H1 H2; auto];  
  try solve [
        simpl in H1; simpljoin1; simpl in H2; simpljoin1;
        lets Hx: IHvl H4 H3 H9 H11; simpljoin1; split; intros; [
          assert(sub x M) by mem_join_sub_solver;
          assert(sub x1 M) by
              mem_join_sub_solver;
          lets Hx1:  mapstoval_true_mem_eq H13 H14 H8 H10;
          substs;
          eapply eq_join_eq; eauto;
          mem_eq_solver M |
          apply (H6 o); auto]
      ].
Qed.

Lemma Astruct'_precise : 
  forall vl vl' l d M1 M2 o1 o2 e e0 i lo a,
    struct_type_vallist_match' d vl ->
    struct_type_vallist_match' d vl' ->
    (e, e0, M1, i, lo, o1, a) |= Astruct' l d vl ->
    (e, e0, M2, i, lo, o2, a) |= Astruct' l d vl' ->
    (forall (M : mem) ( o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros  vl vl' l d M1 M2 o1 o2 e e0 i lo a H H0 H1 H2. 
  eapply precise'2precise;eauto. 
  apply (Astruct'_precise' vl vl' l d M1 M2 o1 o2 e e0 i lo a);eauto.
Qed.


Lemma Astruct_precise' :
  forall vl vl' l t M1 M2 o1 o2 e e0 i lo a,
    struct_type_vallist_match t vl ->
    struct_type_vallist_match t vl' ->
    (e, e0, M1, i, lo, o1, a) |= Astruct l t vl ->
    (e, e0, M2, i, lo, o2, a) |= Astruct l t vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
          sub o1 o -> sub o2 o -> o1 = o2 ).
Proof.
  intros.
  destruct t; simpl in H, H0; tryfalse.
  unfold Astruct in H1, H2.
  lets Hx: Astruct'_precise' H H0 H1 H2; auto.
Qed.

Lemma Astruct_precise :
  forall vl vl' l t M1 M2 o1 o2 e e0 i lo a,
    struct_type_vallist_match t vl ->
    struct_type_vallist_match t vl' ->
    (e, e0, M1, i, lo, o1, a) |= Astruct l t vl ->
    (e, e0, M2, i, lo, o2, a) |= Astruct l t vl' ->
    (forall (M : mem) ( o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  destruct t; simpl in H, H0; tryfalse.
  unfold Astruct in H1, H2.
  lets Hx: Astruct'_precise H H0 H1 H2; auto.
  eapply Hx;eauto.
Qed.


Lemma node_precise' :
  forall vl vl' head t M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= node head vl t ->
    (e, e0, M2, i, l, o2, a) |= node head vl' t ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  simpl in H, H0; simpljoin1; inverts H4.    
  lets Hx: Astruct_precise' H16 H8 H13 H5; auto.
Qed.

Lemma node_precise :
  forall vl vl' head t M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= node head vl t ->
    (e, e0, M2, i, l, o2, a) |= node head vl' t ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' head t M1 M2 o1 o2 e e0 i l a H H0.
  simpl in H, H0; simpljoin1; inverts H4.    
  lets Hx: Astruct_precise H16 H8 H13 H5; auto.
Qed.


Lemma Aarray'_precise' :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= Aarray' head n t vl ->
    (e, e0, M2, i, l, o2, a) |= Aarray' head n t vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intro; inductions vl; intros.
  destruct vl'; destruct n; simpl in H, H0; tryfalse.
  simpljoin1; split;  intros; auto.
  
  destruct vl'; destruct n; simpl in H, H0; tryfalse.
  destruct head.
  
  simpl in H, H0; simpljoin1.
  lets Hx: IHvl H11 H5.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.
Qed.

Lemma Aarray'_precise :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= Aarray' head n t vl ->
    (e, e0, M2, i, l, o2, a) |= Aarray' head n t vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' head n t M1 M2 o1 o2 e e0 i l a H H0.
  eapply precise'2precise;eauto.
  eapply Aarray'_precise';eauto.
Qed.


Lemma Aarray_precise' :
  forall vl vl' head t M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= Aarray head t vl ->
    (e, e0, M2, i, l, o2, a) |= Aarray head t vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).      
Proof.
  intros.
  unfold Aarray in H, H0.
  destruct t; simpl in H, H0; tryfalse.
  eapply Aarray'_precise'; eauto.
Qed.

Lemma Aarray_precise :
  forall vl vl' head t M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= Aarray head t vl ->
    (e, e0, M2, i, l, o2, a) |= Aarray head t vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros vl vl' head t M1 M2 o1 o2 e e0 i l a H H0.
  eapply precise'2precise;eauto.
  eapply Aarray_precise';eauto.
Qed.


Lemma ecbf_sll_precise' :
  forall eventl eventl' head M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= ecbf_sll head eventl os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (e, e0, M2, i, l, o2, a) |= ecbf_sll head eventl' os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions eventl; intros.
  simpl in H; simpljoin1.
  destruct eventl'.
  simpl in H0; simpljoin1; auto.
  unfold ecbf_sll in H0; unfold ecbf_sllseg in H0; fold ecbf_sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct eventl'.
  simpl in H0; simpljoin1.
  unfold ecbf_sll in H; unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold ecbf_sll in H, H0; unfold ecbf_sllseg in H, H0; fold ecbf_sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
 
  lets Hx: node_precise' H9 H12.
  rewrite H14 in H21; inverts H21.
  
  lets Hx1: Aarray_precise' H19 H28. (* H28 -> H30 *)
  (* rewrite H24 in H37; inverts H37. (* new add *) *)
  (* lets Hx1': Aarray_precise' H29 H42. (* new add *) *)

  unfold ecbf_sll in IHeventl.
  simpljoin1; split; intros.
  
  assert(x = x2 (* /\ x4 = x10 /\ x3 = x9 *)). (* x2 -> x4 *)
  assert(sub x8 M) by mem_join_sub_solver. (* x8 -> x11 *)
  assert(sub x15 M) by mem_join_sub_solver. (* x15 -> x21 *)

  lets Hx: node_vl_eq H9 H12 H13 H15(* H13 H15 *).
  simpl in Hx; unfold V_OSEventListPtr in H3, H4.
(*   unfold V_OSPostEventGrp in H39, H55. (* new add *) *)
  unfold node in H9, H12.
  destruct H9, H12; sep split in H9; sep split in  H12; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 a6, a = a1::a2::a3::a4::a5::a6::nil).
  { eapply struct_type_vallist_match_os_event; eauto; do 6 eexists; eauto. } (* H22 -> H31 *)
  assert(exists v1 v2 v3 v4 v5 v6, v = v1::v2::v3::v4::v5::v6::nil).
  { eapply struct_type_vallist_match_os_event; eauto; do 6 eexists; eauto. }
  simpljoin1; simpl in Hx; simpl in H3, H4; simpljoin1; inversion H3; inversion H4; 
(*   inversion H39; inversion H55; (* new add *) *)
  substs; auto.
(*   assert(sub x29 M) by mem_join_sub_solver. *)
(*   assert(sub x47 M) by mem_join_sub_solver. *)
(*   assert (Hvl_eq: x3 = x9). *)
(*   { eapply Aarray'_vl_eq; eauto. } *)
(*   subst; auto. *)
(*   destruct H17 as (Heq1 & Heq2 & Heq3); substs. *)
  substs.

  lets Hx2: IHeventl (* H25 H34 *) H25 H34.
  simpljoin1; mem_eq_solver M.
  
  eapply ecbf_sllseg_osabst_emp in (* H25 *) H25.
  eapply ecbf_sllseg_osabst_emp in (* H34 *) H34.
  substs.
  eapply osabst_eq_join_eq; eauto.
  apply (H2 o). (* H2 -> H10 *)
  clear - H5 H8.
  unfold sub in *; geat.
  clear - H10 H11.
  unfold sub in *; geat.

  eapply osabst_eq_join_eq; eauto.
  apply (H0 o).
  clear -H8 H5 H18.
  unfold sub in *; geat.
  clear -H11 H10 H27.
  unfold sub in *; geat.
Qed.

Lemma ecbf_sll_precise :
  forall eventl eventl' head M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= ecbf_sll head eventl os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (e, e0, M2, i, l, o2, a) |= ecbf_sll head eventl' os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros eventl eventl' head M1 M2 o1 o2 e e0 i l a H H0.
  eapply precise'2precise;eauto.
  eapply ecbf_sll_precise';eauto.
Qed.

Lemma AOSEventFreeList_precise' :
  forall eventl eventl' fecbh fecbh' M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= AOSEventFreeList fecbh eventl ->
    (e, e0, M2, i, l, o2, a) |= AOSEventFreeList fecbh' eventl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSEventFreeList; intros.
  simpl in H, H0; simpljoin1.

  rewrite H23 in H9; inverts H9.
  split; intros.
  assert(fecbh = fecbh').

  assert(isptr fecbh) by (eapply isptr_ecbf_sll; eauto).
  assert(isptr fecbh') by (eapply isptr_ecbf_sll; eauto).
  
  destruct fecbh, fecbh'; auto;
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse);
  try(unfolds in H3; destruct H3; simpljoin1; tryfalse).
  unfolds in H24; simpljoin1; simpl in H4; simpljoin1.
  
  unfolds in H10; simpljoin1; simpl in H11; destruct a0; simpl in H11; simpljoin1.
  clear - H4 H11 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H11; substs.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, Pointer b i0 3)) M).
  mem_join_sub_solver.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, MNull)) M).
  mem_join_sub_solver.

  lets Hx: mem_sub_sig_eq H2 H4; tryfalse.
  
  unfolds in H10; simpljoin1; simpl in H4; simpljoin1.
  unfolds in H24; simpljoin1; simpl in H12; destruct a0; simpl in H12; simpljoin1.
  
  clear - H4 H12 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H12; substs.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, Pointer b i0 3)) M).
  mem_join_sub_solver.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, MNull)) M).
  mem_join_sub_solver.
  lets Hx: mem_sub_sig_eq H2 H4; tryfalse.
 
  inverts H2; inverts H3.
  assert(sub x M).
  apply join_sub_l in H1.
  eapply sub_trans; eauto.
  assert(sub x5 M).
  apply join_sub_l in H15.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_true_vptr_eq H10 H24 H2 H3; simpljoin1.
  
  substs.
  
  assert(x = x5).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  lets Hx: ecbf_sll_precise' H19 H5; simpljoin1.
  mem_eq_solver M.
  
  apply ecbf_sll_osabst_emp in H19; apply ecbf_sll_osabst_emp in H5.
  substs; auto.
Qed.

Lemma AOSEventFreeList_precise :
  forall fecbh fecbh' eventl eventl' M1 M2 o1 o2 e e0 i l a,
    (e, e0, M1, i, l, o1, a) |= AOSEventFreeList fecbh eventl ->
    (e, e0, M2, i, l, o2, a) |= AOSEventFreeList fecbh' eventl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M ->
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros eventl eventl' fecbh fecbh' M1 M2 o1 o2 e e0 i l a H H0.
  eapply precise'2precise;eauto.
  eapply AOSEventFreeList_precise';eauto.
Qed.

Lemma AOSEventTbl_precise' :
  forall l etbl etbl' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AOSEventTbl l etbl ->
    (e, e0, M2, i, lo, o2, a) |= AOSEventTbl l etbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSEventTbl; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  lets Hx: Aarray_precise' H11 H4; auto.
Qed.

Lemma AOSEventTbl_precise :
  forall l etbl etbl' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AOSEventTbl l etbl ->
    (e, e0, M2, i, lo, o2, a) |= AOSEventTbl l etbl' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l etbl etbl' e e0 M1 M2 i lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AOSEventTbl_precise';eauto.
Qed.


Lemma AOSEvent_precise' :
  forall l osevent osevent' etbl etbl' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AOSEvent l osevent etbl ->
    (e, e0, M2, i, lo, o2, a) |= AOSEvent l osevent' etbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSEvent; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  rewrite H14 in H40; inverts H40.
  lets Hx1: node_precise' H30 H4.

  lets Hx2: AOSEventTbl_precise' H35 H9.
  
  (* lets Hx3: AOSEventTbl_precise' H81 H29. *)
  simpljoin1; split; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AOSEvent_precise :
  forall l osevent osevent' etbl etbl' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AOSEvent l osevent etbl ->
    (e, e0, M2, i, lo, o2, a) |= AOSEvent l osevent' etbl' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros. 
  eapply precise'2precise;eauto.
  eapply AOSEvent_precise';eauto.
Qed.
   
Lemma AEventData_precise' :
  forall osevent osevent' d d' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AEventData osevent d ->
    (e, e0, M2, i, lo, o2, a) |= AEventData osevent' d' ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
          sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AEventData; intros.
  simpl in H1.
  assert(exists v1 v2 v3 v4 v5 v6, osevent = v1::v2::v3::v4::v5::v6::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  assert(exists t1 t2 t3 t4 t5 t6, osevent' = t1::t2::t3::t4::t5::t6::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  simpljoin1.
  simpl in H1; simpljoin1; unfold V_OSEventType in *; simpl nth_val in *. 
  destruct d, d'; simpl_sat H; simpl_sat H0; simpljoin1;
  try solve [un_eq_event_type_solver];
  try solve [simpljoin1; intros; auto].
Qed.

Lemma AEventData_precise :
  forall osevent osevent' d d' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AEventData osevent d ->
    (e, e0, M2, i, lo, o2, a) |= AEventData osevent' d' ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros osevent osevent' d d' e e0 M1 M2 i lo o1 o2 a H H0 H1 H2 H3.
  eapply precise'2precise;eauto.
  eapply AEventData_precise';eauto.
Qed.

Lemma AEventNode_precise' :
  forall l osevent osevent' etbl etbl' d d' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AEventNode l osevent etbl d ->
    (e, e0, M2, i, lo, o2, a) |= AEventNode l osevent' etbl' d' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AEventNode; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  
  simpljoin1; split; intros.
  assert(struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT /\
         struct_type_vallist_match os_ucos_h.OS_EVENT osevent /\
         struct_type_vallist_match os_ucos_h.OS_EVENT osevent'
        ).
  split.
  eapply AOSEvent_osevent_eq with (M:=M); eauto; mem_join_sub_solver.
  unfold AOSEvent in H9, H4; unfold node in H9, H4.
  simpl_sat H9; simpl_sat H4; simpljoin1; auto.
  simpljoin1.
  
  lets Hx1: AEventData_precise' H10 H5 H2 H7 H11.
  lets Hx2: AOSEvent_precise' H9 H4.
  simpljoin1.
  mem_eq_solver M.
  
  apply AOSEvent_osabst_emp in H9;
    apply AOSEvent_osabst_emp in H4;
    apply AEventData_osabst_emp in H10;
    apply AEventData_osabst_emp in H5.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H3 a0; pose proof H8 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o2 a0);
    destruct(OSAbstMod.get o1 a0);
    tryfalse; auto.
Qed.

Lemma AEventNode_precise :
  forall l osevent osevent' etbl etbl' d d' e e0 M1 M2 i lo o1 o2 a,
    (e, e0, M1, i, lo, o1, a) |= AEventNode l osevent etbl d ->
    (e, e0, M2, i, lo, o2, a) |= AEventNode l osevent' etbl' d' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros. 
  eapply precise'2precise;eauto. 
  eapply AEventNode_precise';eauto.
Qed.

Lemma evsllseg_precise' :
  forall ectrl ectrl' msgql msgql' head e e0 M1 M2 i l o1 o2 a,
    (e, e0, M1, i, l, o1, a) |= evsllseg head Vnull ectrl msgql ->
    (e, e0, M2, i, l, o2, a) |= evsllseg head Vnull ectrl' msgql' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions ectrl; intros.
  simpl in H; simpljoin1.
  destruct ectrl'.
  simpl in H0; simpljoin1; auto.
  unfold evsllseg in H0; fold evsllseg in H0; destruct msgql'; tryfalse; destruct e1.
  unfold AEventNode in H0; simpl in H0; simpljoin1; tryfalse.
  destruct ectrl'.
  simpl in H0; simpljoin1.
  unfold evsllseg in H; fold evsllseg in H; destruct msgql; tryfalse; destruct a.
  unfold AEventNode in H; simpl in H; simpljoin1; tryfalse.
  
  unfold evsllseg in H, H0;  fold evsllseg in H, H0.
  destruct msgql; destruct msgql'; tryfalse; destruct a, e1.
  destruct H, H0;
    simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  simpljoin1; split; intros.
  assert(
      struct_atom_val_eq v v1 os_ucos_h.OS_EVENT /\
      struct_type_vallist_match os_ucos_h.OS_EVENT v /\
      struct_type_vallist_match os_ucos_h.OS_EVENT v1
    ).
  {
    split.

    eapply AEventNode_osevent_eq with (M:=M); eauto; mem_join_sub_solver.
    split;
      unfold AEventNode in H9, H13; unfold AOSEvent in H9, H13; unfold node in H9, H13;
      simpl_sat H9; simpl_sat H13; simpljoin1; auto.
  }
  simpljoin1.
  simpl in H1.
  assert(exists v1' v2 v3 v4 v5 v6, v = v1'::v2::v3::v4::v5::v6::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  assert(exists a1 a2 a3 a4 a5 a6, v1 = a1::a2::a3::a4::a5::a6::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  simpljoin1.
  simpl in H1; simpljoin1; unfold V_OSEventListPtr in *; simpl nth_val in *; inverts H3; inverts H4.
  lets Hx1: AEventNode_precise' H9 H13.
  lets Hx2: IHectrl H10 H14.
  simpljoin1.
  mem_eq_solver M.

  apply AEventNode_osabst_emp in H9;
    apply AEventNode_osabst_emp in H13;
    apply evsllseg_osabst_emp in H10;
    apply evsllseg_osabst_emp in H14.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H12 a; pose proof H8 a.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o1 a); destruct(OSAbstMod.get o2 a); tryfalse; auto.
Qed.

Lemma evsllseg_precise :
  forall ectrl ectrl' msgql msgql' head e e0 M1 M2 i l o1 o2 a,
    (e, e0, M1, i, l, o1, a) |= evsllseg head Vnull ectrl msgql ->
    (e, e0, M2, i, l, o2, a) |= evsllseg head Vnull ectrl' msgql' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros ectrl ectrl' msgql msgql' head e e0 M1 M2 i l o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply evsllseg_precise';eauto.
Qed.


Lemma AECBList_precise' :
  forall ectrl ectrl' msgql msgql' ecbls ecbls' tcbls tcbls' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AECBList ectrl msgql ecbls tcbls ->
    (e, e0, M2, i, l, o2, a) |= AECBList ectrl' msgql' ecbls' tcbls' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AECBList; intros.
  simpl in H, H0; simpljoin1.
  rewrite H16 in H37; inverts H37.
  split; intros.
  assert(x = x6).
  assert(isptr x).
  eapply evsllseg_isptr; eauto.
  assert(isptr x6).
  eapply evsllseg_isptr; eauto.
  destruct x, x6; auto;
  try(unfolds in H1; destruct H1; simpljoin1; tryfalse);
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse).
  unfolds in H17; simpljoin1; simpl in H3; simpljoin1.
  unfolds in H38; simpljoin1; simpl in H13; destruct a0; simpl in H13; simpljoin1.
  clear - H3 H13 H2 H10 H H0 H8 H29.
  unfold ptomval in H3; unfold ptomval in H13; substs.
  assert(sub x27 M) by mem_join_sub_solver.
  assert(sub x13 M) by mem_join_sub_solver.
  lets Hx: mem_join_sig_sub_eq H10 H2 H1 H3; tryfalse.
  
  unfolds in H17; simpljoin1; simpl in H3; destruct a0; simpl in H3; simpljoin1.
  unfolds in H38; simpljoin1; simpl in H13; simpljoin1.
  clear - H3 H13 H2 H10 H H0 H8 H29.
  unfold ptomval in H3; unfold ptomval in H13; substs.
  assert(sub x27 M) by mem_join_sub_solver.
  assert(sub x13 M) by mem_join_sub_solver.
  lets Hx: mem_join_sig_sub_eq H10 H2 H1 H3; tryfalse.
  
  inverts H1; inverts H2.
  assert(sub x13 M).
  apply join_sub_l in H8.
  eapply sub_trans; eauto.
  assert(sub x27 M).
  apply join_sub_l in H29.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_true_vptr_eq H17 H38 H1 H2; simpljoin1.
  substs.

  assert(x13 = x27).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  
  
  lets Hx: evsllseg_precise' H33 H12; simpljoin1.
  mem_eq_solver M.

  apply evsllseg_osabst_emp in H33; 
    apply evsllseg_osabst_emp in H12; substs; auto.
Qed.

Lemma AECBList_precise :
  forall ectrl ectrl' msgql msgql' ecbls ecbls' tcbls tcbls' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AECBList ectrl msgql ecbls tcbls ->
    (e, e0, M2, i, l, o2, a) |= AECBList ectrl' msgql' ecbls' tcbls' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros ectrl ectrl' msgql msgql' ecbls ecbls' tcbls tcbls' e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AECBList_precise';eauto.
Qed.


Lemma AOSMapTbl_precise' :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSMapTbl ->
    (e, e0, M2, i, l, o2, a) |= AOSMapTbl ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSMapTbl; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9, H4; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H9.
  unfold addrval_to_addr in H9; destruct x, x6; inverts H9.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H3; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise'; eauto.
Qed.

Lemma AOSMapTbl_precise :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSMapTbl ->
    (e, e0, M2, i, l, o2, a) |= AOSMapTbl ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSMapTbl_precise';eauto.
Qed.


Lemma AOSUnMapTbl_precise' :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSUnMapTbl ->
    (e, e0, M2, i, l, o2, a) |= AOSUnMapTbl ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSUnMapTbl; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9, H4; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H9.
  unfold addrval_to_addr in H9; destruct x, x6; inverts H9.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H3; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise'; eauto.
Qed.

Lemma AOSUnMapTbl_precise :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSUnMapTbl ->
    (e, e0, M2, i, l, o2, a) |= AOSUnMapTbl ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSUnMapTbl_precise';eauto.
Qed.

Lemma AOSTCBPrioTbl_precise' :
  forall ptbl ptbl' rtbl rtbl' tcbls tcbls' vhold vhold' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSTCBPrioTbl ptbl rtbl tcbls vhold ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBPrioTbl ptbl' rtbl' tcbls' vhold' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSTCBPrioTbl; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H73, H36; simpljoin1. 
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H6. 
  unfold addrval_to_addr in H6; destruct x49, x17; inverts H6. 
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H5; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  simpl in H68, H31; simpljoin1. 
  rewrite H4 in H; inverts H.
  simpljoin1; split; intros.
  simpl in H69, H32; simpljoin1. 
  assert(x6 = x0). 
  {
    rewrite <- H6 in H9. 
    unfold addrval_to_addr in H9; destruct vhold, vhold'. 
    inverts H9. 
    assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i2)).
    {
      rewrite H11; auto. 
    }
    do 2 rewrite Int.repr_unsigned in H3; substs. 
    eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  }
  substs.
  lets Hx: Aarray_precise' H74 H37; simpljoin1. 
  eapply eq_join_eq; eauto.
  apply H3 with (M:=M); mem_join_sub_solver. 
  apply Aarray_osabst_emp in H74; apply Aarray_osabst_emp in H37; substs. 
  simpl in H69, H32; simpljoin1. 
Qed. 

Lemma AOSTCBPrioTbl_precise :
  forall ptbl ptbl' rtbl rtbl' tcbls tcbls' vhold vhold' e e0 i l a M1 M2 o1 o2, 
    (e, e0, M1, i, l, o1, a) |= AOSTCBPrioTbl ptbl rtbl tcbls vhold ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBPrioTbl ptbl' rtbl' tcbls' vhold' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros ptbl ptbl' rtbl rtbl' tcbls tcbls' vhold vhold' e e0 i l a M1 M2 o1 o2 ptls ptls' H H0.
  eapply precise'2precise;eauto.
  eapply AOSTCBPrioTbl_precise';eauto.
Qed.


Lemma AOSIntNesting_precise' :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSIntNesting ->
    (e, e0, M2, i, l, o2, a) |= AOSIntNesting ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSIntNesting; intros.
  simpl in H, H0; simpljoin1.
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AOSIntNesting_precise :
forall e e0 i l a M1 M2 o1 o2,
  (e, e0, M1, i, l, o1, a) |= AOSIntNesting ->
  (e, e0, M2, i, l, o2, a) |= AOSIntNesting ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSIntNesting_precise';eauto.
Qed.


Lemma AOSRdyTblGrp_precise' :
  forall rtbl rtbl' rgrp rgrp' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSRdyTblGrp rtbl rgrp ->
    (e, e0, M2, i, l, o2, a) |= AOSRdyTblGrp rtbl' rgrp' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSRdyTblGrp; unfold AOSRdyTbl; unfold AOSRdyGrp; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.

  simpl in H65, H32; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H6.
  unfold addrval_to_addr in H6; destruct x54, x29.
  inverts H6.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H5; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  
  simpl in H50, H17; simpljoin1.
  rewrite H21 in H9; inverts H9.
  simpljoin1; split; intros.
  assert(sub x6 M) by mem_join_sub_solver.
  assert(sub x0 M) by mem_join_sub_solver.
  lets Hx': mapstoval_true_rule_type_val_match_eq H51 H18 H22 H11 H4; lets Hx: Hx' H5; clear Hx'.
  simpljoin1.
  
  lets Hx: Aarray_precise' H33 H66; simpljoin1.
  eapply eq_join_eq; eauto.
  symmetry.
  mem_eq_solver M.
  
  apply Aarray_osabst_emp in H33; apply Aarray_osabst_emp in H66.
  substs; auto.
Qed.

Lemma AOSRdyTblGrp_precise :
  forall rtbl rtbl' rgrp rgrp' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSRdyTblGrp rtbl rgrp ->
    (e, e0, M2, i, l, o2, a) |= AOSRdyTblGrp rtbl' rgrp' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros rtbl rtbl' rgrp rgrp' e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSRdyTblGrp_precise';eauto.
Qed.


Lemma AOSTime_precise' :
  forall t t' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSTime (Vint32 t) ->
    (e, e0, M2, i, l, o2, a) |= AOSTime (Vint32 t') ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSTime; intros.
  simpl in H, H0; simpljoin1;
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros; auto.
  lets Hx: mapstoval_true_rule_type_val_match_eq H5 H14 H0 H; simpl; auto.
  simpljoin1.
Qed.

Lemma AOSTime_precise :
  forall t t' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSTime (Vint32 t) ->
    (e, e0, M2, i, l, o2, a) |= AOSTime (Vint32 t') ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros t t' e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSTime_precise';eauto.
Qed.


Lemma Aabsdata_precise' :
  forall id absdata absdata' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= Aabsdata id absdata ->
    (e, e0, M2, i, l, o2, a) |= Aabsdata id absdata' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros; simpl in H, H0.
  simpljoin1; split; intros; auto.
  lets Hx: osabst_sub_sig_eq H H0.
  substs; auto.
Qed.

Lemma Aabsdata_precise :
  forall id absdata absdata' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= Aabsdata id absdata ->
    (e, e0, M2, i, l, o2, a) |= Aabsdata id absdata' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros id absdata absdata' e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply Aabsdata_precise';eauto.
Qed.


Lemma AGVars_precise' :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AGVars ->
    (e, e0, M2, i, l, o2, a) |= AGVars ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AGVars; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H43, H4; simpljoin1.
  rewrite H26 in H7; inverts H7.
  
  simpl in H53, H14; simpljoin1.
  rewrite H24 in H5; inverts H5.

  simpl in H58,  H19; simpljoin1.
  rewrite H22 in H5; inverts H5.

  simpl in H64, H25; simpljoin1.
  rewrite H25 in H5; inverts H5.

  simpl in H75, H36; simpljoin1.
  rewrite H33 in H5; inverts H5.

  simpl in H68, H29; simpljoin1.
  rewrite H29 in H5; inverts H5.

  simpljoin1; split; intros.
  lets Hx1: mapstoval_true_mem_eq M H9 H27.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx2: mapstoval_true_mem_eq M H7 H28.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx3: mapstoval_true_mem_eq M H10 H31.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx4: mapstoval_true_mem_eq M H12 H32.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx5: mapstoval_true_mem_eq M H13 H34.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx6: mapstoval_true_mem_eq M H8 H35.
  mem_join_sub_solver.
  mem_join_sub_solver.

  substs.
  repeat (eapply eq_join_eq; eauto).

  auto.
Qed.

Lemma AGVars_precise :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AGVars ->
    (e, e0, M2, i, l, o2, a) |= AGVars ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AGVars_precise';eauto.
Qed.

Lemma A_isr_is_prop_precise' :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= A_isr_is_prop ->
    (e, e0, M2, i, l, o2, a) |= A_isr_is_prop ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold A_isr_is_prop; intros.
  simpl in H, H0; simpljoin1; intros; auto.
Qed.

Lemma A_isr_is_prop_precise :
  forall e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= A_isr_is_prop ->
    (e, e0, M2, i, l, o2, a) |= A_isr_is_prop ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply A_isr_is_prop_precise';eauto.
Qed.

Require Import seplog_pattern_tacs. 

Lemma Aarray_new'_precise' :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i l a,
    new_array_type_vallist_match t vl ->
    new_array_type_vallist_match t vl' ->
      (e, e0, M1, i, l, o1, a) |= Aarray_new' head n t vl ->
      (e, e0, M2, i, l, o2, a) |= Aarray_new' head n t vl' ->
      (forall M : mem,
         sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
         sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intro. inductions vl; intros. rename H into HX1. rename H0 into HX2. rename H1 into H. rename H2 into H0.
  destruct vl'; destruct n;simpl in H, H0; tryfalse.
  simpljoin1. split; intros; auto.
  rename H into HX1. rename H0 into HX2. rename H1 into H. rename H2 into H0.

  destruct vl';destruct n; tryfalse.
  simpl in H, H0.
  destruct t; destruct v;destruct a; tryfalse; try(destruct a) ;try(destruct v0);tryfalse.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head. simpl in H, H0 . simpl in HX1 , HX2. simpljoin1.
  lets Hx: IHvl H11 H5. apply H17. apply H14.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H11. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H11. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H11. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H11. apply H7.
  osabst_eq_solver o.


  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H11. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H11. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H11. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H11. apply H7.
  osabst_eq_solver o.


  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H11. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H11. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H11. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H11. apply H7.
  osabst_eq_solver o.


  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H11. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H11. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H11. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H11. apply H7.
  osabst_eq_solver o.

  
  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H11. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H11. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H11. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H11. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H11. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H11. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H11. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H11. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H15. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H15. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H13. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H13. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H13. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H13. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H16. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H16. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H15. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H15. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H13. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H13. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H13. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H13. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H16. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H16. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H17. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H17. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H17. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H17. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H15. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H15. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H13. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H13. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H13. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H13. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H16. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Aarray'_precise'. eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H16. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H19. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H19. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Aarray'_precise'.  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H19. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H19. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=nil). simpl. instantiate (1:=d). destruct d. apply H13. apply H11. simpl . destruct d. apply H13. apply H11.
  destruct vl'.
  instantiate (1:=nil). simpl. destruct d. apply H13. apply H11. simpl. destruct d; tryfalse. apply H13.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=nil).  simpl. instantiate (1:=d). destruct d. apply H13. apply H11. simpl. destruct d; tryfalse. apply H13.
  destruct vl'.
  instantiate (1:=nil).  simpl. destruct d. apply H13. apply H11. simpl. destruct d; tryfalse. apply H13.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v :: nil)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
   lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v :: nil)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v :: Vundef :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v :: Vundef :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v :: Vnull :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v :: Vnull :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v :: Vint32 i1 :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v :: Vint32 i1 :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v :: Vptr a1 :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v :: Vptr a1 :: a)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=nil).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
   assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=nil). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=(v :: nil)). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=nil). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=v :: nil).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=nil). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=(v :: v0 :: v1)). simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=nil). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse.
  destruct vl'.
  instantiate (1:=v :: v0 :: v1).  simpl. destruct d. apply H11. apply H11. simpl. destruct d; tryfalse.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v1 :: nil)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=(v :: nil)). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
   lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v1 :: nil)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=(v :: nil)). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.


  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=(v1 :: nil)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=v :: v0 :: v2). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=(v1 :: nil)). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=v :: v0 :: v2). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=v1 :: v2 :: a). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=v :: nil). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
   lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=v1 :: v2 :: a). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=v :: nil). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.

  destruct head.  simpl in H, H0 . simpl in HX1, HX2 . simpljoin1.
  lets Hx: IHvl H10 H5. apply H14. apply H12.
  simpljoin1. split; intros.
  eapply eq_join_eq; eauto.
  eapply Astruct'_precise'.
  unfold new_array_type_vallist_match in H14.
  destruct vl.
  instantiate (1:=v1 :: v2 :: a). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=v :: v0 :: v3). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
  lets Hx1: IHvl H10 H5. eapply H14. eapply H12.
  assert (sub x5 M1). unfold sub. exists x6. apply H6.
  apply sub_trans with (m2:=M1). apply H15. apply H2.
  assert (sub x M2). unfold sub. exists x0. apply H1.
  apply sub_trans with (m2:=M2). apply H15. apply H7.
  mem_eq_solver M.
  eapply eq_join_eq;eauto.
  eapply Astruct'_precise'.
  destruct vl.
  instantiate (1:=v1 :: v2 :: a). simpl. instantiate (1:=d). destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  destruct vl'.
  instantiate (1:=v :: v0 :: v3). simpl. destruct d. apply H13.  destruct t; tryfalse. destruct d; simpl; tryfalse;
  simpl in H13;destruct v1; tryfalse; eauto.
  simpl in H13;destruct v1; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d;simpl; simpl in H13; tryfalse; eauto.
  destruct d; simpl. apply H11. destruct t;simpl;destruct v1;destruct d;tryfalse;eauto.
  eapply H9. eapply H4.
  assert (sub x8 o1). unfold sub. exists x9. apply H8.
  apply sub_trans with (m2:=o1). apply H15. apply H2.
  assert (sub x2 o2). unfold sub. exists x3. apply H3.
  apply sub_trans with (m2:=o2). apply H15. apply H7.
  osabst_eq_solver o.
Qed.

Lemma Aarray_new_precise' :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i l a,
    new_array_type_vallist_match t vl ->
    new_array_type_vallist_match t vl' ->
      (e, e0, M1, i, l, o1, a) |= Aarray_new head (Tarray t n) vl ->
      (e, e0, M2, i, l, o2, a) |= Aarray_new head (Tarray t n) vl' ->
      (forall M : mem,
         sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
         sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   intros.
  unfold Aarray_new in H1, H2.
  destruct t; tryfalse.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
  eapply Aarray_new'_precise'. apply H. apply H0. apply H1. apply H2.
Qed.


Lemma Aarray_new'_osabst_emp :
  forall vl head n t e e0 M i lo o a ,
    (e, e0, M, i, lo, o, a) |= Aarray_new' head n t vl -> 
    o = empabst.
Proof.

  inductions vl; intros.
  destruct n; simpl in H; simpljoin1; tryfalse.
  destruct n. tryfalse.
  simpl in H;tryfalse.
  destruct t. destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.

  destruct head.
  simpl in H; simpljoin1. lets Hx: IHvl H4.
  apply Aarray'_osabst_emp in H3.
  assert (x3 = o). rewrite H3 in H2.  apply map_join_emp''. apply H2. rewrite H in Hx. apply Hx.

  destruct head.
  simpl in H; simpljoin1. lets Hx: IHvl H4.
  apply Astruct'_osabst_emp in H3.
  assert (x3 = o). rewrite H3 in H2.  apply map_join_emp''. apply H2. rewrite H in Hx. apply Hx.
Qed.


Lemma Aarray_new_osabst_emp :
  forall vl head t n e e0 M i lo o a ,
    (e, e0, M, i, lo, o, a) |= Aarray_new head (Tarray t n) vl ->
    o = empabst.
Proof.
  intros.
  unfold Aarray in H; destruct t; tryfalse.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
  eapply Aarray_new'_osabst_emp; eauto.
Qed.

Lemma AObjs_prop_precise' :
  forall e e0 i l a M1 M2 o1 o2 objl absobjs ecbls  absobjs' ecbls' objl' vhold vhold', 
    (e, e0, M1, i, l, o1, a) |= AObjs objl absobjs ecbls vhold ->
    (e, e0, M2, i, l, o2, a) |= AObjs objl' absobjs' ecbls' vhold' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AObjs; intros. 
  unfold AObjArr in *. 
  simpl_sat H; simpl_sat H0.
  simpljoin1.
  simpl in H45, H18.
  simpljoin1.
  rewrite H4 in H16; inverts H16.
  split; intros.
  assert(x17 = x36).
  {
    assert(sub x18 M).
    {
      apply join_sub_l in H15.
      eapply sub_trans;  eauto.
    }
    assert(sub x37 M).
    {
      apply join_sub_l in H42.
      eapply sub_trans; eauto.
    }
    lets Hx: mapstoval_true_vptr_eq H5 H18 H1 H2. simpljoin1.
  }
  assert(x37 = x18).
  substs.
  eapply mapstoval_true_mem_eq with (M:=M);eauto; mem_join_sub_solver.

  eapply eq_join_eq;eauto.
  eapply Aarray_new_precise'. apply H51. apply H24. apply H50. rewrite H1 in H23. eapply H23.

  apply join_sub_r in H42. eapply sub_trans; eauto.
  apply join_sub_r in H15.   eapply sub_trans; eauto.
  eapply Aarray_new_osabst_emp in H50.
  eapply Aarray_new_osabst_emp in H23.
  rewrite <- H23 in H50.
  apply H50.
Qed.


Lemma AOSTCBList_vptr :
  forall s p1 p2 tcbl1 tcbcur tcbl2 rtbl ct tcbls,
    s |= AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ->
    (exists x, p1 = Vptr x).
Proof.
  unfold AOSTCBList; intros.
  destruct_s s.
  simpl_sat H; simpljoin1.
  destruct tcbl1.
  simpl in H8; simpljoin1; eauto.
  unfold tcbdllseg in H8; unfold dllseg in H8; fold dllseg in H8.
  simpl_sat H8; simpljoin1.
  unfold node in H29; simpl_sat H29; simpljoin1.
  eauto.
Qed.

Lemma tcbdllseg_compose:
  forall s P h hp t1 tn1 t2 tn2 l1 l2,
    s |= tcbdllseg h hp t1 tn1 l1 ** tcbdllseg tn1 t1 t2 tn2 l2 ** P->
    s |= tcbdllseg h hp t2 tn2 (l1++l2) ** P.
Proof.
  intros.

  generalize s P h hp t1 tn1 t2 tn2 l2 H.
  clear s P h hp t1 tn1 t2 tn2 l2 H.
  induction l1.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  fold dllseg in H.
  sep split in H.
  subst.
  simpl; auto.
  intros.
  simpl ( (a::l1) ++l2).

  unfold tcbdllseg in *.
  unfold dllseg in *.
  fold dllseg in *.
  sep normal.
  
  sep auto.
  assert (s
      |= dllseg x h t1 tn1 l1 OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
      dllseg tn1 t1 t2 tn2 l2 OS_TCB_flag V_OSTCBPrev V_OSTCBNext ** Aemp).
  sep auto.
  eapply IHl1 in H3.
  sep auto.
  auto.
Qed.

Lemma struct_type_vallist_match_os_tcb :
  forall v, struct_type_vallist_match os_ucos_h.OS_TCB v ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
            exists v11 v12 v13 v14,
              v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: nil.  
Proof.
  intros.
  unfold os_ucos_h.OS_TCB in H.
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
  destruct v11; simpljoin1; tryfalse.
  destruct v12; simpljoin1; tryfalse.
  destruct v13; simpljoin1; tryfalse.
  do 14 eexists; eauto. 
Qed.

Lemma dllseg_osabst_emp :
  forall l head headprev tail tailnext t prev next e e0 M i lo o a0,
    (e, e0, M, i, lo, o, a0) |= dllseg head headprev tail tailnext l t prev next -> o = empabst.
Proof.
  inductions l; intros.
  simpl in H; simpljoin1.
  unfold dllseg in H; fold dllseg in H; simpl_sat H; simpljoin1.
  apply node_osabst_emp in H18; substs.
  eapply IHl in H19; substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H17 a1.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a1); tryfalse; auto.
Qed.

Lemma disj_precise' :
  forall e e0 i l a M1 M2 o1 o2 P P' Q Q',
    ((e, e0, M1, i, l, o1, a) |= P /\
     (e, e0, M2, i, l, o2, a) |= Q' -> False) ->
    ((e, e0, M1, i, l, o1, a) |= Q /\
     (e, e0, M2, i, l, o2, a) |= P' -> False) ->
    (
      forall e e0 i l a M1 M2 o1 o2,
        (e, e0, M1, i, l, o1, a) |= P ->
        (e, e0, M2, i, l, o2, a) |= P' ->
        (forall M : mem,
            sub M1 M -> sub M2 M -> M1 = M2) /\
        (forall o : osabst,
            sub o1 o -> sub o2 o -> o1 = o2)
    ) ->
    (
      forall e e0 i l a M1 M2 o1 o2,
        (e, e0, M1, i, l, o1, a) |= Q ->
        (e, e0, M2, i, l, o2, a) |= Q' ->
        (forall M : mem,
            sub M1 M -> sub M2 M -> M1 = M2) /\
        (forall o : osabst,
            sub o1 o -> sub o2 o -> o1 = o2)
    ) ->
    (e, e0, M1, i, l, o1, a) |= P \\// Q ->
    (e, e0, M2, i, l, o2, a) |= P' \\// Q' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  destruct H3; destruct H4.

  eapply H1; eauto.
  false; eapply H; eauto.
  false; eapply H0; eauto.
  eapply H2; eauto.
Qed.


Lemma AOSTCBFreeList'_isptr :
  forall s p l ct tcbls,
    s |= AOSTCBFreeList' p l ct tcbls ->
    isptr p.
Proof.
  intros.
  unfold AOSTCBFreeList' in H.
  destruct_s s.
  simpl_sat H; simpljoin1.
  destruct H4.
  unfold TCBFree_Not_Eq in H.
  simpl_sat H; simpljoin1.
  destruct l.
  simpl in H11; simpljoin1.
  unfolds; auto.
  unfold assertion.sll in H11.
  unfold sllseg in H11; fold sllseg in H11.
  sep split in H11.
  destruct H11.
  simpl_sat H1; simpljoin1.
  unfold node in H16; destruct H16.
  sep split in H1; simpljoin1.
  unfolds; eauto.

  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  (* do 3 destruct H. *)
  sep split in H; simpljoin1.
  unfolds; eauto.
Qed.

Lemma mapstoval_vnull_vptr_mem_sub_false :
  forall l a x m m' M,
    mapstoval l (Tptr a) true Vnull m ->
    mapstoval l (Tptr a) true (Vptr x) m' ->
    sub m M -> sub m' M ->
    False.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H3, H4.
  destruct x, l.
  simpljoin1.
  simpl in H3; simpljoin1.
  assert(sub x M).
  mem_join_sub_solver.
  assert(sub x5 M).
  mem_join_sub_solver.
  unfold ptomval in H8, H0.
  substs.
  assert (get M (b0, o) = Some (true, MNull)).
  clear - H14.


  eapply mem_sub_sig_true_get; eauto.
  assert (get M (b0, o) = Some (true, Pointer b i 3)).
  clear - H16.
  eapply mem_sub_sig_true_get; eauto.
  rewrite H0 in H8; tryfalse.
Qed.

Lemma struct_type_vallist_match_os_tcb_flag :
  forall v,
    struct_type_vallist_match OS_TCB_flag v ->
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
    exists v11, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: nil. 
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

Lemma ostcb_flag_sll_precise' :
  forall lfree lfree' head e e0 M1 M2 i l o1 o2 a,
    (e, e0, M1, i, l, o1, a) |= sll head lfree OS_TCB_flag V_OSTCBNext ->
    (e, e0, M2, i, l, o2, a) |= sll head lfree' OS_TCB_flag V_OSTCBNext ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions lfree; intros.
  simpl in H; simpljoin1.
  destruct lfree'.
  simpl in H0; simpljoin1; auto.
  unfold sll in H0; unfold sllseg in H0; fold sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct lfree'.
  simpl in H0; simpljoin1.
  unfold sll in H; unfold sllseg in H; fold sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold sll in H, H0; unfold sllseg in H, H0; fold sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  lets Hx: node_precise' H14 H19.
  
  unfold sll in IHlfree.
  simpljoin1; split; intros.
  assert(x5 = x6).
  assert(sub x12 M) by mem_join_sub_solver.
  assert(sub x17 M) by mem_join_sub_solver.
  lets Hx: node_vl_eq H14 H19 H5 H6.
  simpl in Hx; unfold V_OSEventListPtr in H9, H10.
  unfold node in H14, H19.
  destruct H14, H19; sep split in H7; sep split in H8; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, exists a11, a = a1::a2::a3::a4::a5::a6::a7::a8::a9::a10::a11::nil).
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  simpljoin1; simpl in Hx; simpl in H9, H10; simpljoin1; inversion H9; inversion H10; substs; auto.
  substs.
  
  lets Hx2: IHlfree H15 H20.
  simpljoin1; mem_eq_solver M.
  
  eapply sllseg_osabst_emp in H15.
  eapply sllseg_osabst_emp in H20.
  substs.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
Qed.

Lemma ostcb_flag_sll_precise :
  forall lfree lfree' head e e0 M1 M2 i l o1 o2 a,
    (e, e0, M1, i, l, o1, a) |= sll head lfree OS_TCB_flag V_OSTCBNext ->
    (e, e0, M2, i, l, o2, a) |= sll head lfree' OS_TCB_flag V_OSTCBNext ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros lfree lfree' head e e0 M1 M2 i l o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply ostcb_flag_sll_precise';eauto.
Qed.


Fixpoint tcb_linked_list_same_next (vl1 vl2 : list vallist) :=
  match vl1, vl2 with
  | nil, nil => True
  | h1::vl1', h2::vl2' =>
    match (V_OSTCBNext h1), (V_OSTCBNext h2) with
    | (Some a1), (Some a2) => a1 = a2 /\ tcb_linked_list_same_next vl1' vl2'
    | _, _ => False
    end
  | _, _ => False
  end.

Lemma struct_atom_val_eq_V_OSTCBNext_eq :
  forall vl1 vl2 x1 x2,
    struct_atom_val_eq vl1 vl2 OS_TCB_flag ->
    V_OSTCBNext vl1 = Some x1 ->
    V_OSTCBNext vl2 = Some x2 ->
    x1 = x2.
Proof.
  intros.
  destruct vl1;
    unfolds in H0; simpl in H0; tryfalse.
  destruct vl2;
    unfolds in H1; simpl in H1; tryfalse.
  inverts H0; inverts H1.
  simpl in H; simpljoin1.
Qed.

Lemma tcb_linked_list_same_next_intro :
  forall vl vl' p e e0 m i l o1 o2 a,
    (e, e0, m, i, l, o1, a) |= assertion.sll p vl OS_TCB_flag V_OSTCBNext ->
    (e, e0, m, i, l, o2, a) |= assertion.sll p vl' OS_TCB_flag V_OSTCBNext ->
    tcb_linked_list_same_next vl vl'.
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl; auto.

  unfold assertion.sll in H, H0.
  unfold sllseg in *; fold sllseg in *.
  sep split in H; sep split in H0; tryfalse.

  destruct vl'.
  unfold assertion.sll in H, H0.
  unfold sllseg in *; fold sllseg in *.
  sep split in H; sep split in H0; tryfalse.

  unfold assertion.sll in H, H0.
  unfold sllseg in *; fold sllseg in *.
  sep normal in H; sep normal in H0.
  destruct H, H0.
  sep split in H; sep split in H0.
  unfold tcb_linked_list_same_next; fold tcb_linked_list_same_next.
  rewrite H1, H3.
  simpl_sat H; simpl_sat H0; simpljoin1.
  assert (sub x1 m).
  eapply join_sub_l; eauto.
  assert (sub x7 m).
  eapply join_sub_l; eauto.
  lets Hx: node_vl_eq H8 H13 H H0.
  assert (x = x0).
  clear - H1 H3 Hx.
  symmetry.
  eapply struct_atom_val_eq_V_OSTCBNext_eq; eauto.

  substs.
  split; auto.
  lets Hx1: ostcb_flag_sll_precise' H9 H14.
  destruct Hx1.
  assert (sub x2 m).
  eapply join_sub_r; eauto.
  assert (sub x8 m).
  eapply join_sub_r; eauto.
  lets Hx1: H6 H15 H16.
  substs.
  eapply IHvl; eauto.
Qed.
    
Lemma sllfreeflag_precise' :
  forall vl vl' p e e0 i l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, l, o1, a) |= sllfreeflag p vl ->
    (e, e0, M2, i, l, o2, a) |= sllfreeflag p vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl in H0, H1; simpljoin1.
  split; intros; auto.

  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep split in H0.
  sep destruct H1; sep split in H1.
  (* do 2 destruct H1; sep split in H1. *)
  substs; tryfalse.

  destruct vl'.
  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep split in H1.
  sep destruct H0; sep split in H0.
  (* do 2 destruct H0; sep split in H0. *)
  substs; tryfalse.

  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep destruct H0. sep destruct H1.
  (* do 2 destruct H0, H1. *)
  sep split in H0; sep split in H1.
  substs; inverts H4.
  
  (* rearrange H1 and H0 *)
  remember H0 as H0'.
  clear HeqH0' H0.
  remember H0' as H0.
  clear HeqH0 H0'.
  
  simpl_sat H0; simpl_sat H1; simpljoin1.

  unfold tcb_linked_list_same_next in H; fold tcb_linked_list_same_next in H.
  rewrite H3 in H.
  rewrite H5 in H.
  simpljoin1.

  lets Hx: IHvl H0 H18 H33.
  (* lets Hx: IHvl H0 H8 H13. *)
  split; intros.
  destruct Hx.
  assert (sub x25 M) by mem_join_sub_solver.
  assert (sub x37 M) by mem_join_sub_solver.
  lets Hx1: H4 H10 H13.
  substs.
  assert (x = x12).
  {
    simpl in H22, H7; simpljoin1.
    assert (Hsub1': sub x M) by mem_join_sub_solver.
    assert (Hsub2': sub x12 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  substs.
  assert (x18 = x30).
  {
    simpl in H27, H12; simpljoin1.
    assert (Hsub1': sub x18 M) by mem_join_sub_solver.
    assert (Hsub2': sub x30 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  substs.
  assert (x24 = x36). 
  {
    simpl in H32, H17; simpljoin1.
    assert (Hsub1': sub x24 M) by mem_join_sub_solver.
    assert (Hsub2': sub x36 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  substs.

  mem_eq_solver2.
  
  simpl in H7, H22; simpljoin1.
  simpl in H12, H27; simpljoin1.
  simpl in H17, H32; simpljoin1.
  eapply H8; eauto.

Qed.

Lemma sllfreeflag_precise :
  forall vl vl' p e e0 i l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, l, o1, a) |= sllfreeflag p vl ->
    (e, e0, M2, i, l, o2, a) |= sllfreeflag p vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' p e e0 i l a M1 M2 o1 o2 H H0 H1.
  eapply precise'2precise;eauto.
  eapply sllfreeflag_precise';eauto.
Qed.


Lemma sllfreeflag_osabst_emp :
  forall vl p e e0 M i lo o a,
    (e, e0, M, i, lo, o, a) |= sllfreeflag p vl ->
    o = empabst.
Proof.
  inductions vl; intros.
  simpl in H; simpljoin1.

  unfold sllfreeflag in *.
  unfold sllsegfreeflag in H; fold sllsegfreeflag in H.
  do 2 destruct H.
  sep split in H.
  simpl_sat H; simpljoin1.
  simpl in H13; simpljoin1.
  simpl in H18; simpljoin1.
  simpl in H23; simpljoin1.
  eapply IHvl; eauto.
Qed.

Lemma TCBFree_Not_Eq_precise' :
  forall e e0 i l a M1 M2 o1 o2 p ct vl vl',
    (e, e0, M1, i, l, o1, a) |= TCBFree_Not_Eq p ct vl ->
    (e, e0, M2, i, l, o2, a) |= TCBFree_Not_Eq p ct vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold TCBFree_Not_Eq in H, H0.
  sep split in H.
  sep split in H0.
  
  simpl_sat H; simpl_sat H0; simpljoin1.
  split; intros.
  assert(x5 = x).
  lets Hx: ostcb_flag_sll_precise' H11 H6.
  destruct Hx.
  apply H4 with (M:=M); mem_join_sub_solver.
  substs.

  lets Hx: tcb_linked_list_same_next_intro H11 H6.
  lets Hx1: sllfreeflag_precise' Hx H12 H7.
  destruct Hx1.
  assert (sub x6 M) by mem_join_sub_solver.
  assert (sub x0 M) by mem_join_sub_solver.
  lets Hx1: H4 H13 H14; substs.
  eapply join_unique; eauto.
  apply sll_osabst_emp in H11.
  apply sll_osabst_emp in H6.
  substs.
  eapply sllfreeflag_osabst_emp in H12. 
  eapply sllfreeflag_osabst_emp in H7.
  substs.
  eapply eq_join_eq; eauto.
Qed.

Lemma TCBFree_Not_Eq_precise :
  forall e e0 i l a M1 M2 o1 o2 p ct vl vl',
    (e, e0, M1, i, l, o1, a) |= TCBFree_Not_Eq p ct vl ->
    (e, e0, M2, i, l, o2, a) |= TCBFree_Not_Eq p ct vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 p ct vl vl' H H0 .
  eapply precise'2precise;eauto.
  eapply TCBFree_Not_Eq_precise';eauto.
Qed.


Lemma Astruct_vl_eq :
  forall vl vl' t l e e0 M1 M2 M i lo o1 o2 a,
    struct_type_vallist_match t vl -> struct_type_vallist_match t vl' ->
    (e, e0, M1, i, lo, o1, a) |= Astruct l t vl ->
    (e, e0, M2, i, lo, o2, a) |= Astruct l t vl' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq vl vl' t.
Proof.
  intros.
  unfold struct_type_vallist_match in H, H0.
  destruct t; tryfalse.
  unfold Astruct in H1, H2.
  eapply Astruct'_vl_eq; eauto.
Qed.


Lemma TCBFree_Eq_precise' :
  forall e e0 i l a M1 M2 o1 o2 p ct vl vl' tcbls tcbls',
    (e, e0, M1, i, l, o1, a) |= TCBFree_Eq p ct vl tcbls ->
    (e, e0, M2, i, l, o2, a) |= TCBFree_Eq p ct vl' tcbls' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold TCBFree_Eq in H, H0.
  do 3 destruct H; sep split in H.
  do 3 destruct H0; sep split in H0.
  simpl_sat H; simpl_sat H0; simpljoin1.

  split; intros.
  assert(x11 = x5).
  {
    lets Hx: Astruct_precise' H38 H8; auto.
    (* lets Hx: Astruct_precise' H28 H8; auto. *)
    destruct Hx.
    eapply H1 with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.
  
  assert (x1 = x4).
  {
    assert (sub x5 M).
    mem_join_sub_solver.
    lets Hx: Astruct_vl_eq H2 H4 H38 H8 H1. 
    (* lets Hx: Astruct_vl_eq H2 H4 H28 H8 H1. *)
    lets Hx1: Hx H1; clear Hx.
    eapply struct_atom_val_eq_V_OSTCBNext_eq; eauto.
  }
  substs.

  assert (x29 = x56).
  {
    lets Hx: ostcb_flag_sll_precise' H23 H53.
    destruct Hx.
    eapply H1 with (M := M).
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs. 

  assert (x30 = x57).
  {
    lets Hx: tcb_linked_list_same_next_intro H23 H53.
    lets Hx1: sllfreeflag_precise' Hx H24 H54.
    destruct Hx1.
    eapply H1 with (M := M); auto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.
  
  assert (x44 = x17).
  {
    simpl in H43, H13.
    simpljoin1.
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.
  assert (x64 = x37). 
  {
    simpl in H58, H28; simpljoin1.
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.
  assert (x65 = x38).
  {
    simpl in H59, H29; simpljoin1. 
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.    
  }
  substs.
  
  (* Ltac mem_eq_solver2 := *)
  (*   match goal with *)
  (*   | H1: join ?m1 ?m2 ?M1, H2: join ?m3 ?m4 ?M2 |- ?M1 = ?M2 => *)
  (*     eapply eq_join_eq; eauto; mem_eq_solver2 *)
  (*   | _ => idtac *)
  (*   end. *)
  
  mem_eq_solver2.

  apply Astruct_osabst_emp in H8.
  apply Astruct_osabst_emp in H38.

  apply sllfreeflag_osabst_emp in H54.
  apply sllfreeflag_osabst_emp in H24.
  
  apply sll_osabst_emp in H53.
  apply sll_osabst_emp in H23.

  simpl in H43, H13; simpljoin1.
  simpl in H58, H28; simpljoin1.
  simpl in H59, H29; simpljoin1.

Qed.

Lemma TCBFree_Eq_precise :
  forall e e0 i l a M1 M2 o1 o2 p ct vl vl' tcbls tcbls',
    (e, e0, M1, i, l, o1, a) |= TCBFree_Eq p ct vl tcbls ->
    (e, e0, M2, i, l, o2, a) |= TCBFree_Eq p ct vl' tcbls' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i l a M1 M2 o1 o2 p ct vl vl' tcbls tcbls' H H0 .
  eapply precise'2precise;eauto.
  eapply TCBFree_Eq_precise';eauto.
Qed.


Lemma TCBFree_Not_Eq_osabst_emp :
  forall p ct vl e e0 M i lo o a,
    (e, e0, M, i, lo, o, a) |=TCBFree_Not_Eq p ct vl ->
    o = empabst.
Proof.
  intros.
  unfold TCBFree_Not_Eq in H.
  sep split in H.
  simpl_sat H; simpljoin1.
  apply sll_osabst_emp in H4.
  apply sllfreeflag_osabst_emp in H5.
  simpljoin1.
Qed.

Lemma TCBFree_Eq_osabst_emp :
  forall p ct vl e e0 M i lo o a tcbls,
    (e, e0, M, i, lo, o, a) |= TCBFree_Eq p ct vl tcbls ->
    o = empabst.
Proof.
  intros.
  unfold TCBFree_Eq in H.
  do 3 destruct H.
  sep split in H.
  simpl_sat H; simpljoin1.
  apply sll_osabst_emp in H20.
  apply sllfreeflag_osabst_emp in H21.
  apply Astruct_osabst_emp in H5.
  simpl in H10; simpljoin1.
  simpl in H25; simpljoin1.
  simpl in H26; simpljoin1.
Qed.


(*should prove ct = ct' using HCurTCB*)
Lemma AOSTCBFreeList'_precise' :
  forall p p' vl vl' ct e e0 i l a M1 M2 o1 o2 tcbls tcbls',
    (e, e0, M1, i, l, o1, a) |= AOSTCBFreeList' p vl ct tcbls ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBFreeList' p' vl' ct tcbls' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  assert(isptr p).
  eapply AOSTCBFreeList'_isptr; eauto.
  assert(isptr p').
  eapply AOSTCBFreeList'_isptr; eauto.
  unfold AOSTCBFreeList' in *.
  simpl_sat H.
  simpl_sat H0.
  simpljoin1.
  split; intros.
  assert (p = p' /\ x5 = x).
  simpl in H11, H6; simpljoin1.
  rewrite H23 in H14; inverts H14.
  destruct p, p';
    unfold isptr in H1, H2; destruct H1, H2; simpljoin1; tryfalse.
  split; auto.
  eapply mapstoval_true_mem_eq; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  false.
  eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  false.
  eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  assert (sub x M) by mem_join_sub_solver.
  assert (sub x5 M) by mem_join_sub_solver.
  lets Hx: mapstoval_true_vptr_eq H15 H24 H4 H5.
  simpljoin1; auto.

  simpljoin1.
  lets Hx: disj_precise' H7 H12.
  intros.
  clear H6 H7 H12 H11.
  unfold TCBFree_Not_Eq, TCBFree_Eq in H4.
  destruct H4; do 3 destruct H6.
  sep split in H4; sep split in H6; simpljoin1.
  tryfalse.

  intros.
  clear H6 H7 H12 H11.
  unfold TCBFree_Not_Eq, TCBFree_Eq in H4.
  destruct H4; do 3 destruct H4.
  sep split in H4; sep split in H6; simpljoin1.
  tryfalse.

  intros.
  eapply TCBFree_Not_Eq_precise'; eauto.

  intros.
  eapply TCBFree_Eq_precise'; eauto.

  destruct Hx.
  assert (x0 = x6).
  eapply H4 with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.

  mem_eq_solver2.

  simpl in H11, H6; simpljoin1.

  assert (o1 = empabst).
  destruct H12.
  
  apply TCBFree_Not_Eq_osabst_emp in H4; auto.
  apply TCBFree_Eq_osabst_emp in H4; auto.

  assert (o2 = empabst).
  destruct H7.
  apply TCBFree_Not_Eq_osabst_emp in H5; auto.
  apply TCBFree_Eq_osabst_emp in H5; auto.

  simpljoin1.
Qed.

Lemma AOSTCBFreeList'_precise :
  forall p p' vl vl' ct e e0 i l a M1 M2 o1 o2 tcbls tcbls',
    (e, e0, M1, i, l, o1, a) |= AOSTCBFreeList' p vl ct tcbls ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBFreeList' p' vl' ct tcbls' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros p p' vl vl' ct e e0 i l a M1 M2 o1 o2 tcbls tcbls' H H0 .
  eapply precise'2precise;eauto.
  eapply AOSTCBFreeList'_precise';eauto.
Qed.


Lemma AOSTCBFreeList'_pfree_eq :
  forall p p' vl vl' ct ct' e e0 i l a M M1 M2 o1 o2 tcbls tcbls',
    (e, e0, M1, i, l, o1, a) |= AOSTCBFreeList' p vl ct tcbls ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBFreeList' p' vl' ct' tcbls' ->
    sub M1 M -> sub M2 M ->    
    p = p'.
Proof.
  intros.
  lets Hx: AOSTCBFreeList'_isptr H.
  lets Hx1: AOSTCBFreeList'_isptr H0.
    
  unfold AOSTCBFreeList' in *.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H11, H6; simpljoin1.
  rewrite H21 in H11; inverts H11.
  destruct p, p'; auto;
    unfold isptr in *;
    destruct Hx; destruct Hx1; simpljoin1; tryfalse.

  false; eapply mapstoval_vnull_vptr_mem_sub_false with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  false; eapply mapstoval_vnull_vptr_mem_sub_false with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  eapply mapstoval_true_rule_type_val_match_eq with (M := M) (t := (Tptr os_ucos_h.OS_TCB) ).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.


Lemma dllseg_os_tcb_flag_precise' :
  forall l l' head headprev headprev' tail tail' e e0 i lo a M1 M2 o1 o2,
    (e, e0, M1, i, lo, o1, a) |= dllseg head headprev tail Vnull l OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (e, e0, M2, i, lo, o2, a) |= dllseg head headprev' tail' Vnull l' OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions l; intros.
  destruct l'.
  simpl in H, H0; simpljoin1; intros; auto.

  simpl in H; simpljoin1.
  unfold dllseg in H0; fold dllseg in H0.
  simpl_sat H0; simpljoin1; tryfalse.
  
  destruct l'.
  simpl in H0; simpljoin1.
  unfold dllseg in H; fold dllseg in H; simpl_sat H; simpljoin1.
  simpl in H18; simpljoin1; tryfalse.
  unfold dllseg in H0, H; fold dllseg in H0, H; simpl_sat H0; simpl_sat H; simpljoin1.

  simpljoin1; split;  intros.
  assert(struct_atom_val_eq a v OS_TCB_flag).
  eapply node_vl_eq with (M:=M); eauto; mem_join_sub_solver.
  simpl in H1.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, a = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).

  unfold node in H45; simpl_sat H45; simpljoin1.
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).
  unfold node in H19; simpl_sat H19; simpljoin1.
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  simpljoin1.

  simpl in H1; simpljoin1.
  unfold V_OSTCBNext in H9, H35; unfold V_OSTCBPrev in H40, H14; unfold nth_val in *.
  inverts H9; inverts H14; inverts H35; inverts H40.

  lets Hx1: IHl H46 H20.
  lets Hx2: node_precise' H45 H19; simpljoin1.
  mem_eq_solver M.

  apply node_osabst_emp in H45;
    apply node_osabst_emp in H19;
    apply dllseg_osabst_emp in H46;
    apply dllseg_osabst_emp in H20;
    substs.

  eapply OSAbstMod.extensionality; intros.
  pose proof H18 a1; pose proof H44 a1.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o1 a1 );
    destruct(OSAbstMod.get o2 a1 );
    tryfalse; auto.
Qed.

Lemma dllseg_os_tcb_flag_precise :
  forall l l' head headprev headprev' tail tail' e e0 i lo a M1 M2 o1 o2,
    (e, e0, M1, i, lo, o1, a) |= dllseg head headprev tail Vnull l OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (e, e0, M2, i, lo, o2, a) |= dllseg head headprev' tail' Vnull l' OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l l' head headprev headprev' tail tail' e e0 i lo a M1 M2 o1 o2 H H0 .
  eapply precise'2precise;eauto.
  eapply dllseg_os_tcb_flag_precise';eauto.
Qed.


Lemma tcbdllseg_precise' :
  forall l l' head headprev headprev' tail tail' e e0 i lo a M1 M2 o1 o2,
    (e, e0, M1, i, lo, o1, a) |= tcbdllseg head headprev tail Vnull l ->
    (e, e0, M2, i, lo, o2, a) |= tcbdllseg head headprev' tail' Vnull l' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold tcbdllseg; intros.
  eapply dllseg_os_tcb_flag_precise'; eauto.
Qed.

Lemma tcbdllseg_precise :
  forall l l' head headprev headprev' tail tail' e e0 i lo a M1 M2 o1 o2,
    (e, e0, M1, i, lo, o1, a) |= tcbdllseg head headprev tail Vnull l ->
    (e, e0, M2, i, lo, o2, a) |= tcbdllseg head headprev' tail' Vnull l' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l l' head headprev headprev' tail tail' e e0 i lo a M1 M2 o1 o2 H H0 .
  eapply precise'2precise;eauto.
  eapply tcbdllseg_precise';eauto.
Qed.


Lemma tcbdllseg_osabst_emp :
  forall l head headprev tail tailnext e e0 M i lo o a0,
    (e, e0, M, i, lo, o, a0) |= tcbdllseg head headprev tail tailnext l -> o = empabst.
Proof.
  unfold tcbdllseg; intros.
  apply dllseg_osabst_emp in H; auto.
Qed.

Lemma tcb_linked_list_same_next_intro_dllseg :
  forall vl vl' head headprev headprev' tail tail' e e0 m i l o1 o2 a,
    (e, e0, m, i, l, o1, a) |= dllseg head headprev tail Vnull vl OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (e, e0, m, i, l, o2, a) |= dllseg head headprev' tail' Vnull vl' OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    tcb_linked_list_same_next vl vl'.
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl; auto.

  unfold dllseg in *; fold dllseg in *.
  sep split in H; sep split in H0; tryfalse.
  
  destruct vl'.
  unfold dllseg in *; fold dllseg in *.
  sep split in H; sep split in H0; tryfalse.
  
  unfold dllseg in *; fold dllseg in *.
  sep normal in H; sep normal in H0.
  destruct H, H0.
  sep split in H; sep split in H0.
  unfold tcb_linked_list_same_next; fold tcb_linked_list_same_next.
  rewrite H1, H4.
  simpl_sat H; simpl_sat H0; simpljoin1.
  assert (sub x1 m).
  eapply join_sub_l; eauto.
  assert (sub x7 m).
  eapply join_sub_l; eauto.
  lets Hx: node_vl_eq H15 H10 H0 H.
  assert (x = x0).
  clear - H1 H4 Hx.
  eapply struct_atom_val_eq_V_OSTCBNext_eq; eauto.

  substs.
  split; auto.

  lets Hx1: dllseg_os_tcb_flag_precise' H11 H16.
  destruct Hx1.
  assert (sub x2 m).
  eapply join_sub_r; eauto.
  assert (sub x8 m).
  eapply join_sub_r; eauto.
  lets Hx1: H8 H17 H18.
  substs. 
  eapply IHvl; eauto.
Qed.

Lemma tcb_linked_list_same_next_intro' :
  forall vl vl' head tail tail' e e0 m i l o1 o2 a,
    (e, e0, m, i, l, o1, a) |= tcbdllseg head Vnull tail Vnull vl ->
    (e, e0, m, i, l, o2, a) |= tcbdllseg head Vnull tail' Vnull vl' ->
    tcb_linked_list_same_next vl vl'.
Proof.
  intros.
  eapply tcb_linked_list_same_next_intro_dllseg; eauto.
Qed.

Lemma AOSTCBList'_tcbdllseg:
  forall e e0 m i l o a head p2 vll1 vll2 rtbl hcurt tcbls pf, 
    (e, e0, m, i, l, o, a) |= AOSTCBList' head p2 vll1 vll2 rtbl hcurt tcbls pf ->
    exists tail P, 
      (e, e0, m, i, l, o, a) |= tcbdllseg head Vnull tail Vnull (vll1++vll2) ** P.  
Proof.
  introv Hsat.
  unfold AOSTCBList' in *.
  destruct Hsat.
  sep destruct H.
  sep lifts (2::4::nil)%nat in H.
  apply tcbdllseg_compose in H.
  exists x0. eexists.  eauto.
  sep destruct H.
  sep lift 3%nat in H.
  unfold tcblist in H.
  sep normal in H.
  exists x. eexists. eauto.
Qed.   

Lemma gvar_ptr_precise' :
  forall m1 m2 m v1 v2 e e0 i l o1 o2 a t gvar, 
    isptr v1 ->
    isptr v2 -> 
    (e, e0, m1, i, l, o1, a) |= GV gvar @ (Tptr t) |-> v1 ->  
    (e, e0, m2, i, l, o2, a) |= GV gvar @ (Tptr t) |-> v2 ->
    sub m1 m ->
    sub m2 m -> 
    v1 = v2. 
Proof.
  introv Hptr1 Hptr2 Hv1 Hv2 Hsub1 Hsub2.
  destruct Hv1.
  destruct Hv2.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9. simpl in H4. simpljoin1.
  rewrite H0 in H. inverts H.
  destruct H10. destruct H5.
  simpl in *.
  unfold isptr in *.
  destruct Hptr1; destruct Hptr2.
  congruence.
  destruct H5. subst v1. subst v2.
  exfalso. eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  destruct H4.
  subst v1. subst v2.
  exfalso. eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  destruct H4. destruct H5.
  subst v1. subst v2.
  lets H00: mapstoval_true_vptr_eq H H2 Hsub1 Hsub2.
  destruct H00.
  congruence.
Qed.   

Lemma AOSTCBList'_tcb_list_same_head :
  forall vll1 vll1' vll2 vll2' head head' p2 p2' e e0 m i l o1 o2 a
         rtbl rtbl' hcurt hcurt' tcbls tcbls' pf pf',
    (e, e0, m, i, l, o1, a) |= AOSTCBList' head p2 vll1 vll2 rtbl hcurt tcbls pf ->
    (e, e0, m, i, l, o2, a) |= AOSTCBList' head' p2' vll1' vll2' rtbl' hcurt' tcbls' pf' ->
    head = head'.
Proof.
  introv Hsat1 Hsat2.
  lets Htcbdllseg1: AOSTCBList'_tcbdllseg Hsat1.
  lets Htcbdllseg2: AOSTCBList'_tcbdllseg Hsat2.
  simpljoin1. 
  apply dllseg_head_isptr in H0. rename H0 into Hptr1.
  apply dllseg_head_isptr in H. rename H into Hptr2.
  destruct Hsat1; destruct Hsat2; 
    (sep destruct H; sep destruct H0; 
     elim_sep_conj1 H H_; elim_sep_conj1 H0 H0_; 
     eapply gvar_ptr_precise'; eauto; 
     [ instantiate (1:=m); eapply join_sub_l; eauto | 
       eapply join_sub_l; eauto]).
Qed.     
  
Lemma AOSTCBList'_tcb_list_same_next_intro':
  forall vll1 vll1' vll2 vll2' head head' p2 p2' e e0 m i l o1 o2 a
         rtbl rtbl' hcurt hcurt' tcbls tcbls' pf pf',  
    (e, e0, m, i, l, o1, a) |= AOSTCBList' head p2 vll1 vll2 rtbl hcurt tcbls pf ->
    (e, e0, m, i, l, o2, a) |= AOSTCBList' head' p2' vll1' vll2' rtbl' hcurt' tcbls' pf' -> 
    tcb_linked_list_same_next (vll1 ++ vll2) (vll1' ++ vll2').  
Proof.
  introv Hsat1 Hsat2.
  assert (Hhdeq: head = head').
  {
     eapply AOSTCBList'_tcb_list_same_head; eauto.
  }
  subst head'.
  unfold AOSTCBList' in *.
  destruct Hsat1; destruct Hsat2.
  - 
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lifts (2::4::nil)%nat in H. sep lifts (2::4::nil)%nat in H0.
    apply tcbdllseg_compose in H.
    apply tcbdllseg_compose in H0.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x7 = x11).
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H15 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x11. 
    eapply tcb_linked_list_same_next_intro'; eauto.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lifts (2::4::nil)%nat in H.
    apply tcbdllseg_compose in H.
    sep lift 3%nat in H0.
    unfold tcblist in H0.
    sep split in H0.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x4 = x8).
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H13 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x8. 
    eapply tcb_linked_list_same_next_intro'; eauto.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lifts (2::4::nil)%nat in H0.
    apply tcbdllseg_compose in H0.
    sep lift 3%nat in H.
    unfold tcblist in H.
    sep split in H.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x4 = x8).
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H13 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x8. 
    eapply tcb_linked_list_same_next_intro'; eauto.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lift 3%nat in H.
    unfold tcblist in H. sep split in H.
    sep lift 3%nat in H0.
    unfold tcblist in H0. sep split in H0.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x1 = x5). 
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H11 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x5.
    eapply tcb_linked_list_same_next_intro'; eauto.
Qed.   

Lemma tcbdllseg_isvptr1:
  forall l s p1 tail1 ct p z,
    s |= tcbdllseg p1 z tail1 (Vptr ct) l ** p -> exists x, p1 = Vptr x.
Proof.
  inductions l.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  sep split in H.
  eauto.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  unfold node in H.
  sep normal in H.
  sep destruct  H.
  sep split in H.
  simpljoin1; eauto.
Qed.


Lemma tcblist_isptr :
  forall s head tail vl rtbl tcbls P,
    s |= tcblist head Vnull tail Vnull vl rtbl tcbls ** P ->
    isptr head.
Proof.
  intros.
  destruct_s s.
  destruct vl.
  simpl in H; simpljoin1.
  unfolds; eauto.

  unfold tcblist in H.
  sep split in H.
  unfold tcbdllseg in H.
  
  sep_rmb_trms_in H dllseg.
  (* sep remember (1::nil)%nat in H. *)
  eapply dllseg_head_isptr in H; auto.
Qed.

Lemma AOSTCBList'_isptr :
  forall s p1 p2 l1 l2 rtbl hcurt tcbls pf,
    s |= AOSTCBList' p1 p2 l1 l2 rtbl hcurt tcbls pf ->
    isptr p1.
Proof.
  intros.
  unfold AOSTCBList' in H.
  destruct H.
  do 4 destruct H.
  sep split in H; simpljoin1.
  sep remember (2::nil)%nat in H.
  eapply tcbdllseg_isvptr1 in H.
  destruct H; substs; unfolds; eauto.

  destruct H.
  sep split in H; simpljoin1.
  sep remember (3::nil)%nat in H.
  eapply tcblist_isptr; eauto.
Qed.

Lemma dllsegflag_osabst_emp :
  forall vl e e0 M i o a0 lo p headprev,
    (e, e0, M, i, lo, o, a0) |= dllsegflag p headprev vl V_OSTCBNext ->
    o = empabst.
Proof.
  inductions vl; intros.
  simpl in H; simpljoin1.

  unfold dllsegflag in H; fold dllsegflag in H.
  do 2 destruct H; sep split in H.
  simpl_sat H; simpljoin1.
  lets Hx: IHvl H6; substs.
  simpl in H5; simpljoin1.
Qed.

Lemma tcbdllflag_osabst_emp :
  forall vl e e0 M i o a0 lo p,
    (e, e0, M, i, lo, o, a0) |= tcbdllflag p vl ->
    o = empabst.
Proof.
  intros.
  unfold tcbdllflag in H.
  eapply dllsegflag_osabst_emp; eauto.
Qed.

Lemma dllsegflag_precise' :
  forall vl vl' p headprev headprev' e e0 i l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, l, o1, a) |= dllsegflag p headprev vl V_OSTCBNext ->
    (e, e0, M2, i, l, o2, a) |= dllsegflag p headprev' vl' V_OSTCBNext ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl in H0, H1; simpljoin1.
  split; intros; auto.
  
  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep split in H0.
  do 2 destruct H1; sep split in H1.
  substs; tryfalse.
  
  destruct vl'.
  unfold dllsegflag in *; fold dllsegflag in *.
  sep split in H1.
  do 2 destruct H0; sep split in H0.
  substs; tryfalse.
  
  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  do 2 destruct H0, H1.
  sep split in H0; sep split in H1.
  substs; inverts H4.
  
  (* rearrange H1 and H0 *)
  remember H0 as H0'.
  clear HeqH0' H0.
  remember H0' as H0.
  clear HeqH0 H0'.
  
  simpl_sat H0; simpl_sat H1; simpljoin1.

  unfold tcb_linked_list_same_next in H; fold tcb_linked_list_same_next in H.
  rewrite H3 in H.
  rewrite H5 in H.
  simpljoin1.

  lets Hx: IHvl H0 H8 H13.
  split; intros.
  destruct Hx.
  assert (sub x3 M).
  mem_join_sub_solver.
  assert (sub x9 M).
  mem_join_sub_solver.
  lets Hx1: H4 H14 H15.
  substs.
  assert (x = x8).
  simpl in H12, H7; simpljoin1.
  assert (sub x M).
  mem_join_sub_solver.
  assert (sub x8 M).
  mem_join_sub_solver.
  lets Hx: mapstoval_false_mem_eq H6 H11 H7 H12.
  auto.
  substs.
  clear - H9 H2.
  eapply join_unique; eauto.

  simpl in H7, H12; simpljoin1.
  eapply H10; eauto.
Qed.

Lemma dllsegflag_precise :
  forall vl vl' p headprev headprev' e e0 i l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, l, o1, a) |= dllsegflag p headprev vl V_OSTCBNext ->
    (e, e0, M2, i, l, o2, a) |= dllsegflag p headprev' vl' V_OSTCBNext ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' p headprev headprev' e e0 i l a M1 M2 o1 o2 H H0 H1.
  eapply precise'2precise;eauto.
  eapply dllsegflag_precise';eauto.
Qed.


Lemma tcbdllflag_precise' :
  forall vl vl' p e e0 i l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, l, o1, a) |= tcbdllflag p vl ->
    (e, e0, M2, i, l, o2, a) |= tcbdllflag p vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold tcbdllflag in *.
  eapply dllsegflag_precise'; eauto.
Qed.

Lemma tcbdllflag_precise :
  forall vl vl' p e e0 i l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, l, o1, a) |= tcbdllflag p vl ->
    (e, e0, M2, i, l, o2, a) |= tcbdllflag p vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' p e e0 i l a M1 M2 o1 o2 H H0 H1.
  eapply precise'2precise;eauto.
  eapply tcbdllflag_precise';eauto.
Qed.


(*pfree eq by the above lemma on AOSTCBFreeList*)
(*ct eq can be obtained from HCurTid*)
Lemma AOSTCBList'_precise' :
  forall p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct tcbls tcbls' pfree  e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pfree ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBList' p1' p2' tcbl1' (tcbcur' :: tcbl2') rtbl' ct tcbls' pfree ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  eapply disj_precise'; eauto.

  intros.
  destruct H1.
  do 4 destruct H1; sep split in H1.
  destruct H2; sep split in H2.
  simpljoin1; tryfalse.

  intros.
  destruct H1.
  destruct H1; sep split in H1.
  do 4 destruct H2; sep split in H2.
  simpljoin1; tryfalse.

-
  intros.
  do 4 destruct H1; do 4 destruct H2.
  sep split in H1; sep split in H2; simpljoin1.
  
  (* rearrange H1 and H2 *)
  remember H1 as H1'.
  clear HeqH1' H1.
  remember H1' as H1.
  clear HeqH1 H1'.
  
  apply AOSTCBList'_isptr in H.
  apply AOSTCBList'_isptr in H0.
  clear H4 H5 H9 H10 H11 H12 H6 H7; clears.
  sep lifts (2::4::nil)%nat in H2.
  sep lifts (2::4::nil)%nat in H1.
  apply tcbdllseg_compose in H2.
  apply tcbdllseg_compose in H1.
  
  destruct p1, p1'; unfold isptr in H, H0; destruct H; destruct H0; simpljoin1; tryfalse.
  clear H3 H8 H0 H; clears.
  split; intros.
  simpl_sat H2.
  simpl_sat H1.
  simpljoin1.
  simpl in H26; simpljoin1.
  simpl in H11; simpljoin1.
  rewrite H9 in H11; inverts H11.
  
  assert (Vptr a = Vptr a1 /\ x13 = x25).
  eapply mapstoval_true_rule_type_val_match_eq with (M := M) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  
  simpljoin1.
  inverts H1.
  simpl in H31; simpl in H16; simpljoin1.
  rewrite H31 in H11; inverts H11.
  assert (x19 = x31).
  eapply mapstoval_false_mem_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  assert (x7 = x).
  lets Hx: tcbdllseg_precise' H21 H6.
  destruct Hx.
  eapply H2 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.

  substs.
  lets Hx: tcb_linked_list_same_next_intro' H21 H6.
  assert (x32 = x20).
  lets Hx1: tcbdllflag_precise' Hx H32 H17.
  destruct Hx1.
  eapply H1 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  mem_eq_solver2.

  simpl_sat H2; simpl_sat H1; simpljoin1.
  unfold tcbdllseg in *.
  apply dllseg_osabst_emp in H21;
    apply dllseg_osabst_emp in H6.
  simpl in H26, H31, H11, H16; simpljoin1.
  eapply tcbdllflag_osabst_emp in H32;
    eapply tcbdllflag_osabst_emp in H17.
  simpljoin1.

- 
  intros.
  apply AOSTCBList'_isptr in H.
  apply AOSTCBList'_isptr in H0.
  destruct H1, H2.
  unfold TCB_Not_In in *.
  unfold tcblist in *.
  sep split in H1; sep split in H2.
  simpljoin1.
  
  (* rearrange H1 and H2 *)
  remember H1 as H1'.
  clear HeqH1' H1.
  remember H1' as H1.
  clear HeqH1 H1'.
  
  destruct p1, p1'; unfold isptr in H, H0; destruct H; destruct H0; simpljoin1; tryfalse.
  inverts H10.
  clear H H0 H3 H7 H8 H11 H4 H13 H5 H9; clears.
  simpl_sat H2; simpl_sat H1; simpljoin1.
  split; intros.
  
  assert (Vptr a2 = Vptr a1 /\ x8 = x1).
  simpl in H19, H4; simpljoin1.
  rewrite H33 in H12; inverts H12.
  eapply mapstoval_true_rule_type_val_match_eq with (M := M) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  simpljoin1.
  inverts H2.
  
  assert (x26 = x14).
  simpl in H24, H9; simpljoin1.
  rewrite H33 in H12.
  inverts H12.
  eapply mapstoval_false_mem_eq with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  eauto.
  eauto.
  substs.

  assert (x20 = x32).
  lets Hx: tcbdllseg_precise' H14 H29.
  destruct Hx.
  eapply H2 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.

  assert (x21 = x33).
  lets Hx: tcb_linked_list_same_next_intro' H14 H29.
  lets Hx1: tcbdllflag_precise' Hx H15 H30.
  destruct Hx1.
  eapply H2 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  mem_eq_solver2.

  simpl in H19, H24, H4, H9; simpljoin1.
  apply tcbdllseg_osabst_emp in H29;
    apply tcbdllseg_osabst_emp in H14.
  apply tcbdllflag_osabst_emp in H30;
    apply tcbdllflag_osabst_emp in H15.
  simpljoin1.
Qed.

Lemma AOSTCBList'_precise :
  forall p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct tcbls tcbls' pfree  e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pfree ->
    (e, e0, M2, i, l, o2, a) |= AOSTCBList' p1' p2' tcbl1' (tcbcur' :: tcbl2') rtbl' ct tcbls' pfree ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct tcbls tcbls' pfree  e e0 i l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSTCBList'_precise';eauto.
Qed.


Lemma AOSTCBList'_ct_eq :
  forall p1 p1' p2 p2' l1 l1' l2 l2' rtbl rtbl' ct ct'
    tcbls tcbls' pfree pfree'
    e e0 i lo a M1 M2 M o1 o2,
    (e, e0, M1, i, lo, o1, a) |= AOSTCBList' p1 p2 l1 l2 rtbl ct tcbls pfree ->
    (e, e0, M2, i, lo, o2, a) |= AOSTCBList' p1' p2' l1' l2' rtbl' ct' tcbls' pfree' ->
    sub M1 M -> sub M2 M ->
    ct = ct'.
Proof.
  intros.
  unfold AOSTCBList' in *.
  destruct H, H0.
  
  do 4 destruct H.
  do 4 destruct H0.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (3::nil)%nat in H0.
  sep remember (3::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H37 in H23; inverts H23.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  do 4 destruct H.
  destruct H0.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (2::nil)%nat in H0.
  sep remember (3::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H33 in H19; inverts H19.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  do 4 destruct H0.
  destruct H.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (3::nil)%nat in H0.
  sep remember (2::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H33 in H19; inverts H19.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  destruct H.
  destruct H0.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (2::nil)%nat in H0.
  sep remember (2::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H29 in H15; inverts H15.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.

Lemma AOSTCBList'_osabst_emp :
  forall e e0 M i o a0 lo p1 p2 l1 l2 rtbl hcurt tcbls pf,
    (e, e0, M, i, lo, o, a0) |= AOSTCBList' p1 p2 l1 l2 rtbl hcurt tcbls pf ->
    o = empabst.
Proof.
  intros.
  unfold AOSTCBList' in H.
  destruct H.
  do 4 destruct H.
  sep split in H.
  clear H0 H1 H2 H3 H4.
  sep lifts (2::4::nil)%nat in H.
  eapply tcbdllseg_compose in H.
  simpl_sat H; simpljoin1.
  simpl in H8; simpljoin1.
  apply tcbdllseg_osabst_emp in H3.
  apply tcbdllflag_osabst_emp in H14.
  simpl in H13; simpljoin1.

  destruct H.
  unfold tcblist in H.
  unfold TCB_Not_In in H.
  sep normal in H; sep split in H.
  simpl_sat H; simpljoin1.
  clear H0 H2 H1 H19.
  simpl in H7.
  simpl in H12.
  simpljoin1.
  apply tcbdllseg_osabst_emp in H17.
  apply tcbdllflag_osabst_emp in H18.
  simpljoin1.
Qed.

Lemma AOSTCBFreeList'_osabst_emp :
  forall e e0 M i o a0 lo ptfree lfree ct tcbls,
    (e, e0, M, i, lo, o, a0) |= AOSTCBFreeList' ptfree lfree ct tcbls->
    o = empabst.
Proof.
  intros.
  unfold AOSTCBFreeList' in H.
  simpl_sat H.
  simpljoin1.
  destruct H4.
  unfold TCBFree_Not_Eq in H.
  sep split in H.
  clear H1.
  simpl_sat H.
  simpl in H3.
  simpljoin1.
  apply sll_osabst_emp in H6.
  apply sllfreeflag_osabst_emp in H7.
  simpljoin1.

  unfold TCBFree_Eq in H.
  do 3 destruct H.
  sep split in H.
  clear H1 H4.
  simpl_sat H.
  simpl in H3.
  simpljoin1.
  apply Astruct_osabst_emp in H6.
  apply sll_osabst_emp in H21.
  apply sllfreeflag_osabst_emp in H22.
  simpl in H11; simpljoin1.
  simpl in H26; simpljoin1.
  simpl in H27; simpljoin1.
Qed.

Lemma HObjs_precise': 
  forall absobjs absobjs' e e0 M1 M2 i l o1 o2 a,   
  (e, e0, M1, i, l, o1, a) |= HObjs absobjs ->
  (e, e0, M2, i, l, o2, a) |= HObjs absobjs' -> 
  (forall M : mem, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H0, H2.
  split.
  intros. congruence.
  intros.
  lets H00: osabst_sub_sig_eq H H1.
  congruence.
Qed.   
  
Require Import os_ucos_h.

Ltac simp_mt hyp :=
  match type of hyp with
    context [?t] =>
    match goal with
      H: ?t = _ |- _ => rewrite H in hyp  
    end
  end.

Lemma llsegobjaux_mpeq: 
  forall tcbvl tcbvl' tcblh ctcb locmp locmp' ptrmp ptrmp' e e0 i l a M1 M2 o1 o2 M, 
    (e, e0, M1, i, l, o1, a) |= llsegobjaux tcblh ctcb tcbvl locmp ptrmp V_OSTCBNext ->
    (e, e0, M2, i, l, o2, a) |= llsegobjaux tcblh ctcb tcbvl' locmp' ptrmp' V_OSTCBNext ->  
    tcb_linked_list_same_next tcbvl tcbvl' ->
    sub M1 M ->
    sub M2 M -> 
    locmp = locmp' /\ ptrmp = ptrmp'. 
Proof.
  inductions tcbvl.
  introv Hsat1 Hsat2 Hnxt Hsub1 Hsub2.
  simpl in Hsat1.
  simpljoin1.
  destruct tcbvl'.
  simpl in Hsat2.
  simpljoin1.
  splits; auto.
  simpl in Hnxt. inverts Hnxt.

  introv Hsat1 Hsat2 Hnxt Hsub1 Hsub2.  
  destruct tcbvl'.
  simpl in Hnxt. inverts Hnxt.

  unfold llsegobjaux in Hsat1, Hsat2.
  fold llsegobjaux in Hsat1, Hsat2.
  sep destruct Hsat1.
  sep destruct Hsat2.
  simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
  inverts H4. (*Vptr _ = Vptr _*)
  simpl in Hnxt.
  simp_mt Hnxt.
  simp_mt Hnxt.
  destruct Hnxt. subst.
  unfold objaux_node in H14, H47.
  sep split in H14. sep split in H47. 
  simpl in H47. simpl in H14. simpljoin1.
  
  assert (Heq: x1 = x7 /\ x15 = x).
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tint8) (M:=M); eauto.
    mem_join_sub_solver. mem_join_sub_solver.
  }
  destruct Heq. substs. 
  (* simpl in H47. simpl in H22. simpljoin1. *)
  assert (Heq: x2 = x8 /\ x16 = x0). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT) (M:=M); eauto.
    mem_join_sub_solver. mem_join_sub_solver.    
  }
  destruct Heq. substs.
  (* simpl in H95. simpl in H24. simpljoin1.   *)
  lets H00: IHtcbvl H58 H25 H0. 
  assert (Heq0: x3 = x9 /\ x4 = x10). 
  {
    apply H00. clear H00.
    instantiate (1:=M). mem_join_sub_solver.
    mem_join_sub_solver.
  }
  destructs Heq0.
  substs.
  clear H00.
  splits. join auto. join auto. 
Qed.

Lemma tcbllsegobjaux_mpeq: 
  forall tcbvl tcbvl' tcblh locmp locmp' ptrmp ptrmp' e e0 i l a M1 M2 o1 o2 M, 
    (e, e0, M1, i, l, o1, a) |= tcbllsegobjaux tcblh tcbvl locmp ptrmp ->
    (e, e0, M2, i, l, o2, a) |= tcbllsegobjaux tcblh tcbvl' locmp' ptrmp' ->  
    tcb_linked_list_same_next tcbvl tcbvl' ->
    sub M1 M ->
    sub M2 M -> 
    locmp = locmp' /\ ptrmp = ptrmp'. 
Proof. 
  introv Hsat1 Hsat2 Hnxt Hsub1 Hsub2.
  unfold tcbllsegobjaux in *.
  lets H00: llsegobjaux_mpeq Hsat1 Hsat2 Hnxt.
  apply H00; eauto.
Qed.   

Lemma llsegobjaux_osabst_emp:
  forall tcbvl e e0 M i l o a tcblh tn locmp ptrmp,
    (e, e0, M, i, l, o, a) |= llsegobjaux tcblh tn tcbvl locmp ptrmp V_OSTCBNext -> 
    o = empabst.
Proof.
  inductions tcbvl.
  intros.
  simpl in H. simpljoin1.
  
  introv Hsat.
  simpl in Hsat. simpljoin1.
  eapply IHtcbvl; eauto.
Qed.  

Lemma llsegobjaux_precise0:  
  forall tcbvl tcbvl' tcblh tn locmp locmp' ptrmp ptrmp' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= llsegobjaux tcblh tn tcbvl locmp ptrmp V_OSTCBNext ->
    (e, e0, M2, i, l, o2, a) |= llsegobjaux tcblh tn tcbvl' locmp' ptrmp' V_OSTCBNext ->
    tcb_linked_list_same_next tcbvl tcbvl' -> 
    (forall M, sub M1 M -> sub M2 M -> M1 = M2). 
Proof.
  inductions tcbvl.
  introv Hsat1 Hsat2 Hnxt.
  simpl in Hsat1. simpljoin1.
  destruct tcbvl'. simpl in Hsat2. simpljoin1. intros. auto.
  simpl in Hnxt. tryfalse.

  introv Hsat1 Hsat2 Hnxt.
  destruct tcbvl'. simpl in Hnxt. tryfalse.
  unfold llsegobjaux in *. fold llsegobjaux in *.
  sep destruct Hsat1. sep destruct Hsat2.
  sep split in Hsat1. sep split in Hsat2.
  unfold objaux_node in *. sep split in Hsat1. sep split in Hsat2.
  simpl in Hsat1; simpl in Hsat2; simpljoin1.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end. 
  simpl in Hnxt.
  simp_mt Hnxt.
  simp_mt Hnxt.
  destruct Hnxt.
  subst.
  introv Hsub1 Hsub2.
  
  assert (Heqs: x1 = x7 /\ x17 = x11). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tint8); eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
  }
  destruct Heqs. subst.
  assert (Heqs: x2 = x8 /\ x29 = x23). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT); eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
  }
  destruct Heqs. subst.
  mem_eq_solver2.
  lets H00: IHtcbvl H34 H22 H3.  
  eapply H00.
  instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
Qed.   

Lemma tcbllsegobjaux_precise':
  forall tcbvl tcbvl' tcblh locvl locvl' ptrvl ptrvl' e e0 i l a M1 M2 o1 o2,
    (e, e0, M1, i, l, o1, a) |= tcbllsegobjaux tcblh tcbvl locvl ptrvl ->
    (e, e0, M2, i, l, o2, a) |= tcbllsegobjaux tcblh tcbvl' locvl' ptrvl' ->
    tcb_linked_list_same_next tcbvl tcbvl' ->
    (forall M, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2 Hnxt.
  unfold tcbllsegobjaux in *.
  assert (Hemp1: o1 = empabst).
  { eapply llsegobjaux_osabst_emp in Hsat1. auto. }
  assert (Hemp2: o2 = empabst).
  { eapply llsegobjaux_osabst_emp in Hsat2. auto. }
  subst o1. subst o2.
  split.
  2: {
    intros. auto.
  }
  eapply llsegobjaux_precise0; eauto.
Qed.


Require Import Aarray_new_common.
Require Import Maps.

Lemma struct_atom_val_eq_vl_eq: 
  forall vl1 vl2, 
    struct_atom_val_eq vl1 vl2 os_ucos_h.service_obj_t ->
    vl1 = vl2.
Proof.
  intros.
  destruct vl1; destruct vl2; tryfalse.
  auto.
  simpl in H. destruct H. subst v0.
  destruct vl1; destruct vl2; tryfalse.
  auto.
  simpl in H0. destruct H0. subst v1.
  destruct vl1; destruct vl2; tryfalse.
  auto.
Qed.   
          
Lemma Aarray_new'_vll_eq:
  forall vll vll' M1 M2 o1 o2 e e0 i l a n adr M, 
    new_array_type_vallist_match os_ucos_h.service_obj_t vll -> 
    new_array_type_vallist_match os_ucos_h.service_obj_t vll' -> 
    (e, e0, M1, i, l, o1, a) |= Aarray_new' adr n os_ucos_h.service_obj_t vll ->
    (e, e0, M2, i, l, o2, a) |= Aarray_new' adr n os_ucos_h.service_obj_t vll' -> 
    sub M1 M ->
    sub M2 M ->
    vll = vll'. 
Proof.
  inductions vll.
  intros.
  destruct vll'.
  auto.
  unfold Aarray_new' in H.
  destruct n.
  simpl in H0. tryfalse.
  tryfalse.

  introv Hmt1 Hmt2 Hsat1 Hsat2.
  destruct vll'.
  destruct n.
  simpl in Hsat1. tryfalse.
  simpl in Hsat2. tryfalse.

  destruct n.
  simpl in Hsat1. tryfalse.
  destruct adr.
  eapply Aarray_new'_succ_imp in Hsat1; eauto.
  eapply Aarray_new'_succ_imp in Hsat2; eauto.
  introv Hsub1 Hsub2.

  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  assert (Hsub1': sub x6 M) by mem_join_sub_solver.
  assert (Hsub2': sub x0 M) by mem_join_sub_solver.
  lets H00: IHvll H10 H5 Hsub1' Hsub2'.
  unfold new_array_type_vallist_match in Hmt1.
  fold new_array_type_vallist_match in Hmt1.
  unfold os_ucos_h.service_obj_t in Hmt1.
  fold os_ucos_h.service_obj_t in Hmt1.
  destruct Hmt1. auto.
  unfold new_array_type_vallist_match in Hmt2.
  fold new_array_type_vallist_match in Hmt2.
  unfold os_ucos_h.service_obj_t in Hmt2.
  fold os_ucos_h.service_obj_t in Hmt2.
  destruct Hmt2. auto.

  unfold Aarray_new' in H9.
  unfold os_ucos_h.service_obj_t in H9. fold os_ucos_h.service_obj_t in H9.
  unfold Aarray_new' in H4.
  unfold os_ucos_h.service_obj_t in H4. fold os_ucos_h.service_obj_t in H4.
  apply astar_r_aemp_elim in H9.
  apply astar_r_aemp_elim in H4.
  unfold new_array_type_vallist_match in Hmt1.
  fold new_array_type_vallist_match in Hmt1.
  unfold os_ucos_h.service_obj_t in Hmt1.
  fold os_ucos_h.service_obj_t in Hmt1.
  destruct Hmt1. 
  unfold new_array_type_vallist_match in Hmt2.
  fold new_array_type_vallist_match in Hmt2.
  unfold os_ucos_h.service_obj_t in Hmt2.
  fold os_ucos_h.service_obj_t in Hmt2.
  destruct Hmt2.
  assert (Hveq: struct_atom_val_eq a v os_ucos_h.service_obj_t). 
  {
    eapply Astruct_vl_eq; eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
  }
  apply struct_atom_val_eq_vl_eq in Hveq.
  subst a.
  congruence.
Qed.   
  
 
Lemma Aarray_new_vll_eq:
  forall vll vll' M1 M2 o1 o2 e e0 i l a adr M n, 
    new_array_type_vallist_match os_ucos_h.service_obj_t vll -> 
    new_array_type_vallist_match os_ucos_h.service_obj_t vll' -> 
    (e, e0, M1, i, l, o1, a) |= Aarray_new adr (Tarray os_ucos_h.service_obj_t n) vll ->
    (e, e0, M2, i, l, o2, a) |= Aarray_new adr (Tarray os_ucos_h.service_obj_t n) vll' -> 
    sub M1 M ->
    sub M2 M ->
    vll = vll'. 
Proof.
  intros.
  unfold Aarray_new in *.
  unfold os_ucos_h.service_obj_t in *.
  fold os_ucos_h.service_obj_t in *.
  eapply Aarray_new'_vll_eq; eauto.
Qed. 
              
Lemma AObjArr_vll_eq:
  forall vll vll' M1 M2 o1 o2 e e0 i l a M, 
    (e, e0, M1, i, l, o1, a) |= AObjArr vll ->
    (e, e0, M2, i, l, o2, a) |= AObjArr vll' -> 
    sub M1 M ->
    sub M2 M ->
    vll = vll'.
Proof.
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  unfold AObjArr in *. 
  sep destruct Hsat1.
  sep split in Hsat1.
  sep destruct Hsat2.
  sep split in Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H12. simpl in H6.
  simpljoin1.
  rewrite H23 in H12. inverts H12.
  assert (Hsub1': sub x7 M) by mem_join_sub_solver.
  assert (Hsub2': sub x1 M) by mem_join_sub_solver.
  lets H00: mapstoval_true_vptr_eq H24 H15 Hsub1' Hsub2'.
  destruct H00.
  subst x.
  eapply Aarray_new_vll_eq; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed. 
      
  
Lemma RHL_OBJ_vl_eq_eib_eq:
  forall vl obj1 obj2 vhold,   
    RHL_OBJ_P vl obj1 vhold -> 
    RHL_OBJ_P vl obj2 vhold ->
    obj1 = obj2. 
Proof.
  introv Hre1 Hre2.
  unfold RHL_OBJ_P in *.
  destruct obj1 as (e1 & tp1).
  destruct obj2 as (e2 & tp2).
  specialize (Hre1 e1 tp1 (eq_refl _)).
  specialize (Hre2 e2 tp2 (eq_refl _)).
  destruct Hre1.
  destruct Hre2.
  rewrite H in H1.
  inverts H1.
  destruct H0; destruct H2.
  destruct H0. destruct H1.
  destructs H0. destructs H1. rewrite H2 in H4. inverts H4.
  congruence.
  destruct H0. destructs H0.
  destruct H1. destruct H1. rewrite H2 in H4. inverts H4.
  tryfalse.
  destructs H1. rewrite H2 in H4. inverts H4.
  destruct H1.
  destructs H1.
  destruct H0.
  destruct H0. rewrite H2 in H4. inverts H4. tryfalse.
  destruct H0.
  rewrite H2 in H4. inverts H4.
  destruct H0. destruct H1. destruct H0. destruct H1.
  congruence.
  destruct H0. destruct H1. rewrite H2 in H3. inverts H3.
  destruct H1.
  destruct H0. destruct H1.
  rewrite H2 in H3. inverts H3.
  destruct H0. destruct H1.
  congruence.
Qed.  

Lemma RHL_OBJ_vl_eq_obj_ptreq:
  forall vl obj1 obj2 vhold1 vhold2 id1 id2 att1 att2,  
    RHL_OBJ_P vl obj1 vhold1 -> 
    RHL_OBJ_P vl obj2 vhold2 -> 
    obj1 = (objid id1, att1) ->
    obj2 = (objid id2, att2) ->
    id1 = id2. 
Proof.
  introv Hre1 Hre2 Heib1 Heib2.
  unfold RHL_OBJ_P in *.
  destruct obj1 as (e1 & att1').
  destruct obj2 as (e2 & att2').
  specialize (Hre1 e1 att1' (eq_refl _)).
  specialize (Hre2 e2 att2' (eq_refl _)).
  inverts Heib1. inverts Heib2.
  destruct Hre1.  destruct Hre2.
  rewrite H in H1. inverts H1.
  destruct H0; destruct H2.
  destruct H0. destruct H1. destructs H0. destructs H1.
  inverts H0. inverts H1.
  congruence.
  destruct H1. destruct H1. tryfalse.
  destruct H1. tryfalse.
  destruct H0.
  destruct H0. inverts H0.
  destruct H0. inverts H0.
  destruct H0. destruct H1.
  destruct H0. destruct H1.
  congruence.
  destruct H0. destruct H1. rewrite H2 in H3. tryfalse.
  destruct H0. tryfalse.
Qed.   

Lemma ObjArray_P_vl_eq_mp_eq: 
  forall objl i absobjs1 absobjs2 vhold,  
    ObjArray_P i objl absobjs1 vhold ->
    ObjArray_P i objl absobjs2 vhold -> 
    absobjs1 = absobjs2. 
Proof.
  inductions objl.
  intros.
  simpl in H. simpl in H0. congruence.
  introv Hep1 Hep2.
  simpl in Hep1.
  simpl in Hep2.
  simpljoin1.
  inverts H.
  lets H00: IHobjl H8 H4.
  assert (Heibeq: x5 = x1).
  {
    eapply RHL_OBJ_vl_eq_eib_eq; eauto.
  }
  subst x4. subst x5. 
  eapply join_unique; eauto.
Qed.

Lemma ObjArray_P_vl_eq_mp_ptreq: 
  forall objl i absobjs1 absobjs2 vhold1 vhold2 idxv id1 att1 id2 att2, 
    ObjArray_P i objl absobjs1 vhold1 ->
    ObjArray_P i objl absobjs2 vhold2 -> 
    get absobjs1 idxv = Some (objid id1, att1) ->
    get absobjs2 idxv = Some (objid id2, att2) ->  
    id1 = id2. 
Proof.
  inductions objl.
  intros.
  simpl in H. simpl in H0. subst absobjs1. subst absobjs2. 
  rewrite map_emp_get in H1. tryfalse.
  
  introv Hep1 Hep2 Hget1 Hget2.
  simpl in Hep1. simpl in Hep2.
  simpljoin1.
  inverts H.
  assert (Hcases: idxv = x \/ idxv <> x) by tauto.
  destruct Hcases.
  subst x.
  assert (Hget1': get absobjs1 idxv = Some x5).
  {
    eapply join_sig_get; eauto.
  }
  assert (Hget2': get absobjs2 idxv = Some x1). 
  {
    eapply join_sig_get; eauto.
  }
  rewrite Hget1' in Hget1. rewrite Hget2' in Hget2.
  inversion Hget1. inversion Hget2.
  eapply RHL_OBJ_vl_eq_obj_ptreq with (obj1:=x5) (obj2:=x1); eauto.
  assert (Hget1': get x4 idxv = Some (objid id1, att1)).
  {
    eapply join_sig_get_r; eauto.
  }
  assert (Hget2': get x0 idxv = Some (objid id2, att2)). 
  {
    eapply join_sig_get_r; eauto.
  }
  eapply IHobjl with (absobjs1:=x4) (absobjs2:=x0); eauto.
Qed.   

Lemma AObjs_vl_mp_eq: 
  forall objl objl' absobjs absobjs' ecbls ecbls' vhold e e0 M1 M2 i l o1 o2 a M,   
  (e, e0, M1, i, l, o1, a) |= AObjs objl absobjs ecbls vhold ->
  (e, e0, M2, i, l, o2, a) |= AObjs objl' absobjs' ecbls' vhold ->   
  sub M1 M -> 
  sub M2 M -> 
  objl = objl' /\ absobjs = absobjs'. 
Proof.
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  unfold AObjs in *. 
  sep split in Hsat1.
  sep split in Hsat2. 
  lets Hvleq: AObjArr_vll_eq Hsat1 Hsat2 Hsub1 Hsub2.
  subst objl'. 
  split; auto.
  eapply ObjArray_P_vl_eq_mp_eq; eauto.
Qed.

Lemma AObjs_vl_mpptr_eq: 
  forall objl objl' absobjs absobjs' ecbls ecbls' vhold vhold' e e0 M1 M2 i l o1 o2 a M,   
    (e, e0, M1, i, l, o1, a) |= AObjs objl absobjs ecbls vhold ->
    (e, e0, M2, i, l, o2, a) |= AObjs objl' absobjs' ecbls' vhold' ->  
    sub M1 M -> 
    sub M2 M -> 
    objl = objl' /\
      (forall idxv id1 att1 id2 att2,
          get absobjs idxv = Some (objid id1, att1) ->
          get absobjs' idxv = Some (objid id2, att2) ->  
          id1 = id2).  
Proof. 
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  unfold AObjs in *.
  sep split in Hsat1.
  sep split in Hsat2.
  lets Hvleq: AObjArr_vll_eq Hsat1 Hsat2 Hsub1 Hsub2.
  subst objl'. 
  split; auto.
  intros.  
  eapply ObjArray_P_vl_eq_mp_ptreq with (absobjs1:=absobjs) (absobjs2:=absobjs'); eauto. 
Qed. 


Lemma AOBJ_precise: 
  forall objl objl' absobjs absobjs' ecbls ecbls' vhold vhold'          
         tcbh tcbvl tcbvl' fecbh fecbh' fecbvl fecbvl'  e e0 i l a M1 M2 o1 o2,          
    (e, e0, M1, i, l, o1, a) |= AOBJ objl absobjs ecbls vhold tcbh tcbvl fecbh fecbvl ->
    (e, e0, M2, i, l, o2, a) |= AOBJ objl' absobjs' ecbls' vhold' tcbh tcbvl' fecbh' fecbvl' ->  
    tcb_linked_list_same_next tcbvl tcbvl' -> 
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  introv Hsat1 Hsat2 Hnxt Hsubm1 Hsubm2 Hsubo1 Hsubo2.
  unfold AOBJ in Hsat1, Hsat2.
  sep destruct Hsat1.
  sep destruct Hsat2.
  sep split in Hsat1.
  sep split in Hsat2.
  rename H into H_.
  rename H0 into H0_.
  rename Hsat1 into H.
  rename Hsat2 into H0.

  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hhobjs: HObjs_precise' _H _H0.
  lets Hhobjs': precise'2precise Hhobjs. 
  clear _H _H0.
  
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Haobjs: AObjs_prop_precise' _H _H0. 
  lets Haobjs': precise'2precise Haobjs.
  clear _H _H0.

  lets Hobjaux: tcbllsegobjaux_precise' H H0 Hnxt. 
  lets Hobjaux': precise'2precise Hobjaux.

  eapply precise'2precise;eauto.

  simpljoin1.

  Ltac XX x1 x2:= 
    match goal with
      H: forall _, _ -> _ -> ?R |- ?R => apply H with (x1:=x2); mem_join_sub_solver
    end. 

  split.
  introv Hsub1 Hsub2.
  simpl_sat H; simpl_sat H0; simpljoin1.
  mem_eq_solver2; try XX M M. 
      
  introv Hsub1 Hsub2.
  mem_eq_solver2; try XX o o. 

Qed.


(*main lemmas*)
Lemma OSInv_precise : precise OSInv. 
Proof.
  unfold precise; intros.
  destruct s; destruct r; destruct t; destruct p; destruct s; destruct p; simpl substmo in *.
  unfold OSInv in *.
  sep destruct H. sep destruct H0.

  sep_rmb_trms_in H (AOSTCBList', AOSTCBFreeList', Aexists).
  sep_rmb_trms_in H0 (AOSTCBList', AOSTCBFreeList', Aexists).
  sep remember (4::nil)%nat in H;
    sep remember (4::nil)%nat in H0.
  simpl in H, H0; simpljoin1.

  assert (
      forall (M: mem) (o0 : osabst),
        sub x43 M -> sub x37 M -> sub x46 o0 -> sub x40 o0 ->  
        x43 = x37 /\ x46 = x40 
    ).
  {
    clear H18 H13.
    rename H17 into H; rename H12 into H0.
    
    intros.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1: AOSEventFreeList_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx4: AECBList_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx5: AOSMapTbl_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx6: AOSUnMapTbl_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx7: AOSTCBPrioTbl_precise _H _H0; clear _H _H0.

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx8: AOSIntNesting_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx11: AOSRdyTblGrp_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx12: AOSTime_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx13: Aabsdata_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx14: Aabsdata_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx15: Aabsdata_precise _H _H0; clear _H _H0.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx16: Aabsdata_precise _H _H0; clear _H _H0.

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx17: AGVars_precise _H _H0; clear _H _H0.

    sep split in H; sep split in H0.
    lets Hx18: A_isr_is_prop_precise H H0; clear H H0.
    
    repeat match goal with 
           | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
             |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
                           apply (Hx M0 o3);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
           end. 
    repeat match goal with 
           | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
             |- _ => assert (m1 = m2);[jeat | ]; subst m1 
           end.
    auto.
  }

  (**)
  clear H17 H12. 

  assert (x32 = x13).
  {
    simpl_sat H18; simpl_sat H13; simpljoin1.
    eapply AOSTCBList'_ct_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.

  sep normal in H18. sep destruct H18.
  sep normal in H13. sep destruct H13. 
  rename H into H_prec0.

  rename H18 into H. rename H13 into H0.
  elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
  assert (H18:=H). assert (H13:=H0). 
  elim_sep_conj1 H H'_. elim_sep_conj1 H0 H0'_.
  
  assert (x15 = x34). 
  {
    eapply AOSTCBFreeList'_pfree_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  subst.
  
  (* the two pieces of mems for AOSTCBList' are the same *)
  assert (Hmoeq: x56 = x60 /\ x58 = x62).  
  {
    lets H00: AOSTCBList'_precise H'_ H0'_.
    apply (H00 M o); mem_join_sub_solver.
  }
  destruct Hmoeq; subst.
  lets Htcbheq: AOSTCBList'_tcb_list_same_head H'_ H0'_.
  subst.
  lets Htcblsamenxt: AOSTCBList'_tcb_list_same_next_intro' H'_ H0'_.

  lets Hxfreelst: AOSTCBFreeList'_precise H H0. 
  lets Hxlst: AOSTCBList'_precise H'_ H0'_.

  lets Hxcnu: AOBJ_precise H_ H0_ Htcblsamenxt; clear H_ H0_ Htcblsamenxt.

  repeat match goal with 
         | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
            |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
                           apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
         end. 
  repeat match goal with 
         | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
           |- _ => assert (m1 = m2);[jeat | ]; subst m1 
         end.
  auto.

Qed.

(*----is isr irrelvant lemmas----*)
Ltac destr_and_inst H v:= let s := fresh v in (destruct H as [s H]; exists s).

Ltac simpl_sat_goal :=
  unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem.

Ltac cancel_pure H := sep split in H; sep split; auto.

Ltac solve_sat H := simpl_sat H; simpl_sat_goal; simpljoin1; do 6 eexists; repeat(split; eauto); eauto.

Ltac get_isr_is_prop H :=
  unfold OSInv in H; simpljoin1; sep destruct H; sep_rmb_trms_in H A_isr_is_prop; simpl in H; simpljoin1. 

Ltac solve_sat_auto :=
  match goal with
    | H: _ |= ?P ** ?Q |- _ => sep remember (1::nil)%nat in H; solve_sat H; solve_sat_auto
    | _ => idtac
  end.


Lemma is_isr_irrel_Astruct' :
  forall vl l d a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= Astruct' l d vl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= Astruct' l d vl.
Proof.
  inductions vl; intros.
  destruct d; simpl in H; simpl; auto.
  
  destruct d; simpl in H; tryfalse.
          
  destruct t; destruct l;
  try solve [
        simpl in H; simpl; simpljoin1;
        do 6 eexists; repeat(split; eauto);
        apply OSAbstMod.join_emp; auto;
        eapply IHvl];
  try solve [
        simpl; eapply IHvl; eauto].
Qed.

Lemma is_isr_irrel_Astruct :
  forall vl l t a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= Astruct l t vl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= Astruct l t vl.
Proof.
  unfold Astruct; intros; destruct t; tryfalse. 
  eapply is_isr_irrel_Astruct'; eauto.
Qed.

Lemma is_isr_irrel_node :
  forall vl v t a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= node v vl t ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= node v vl t.
Proof.
  unfold node; intros.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  
  eapply is_isr_irrel_Astruct; eauto.
Qed.

Lemma is_isr_irrel_Aarray' :
  forall vl l n t a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= Aarray' l n t vl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= Aarray' l n t vl.
Proof.
  inductions vl; destruct n; intros.
  simpl in H; simpl;auto.
  simpl in H; tryfalse.
  
  simpl in H; tryfalse.
  simpl in H; destruct l; simpl.
  simpl in H; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  apply OSAbstMod.join_emp; auto.
Qed.

Lemma is_isr_irrel_Aarray :
  forall vl l t a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= Aarray l t vl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= Aarray l t vl.
Proof.
  unfold Aarray; intros.
  destruct t; tryfalse.
  eapply is_isr_irrel_Aarray'; eauto.
Qed.

Lemma is_isr_irrel_sllseg :
  forall l head tail t next a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= sllseg head tail l t next ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= sllseg head tail l t next.
Proof.
  inductions l; intros.
  simpl in H; simpl; simpljoin1; splits; auto.
  unfolds; auto.
  
  unfold sllseg in H; fold sllseg in H.
  unfold sllseg; fold sllseg.
  sep split in H; sep split; auto.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_node; eauto.
Qed.

Lemma is_isr_irrel_sll :
  forall l head t next a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= sll head l t next ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= sll head l t next.
Proof.
  unfold sll; intros.      
  eapply is_isr_irrel_sllseg; eauto.
Qed.

Lemma is_isr_AOSEvent :
  forall v osevent etbl a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= AOSEvent v osevent etbl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= AOSEvent v osevent etbl.
Proof.
  unfold AOSEvent; intros.
  do 2 destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  eapply is_isr_irrel_node; eauto.

  (* do 6 eexists; repeat (split; eauto). *)
  unfold AOSEventTbl in *.
  sep split in H7; sep split; auto.
  eapply is_isr_irrel_Aarray; eauto.
Qed.   

Lemma is_isr_AEventData :
  forall osevent d a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= AEventData osevent d ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= AEventData osevent d.
Proof.
  unfold AEventData; intros.
  destruct d; try (sep split in H; sep split; auto).
Qed. 

Lemma is_isr_AEventNode :
  forall v osevent etbl d a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= AEventNode v osevent etbl d ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= AEventNode v osevent etbl d.
Proof.
  unfold AEventNode in *; intros.
  simpl_sat H; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat (split; eauto).
  clear - H3.
  
  eapply is_isr_AOSEvent; eauto.
  clear - H4.
  eapply is_isr_AEventData; eauto.
Qed.

Lemma is_isr_qblkf_evsllseg :
  forall vl head tail ecbls a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= evsllseg head tail vl ecbls  ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= evsllseg head tail vl ecbls.
Proof.
  inductions vl; intros.
  simpl in H; simpl; simpljoin1.
  splits; eauto.
  unfolds; auto.
  
  unfold evsllseg in H; fold evsllseg in H.
  unfold evsllseg; fold evsllseg.
  destruct ecbls; tryfalse; destruct a.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  clear - H4.
  
  eapply is_isr_AEventNode; eauto.
Qed.


Lemma is_isr_dllseg :
  forall l head headprev tail tailnext t prev next a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= dllseg head headprev tail tailnext l t prev next->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= dllseg head headprev tail tailnext l t prev next.
Proof.
  inductions l; intros.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; auto.
  unfolds; auto.

  unfold dllseg in H; fold dllseg in H.
  unfold dllseg; fold dllseg.
  sep split in H; sep split; auto.
  destr_and_inst H v.
  cancel_pure H.

  solve_sat H.
  eapply is_isr_irrel_node; eauto.
Qed.


Lemma is_isr_tcbdllseg :
  forall head headprev tail tailnext l a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= tcbdllseg head headprev tail tailnext l->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= tcbdllseg head headprev tail tailnext l.
Proof.
  unfold tcbdllseg; intros.
  eapply is_isr_dllseg; eauto.
Qed.

(*--end--*)

Lemma is_isr_sllsegfreeflag :
  forall l head tailnext next a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= sllsegfreeflag head tailnext l next->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= sllsegfreeflag head tailnext l next.
Proof.
  inductions l; intros.
  simpl in H; simpljoin1.
  simpl.
  unfold emposabst; auto.

  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep destruct H.
  (* do 2 destruct H. *)
  exists x0 x1 x2 x3.
  (* exists x0 x1. *)
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl. 
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
Qed.

Lemma is_isr_sllfreeflag :
  forall head l a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= sllfreeflag head l->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= sllfreeflag head l.
Proof.
  intros.
  unfold sllfreeflag in *.
  eapply is_isr_sllsegfreeflag; eauto.
Qed.

Lemma is_isr_dllsegflag :
  forall l head tailnext next a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= dllsegflag head tailnext l next->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= dllsegflag head tailnext l next.
Proof.
  inductions l; intros.
  simpl in H; simpljoin1.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst; auto.
  unfolds; auto.

  unfold dllsegflag in *; fold dllsegflag in *.
  do 2 destruct H.
  exists x0 x1.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl.
  do 6 eexists; splits; eauto.
Qed.

Lemma is_isr_tcbdllflag :
  forall head l a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= tcbdllflag head l->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= tcbdllflag head l.
Proof.
  intros.
  unfold tcbdllflag in *.
  eapply is_isr_dllsegflag; eauto.
Qed.


Lemma is_isr_irrel_Aarray_new' :
  forall vl l n t a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= Aarray_new' l n t vl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= Aarray_new' l n t vl.
Proof.
  inductions vl; destruct n; intros.
  simpl in H; simpl;auto.
  simpl in H; tryfalse.
  
  simpl in H; tryfalse.
  simpl in H. destruct t; destruct a ; tryfalse. 
  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct a;tryfalse. destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  apply OSAbstMod.join_emp; auto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Aarray'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Aarray'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Astruct'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Astruct'; eauto.
Qed.

Lemma is_isr_irrel_Aarray_new :
  forall vl l t a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= Aarray_new l t vl ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= Aarray_new l t vl.
Proof.
  intros.
  unfold Aarray_new in *.
  destruct t; tryfalse.
  eapply is_isr_irrel_Aarray_new'. apply H.
Qed.

Lemma is_isr_AObjArr :
  forall vll a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= AObjArr vll ->
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= AObjArr vll. 
Proof.
  intros.
  unfold AObjArr in *.
  do 2 destr_and_inst H head.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 5 eexists; repeat (split; eauto). 
  do 6 eexists. split; eauto. split; eauto. apply join_comm.
  apply join_emp. eauto. 
  split. eauto. split. apply join_comm . apply join_emp. eauto. 
  split. eapply is_isr_irrel_Aarray_new. eauto.
  split; eauto.
  simpl. split; eauto. unfold emposabst. auto.
Qed.


Lemma is_isr_llsegobjaux: 
  forall l a b c ir ir' ie si si' cs x aop head locmp ptrmp, 
    (a, b, c, ir, (ie, si, cs), x, aop) |= llsegobjaux head Vnull l locmp ptrmp V_OSTCBNext ->
    (a, b, c, ir', (ie, si', cs), x, aop) |= llsegobjaux head Vnull l locmp ptrmp V_OSTCBNext. 
Proof.
  inductions l.
  introv Hsat.
  simpl in Hsat. simpljoin1.
  simpl.
  do 6 eexists.
  splits; eauto.
  join auto. join auto. splits; auto. unfold emposabst. auto.
  unfold emposabst.
  do 6 eexists. splits; auto. join auto. join auto. 

  introv Hsat.
  unfold llsegobjaux in Hsat. fold llsegobjaux in Hsat.
  sep destruct Hsat.
  unfold llsegobjaux. fold llsegobjaux.

  exists x0 x1 x2 x3 x4 x5.
  sep split in Hsat.
  sep split; eauto.

  sep remember (1::nil)%nat in Hsat.
  solve_sat Hsat.
Qed.

Lemma is_isr_tcbdllsegobjaux: 
  forall a b c ir ir' ie si si' cs x aop tcbh tcbvl locvl ptrvl, 
    (a, b, c, ir, (ie, si, cs), x, aop) |= tcbllsegobjaux tcbh tcbvl locvl ptrvl ->
    (a, b, c, ir', (ie, si', cs), x, aop) |= tcbllsegobjaux tcbh tcbvl locvl ptrvl.  
Proof.
  introv Hsat.
  unfold tcbllsegobjaux in *.
  sep split in Hsat.
  sep split; eauto.
  eapply is_isr_llsegobjaux; eauto.
Qed.


Lemma AOBJ_isr_is_irrel: 
  forall a b c ir ir' ie si si' cs x aop objl absobjs ecbls vhold tcbh tcbvl fecbh fecbvl,      
    (a, b, c, ir, (ie, si, cs), x, aop) |= AOBJ objl absobjs ecbls vhold tcbh tcbvl fecbh fecbvl->  
    (a, b, c, ir', (ie, si', cs), x, aop) |= AOBJ objl absobjs ecbls vhold tcbh tcbvl fecbh fecbvl.  
Proof.
  introv Hsat.
  unfold AOBJ in *.
  unfold AObjs in *.
  sep normal in Hsat. sep normal. 
  sep destruct Hsat.
  exists x0 x1.

  sep split in Hsat. sep split; eauto.

  clear -Hsat.
  sep remember (1::nil)%nat in Hsat.
  solve_sat Hsat.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AObjArr; eauto. 
  eapply is_isr_tcbdllsegobjaux; eauto.
  
Qed.


(*main lemma*)

Lemma OSInv_isr_is_irrel :
  forall a b c ir ir' ie0 si si' cs0 x aop,
    (a, b, c, ir, (ie0, si, cs0), x, aop) |= OSInv ->
    isr_is_prop ir' si' -> 
    (a, b, c, ir', (ie0, si', cs0), x, aop) |= OSInv.
Proof.
  unfold OSInv; intros.
  rename H0 into Hxxx.
  do 19 destr_and_inst H v. 

  sep_rmb_trms_in H AOSEventFreeList. 
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto. join auto.
  do 4 eexists; do 3 exists empabst.
  splits; eauto. join auto.
  symmetry; eapply ecbf_sllseg_osabst_emp; eauto.
  apply map_join_emp.
  eexists. splits; eauto.
  unfold emposabst. auto. unfold emposabst. auto.
  
  clear - H10.
  (*ecbf_sll isr_is_irrel*)
  unfold ecbf_sll in *.
  inductions v.
  simpl in H10; simpljoin1.
  simpl; intuition.
  unfolds; auto.

  unfold ecbf_sllseg in H10; fold ecbf_sllseg in H10.
  unfold ecbf_sllseg; fold ecbf_sllseg.
  do 3 destr_and_inst H10 v.
  
  sep split in H10; sep split; auto.
  simpl_sat H10.
  simpl_sat_goal. 
  simpljoin1.

  do 3 eexists; do 3 exists empabst.
  repeat (split; eauto).
  lets Hx : node_osabst_emp H6; substs. 
  
  eapply is_isr_irrel_node; eauto.
  
  do 6 eexists; repeat(split; eauto).
  eapply OSAbstMod.join_emp; auto.
  lets Hx: Aarray_osabst_emp H11; substs. 

  eapply is_isr_irrel_Aarray; eauto.

  (*  do 6 eexists; repeat(split; eauto). *)
  (* eapply OSAbstMod.join_emp; auto. *)
  (* lets Hx': Aarray_osabst_emp H17; substs.  *)

  (* eapply is_isr_irrel_Aarray; eauto. *)
  (* (*end of ecbf_sll isr_is_irrel*)  *)
  
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H7.
  
  (*AECBList is_isr_irrel*)
  unfold AECBList in *.
  destr_and_inst H7 v.
  sep split in H7; sep split; auto.
  simpl_sat H7; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear - H5.

  eapply is_isr_qblkf_evsllseg; eauto.

  sep remember (1::nil)%nat in H8.
  simpl_sat H8; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H11.
  unfold AOSMapTbl in *; unfold GAarray in *.
  destr_and_inst H11 v.
  simpl_sat H11; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
  clear - H12 Hxxx.

  sep remember (1::nil)%nat in H12.
  simpl_sat H12; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.
  unfold AOSUnMapTbl in *; unfold GAarray in *.
  destr_and_inst H4 v.
  simpl_sat H4; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
  clear - H5 Hxxx.

  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.
  unfold AOSTCBPrioTbl in *.
  sep split in H4; sep split; auto.
  simpl_sat H4; simpl_sat_goal; simpljoin1.
  
  do 6 eexists; repeat (split; eauto).
  unfold GAarray in *.
  destr_and_inst H6 v.
  simpl_sat H6; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
  do 6 eexists; repeat(split; eauto).
  eexists; simpl in H12; simpl; eauto.
  (* do 6 eexists; repeat(split; eauto). (* new add *) *)
  (* eexists; simpl in H17; simpl; eauto. (* new add *) *)
  clear - H5 Hxxx.

  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H5 Hxxx.
  
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.

  unfold AOSTCBList' in *.
  destruct H4.
  left.
  do 4 destruct H.
  exists x0 x1 x2 x4.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  do 6 eexists; splits; eauto.
  eapply is_isr_tcbdllseg; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  eapply is_isr_tcbdllseg; eauto.  
  eapply is_isr_tcbdllflag; eauto.

  right.
  destruct H.
  exists x0.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  unfold tcblist in *.
  sep split in H15.
  sep split; auto.
  eapply is_isr_tcbdllseg; eauto.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_tcbdllflag; eauto.
  
  clear - H5 Hxxx.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear - H4.
  unfold AOSTCBFreeList' in *.
  simpl_sat H4; simpljoin1.
  simpl_sat_goal.
  do 6 eexists; splits; eauto.
  destruct H4.
  left.
  unfold TCBFree_Not_Eq in *.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_irrel_sll; eauto.  
  eapply is_isr_sllfreeflag; eauto.

  right.
  unfold TCBFree_Eq in *.
  do 3 destruct H.
  exists x2 x6 x7.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_irrel_Astruct; eauto.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  exists x32. exists x33. do 6 eexists. 
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_irrel_sll; eauto.
  eapply is_isr_sllfreeflag; eauto.
  
  clear - H5 Hxxx.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear - H4.
  unfold AOSRdyTblGrp in *.
  cancel_pure H4; clear - H4.
  solve_sat H4.
  unfold AOSRdyTbl in *.
  cancel_pure H3.
  unfold GAarray in *.
  destr_and_inst H3 v.
  solve_sat H3.
  eapply is_isr_irrel_Aarray; eauto.
  clear - H5 Hxxx.

  sep remember ((7::nil)%nat) in H5.
  sep remember ((7::nil)%nat).
  sep normal in H5. sep destruct H5.
  sep normal. 
  exists x x0. 
  rewrite <- HeqH. 
  solve_sat H5. 
  eapply AOBJ_isr_is_irrel; eauto. 
  clear H5. 

  sep split in H6. sep split; eauto.
  sep remember (1::nil) in H6.
  solve_sat H6.
  clear H7.
  sep remember (1::nil) in H8.
  solve_sat H8.
  sep remember (1::nil) in H10.
  solve_sat H10.
  sep remember (1::nil) in H13.
  solve_sat H13.
  sep remember (1::nil) in H16.
  solve_sat H16.
  sep remember (1::nil) in H19.
  solve_sat H19.
  unfold A_isr_is_prop.
  exists ir'. exists si'.
  sep split; eauto.
  simpl.
  destruct H22. simpl_sat H0. simpljoin1.
  split; auto. unfold emposabst. auto.
Qed.  


(*----good inv asrt lemmas ----*)
Lemma GoodInvAsrt_Astruct' :
  forall vl l d, GoodInvAsrt (Astruct' l d vl).
Proof.
  inductions vl; intros.
  destruct d; simpl; auto.
  destruct d; simpl; auto.
  destruct t; destruct l; try solve [simpl; split; auto];
  try solve [simpl; apply IHvl].
Qed.

Lemma GoodInvAsrt_Astruct :
  forall vl l t, GoodInvAsrt (Astruct l t vl).
Proof.
  intros.
  destruct t; simpl; auto.
  apply GoodInvAsrt_Astruct'.
Qed.

Lemma GoodInvAsrt_Aarray' :
  forall vl l n t, GoodInvAsrt (Aarray' l n t vl).
Proof.
  inductions vl; intros.
  destruct n; simpl; auto.
  destruct n; destruct l; simpl; auto.
Qed.

Lemma GoodInvAsrt_Aarray :
  forall vl l t, GoodInvAsrt (Aarray l t vl).
Proof.
  intros.
  destruct t; simpl; auto.
  apply GoodInvAsrt_Aarray'.
Qed.

Lemma GoodInvAsrt_AEventNode : forall v1 v2 v3 v4,  GoodInvAsrt (AEventNode v1 v2 v3 v4).
Proof.
  intros.
  unfold AEventNode; unfold GoodInvAsrt; fold GoodInvAsrt; split.

  unfold AOSEvent.
  unfold GoodInvAsrt; fold GoodInvAsrt; intros.
  repeat(split; auto).

  apply GoodInvAsrt_Astruct.

  apply GoodInvAsrt_Aarray.
  unfold AEventData; destruct v4; try solve [simpl; auto].
Qed.

Lemma GoodInvAsrt_dllseg :
  forall vl head headprev tail tailnext t prev next,
    GoodInvAsrt (dllseg head headprev tail tailnext vl t prev next).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; split; auto.
  intros.
  repeat (split; auto).
  unfold Astruct; destruct t; simpl; auto.

  apply GoodInvAsrt_Astruct'.
Qed.

Lemma GoodInvAsrt_dllsegflag :
  forall vl head tailnext next,
    GoodInvAsrt (dllsegflag head tailnext vl next).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; split; auto.
Qed.

Lemma GoodInvAsrt_tcbdllflag :
  forall vl head,
    GoodInvAsrt (tcbdllflag head vl).
Proof.
  intros.
  unfold tcbdllflag.
  apply GoodInvAsrt_dllsegflag.
Qed.

Lemma GoodInvAsrt_sllseg :
  forall l head tailnext t next,
    GoodInvAsrt (sllseg head tailnext l t next).
Proof.
  inductions l.
  simpl; auto.
  simpl; split; auto.
  intro.
  splits; auto.
  intro.
  split; auto.
  apply GoodInvAsrt_Astruct.
Qed.

Lemma GoodInvAsrt_sll :
  forall head l t next,
    GoodInvAsrt (sll head l t next).
Proof.
  intros.
  unfold sll.
  apply GoodInvAsrt_sllseg.
Qed.

Lemma GoodInvAsrt_sllsegfreeflag :
  forall vl head tailnext next,
    GoodInvAsrt (sllsegfreeflag head tailnext vl next).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; intros.
  splits; auto.
Qed.

Lemma GoodInvAsrt_sllfreeflag :
  forall head l,
    GoodInvAsrt (sllfreeflag head l).
Proof.
  intros.
  unfold sllfreeflag.
  apply GoodInvAsrt_sllsegfreeflag.
Qed.

(*---end of auxiliary lemmas----*)

Lemma invprop : inv_prop OSInv.
Proof.
  unfolds.
  split.
  apply OSInv_precise. 
  unfolds.
  
  split; intros.
  destruct_s s; simpl set_isr_s.

  eapply OSInv_isr_is_irrel; eauto.
  unfold OSInv in H. simpljoin1.
  sep destruct H.
  (* do 22 destruct H. *)
  sep_rmb_trms_in H A_isr_is_prop; simpl in H; simpljoin1. 

  clear - H15. 
  
  unfold isr_is_prop in *; intros.
  apply H15 in H.
  unfold isrupd.
  destruct(beq_nat i x); auto.

  split; intros.
  destruct_s s; simpl set_isisr_s.
  eapply OSInv_isr_is_irrel; eauto.

  get_isr_is_prop H; 
    match goal with H: isr_is_prop _ _ |- _ => clear - H end.
  
  unfold isr_is_prop in *; intros.
  unfold isrupd.
  destruct(beq_nat i x) eqn : eq1.
  false; apply H.
  simpl; left.
  apply beq_nat_true in eq1; auto.
  apply H15.
  intro; apply H.
  simpl; right; auto.
  
  split; intros.
  destruct_s s; simpl set_is_s.
  simpl get_isr_s in H0; simpl get_is_s in H1.
  eapply OSInv_isr_is_irrel; eauto.
  get_isr_is_prop H; clear - H16 H0.
  unfold isr_is_prop in *; intros.
  destruct(beq_nat i x) eqn : eq1.
  apply beq_nat_true in eq1; substs; auto.
  apply H16.
  intro; apply H.
  simpl in H1; destruct H1; substs.
  rewrite <- beq_nat_refl in eq1; tryfalse.
  auto.

  destruct_s s; simpl set_is_s.
  simpl get_isr_s in H0; substs.
  eapply OSInv_isr_is_irrel; eauto.
  unfolds; intros.
  unfold empisr; auto.
Qed.

Lemma GoodInvAsrt_ecbf_sllseg:
  forall vl hd tn t, 
    GoodInvAsrt (ecbf_sllseg hd tn vl t V_OSEventListPtr).
Proof.
  inductions vl.
  intros. simpl. auto.

  intros.
  unfold ecbf_sllseg. fold ecbf_sllseg.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  splits; auto.
  simpl. intros. split; auto.
  apply GoodInvAsrt_Astruct.
  apply GoodInvAsrt_Aarray.
Qed.

Lemma GoodInvAsrt_evsllseg: 
  forall vl hd tn ecbls, GoodInvAsrt (evsllseg hd tn vl ecbls). 
Proof.
  inductions vl.
  intros.
  simpl. auto.
  intros. simpl evsllseg.
  destruct ecbls.
  simpl. auto.
  destruct a.

  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros.
  split; auto.
  split.
  apply GoodInvAsrt_AEventNode.
  apply IHvl.
Qed. 

Lemma GoodInvAsrt_Aarray_new': 
  forall vll l m t, GoodInvAsrt (Aarray_new' l m t vll).
Proof.
  inductions vll.
  intros.
  destruct m.
  simpl. auto.
  simpl. auto.
  intros.
  destruct m.
  simpl. auto.
  simpl.
  destruct t eqn: et;
    try
      (destruct a; simpl; auto;
       destruct a; [destruct l; simpl; split; auto | simpl; auto]).
  destruct l.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split. apply GoodInvAsrt_Aarray.
  apply IHvll.
  destruct l.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split. apply GoodInvAsrt_Astruct.
  apply IHvll.
Qed.

Lemma GoodInvAsrt_llsegobjaux:
  forall l head locvl ptrvl, 
    GoodInvAsrt (llsegobjaux head Vnull l locvl ptrvl V_OSTCBNext). 
Proof.
  inductions l.
  intros.
  simpl.
  destruct locvl; destruct ptrvl; tryfalse; simpl; auto.
  intros.
  simpl.
  destruct locvl; destruct ptrvl; tryfalse; simpl; auto. 
  intros.
  splits; auto. 
Qed.

Lemma goodinv:  GoodInvAsrt OSInv.
Proof.
  unfold OSInv.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  split.
  unfold GoodInvAsrt.
  unfold AOSEventFreeList. fold GoodInvAsrt.
  intros.
  split.
  simpl. auto.
  unfold ecbf_sll.
  apply GoodInvAsrt_ecbf_sllseg.
  split.
  unfold AECBList.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros. split; auto.
  split. simpl. auto.
  apply GoodInvAsrt_evsllseg.
  split.
  unfold AOSMapTbl.
  unfold GAarray.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto.
  apply GoodInvAsrt_Aarray.
  split.
  unfold AOSUnMapTbl.
  unfold GAarray.
  unfold GoodInvAsrt; fold GoodInvAsrt.  
  intros. split. simpl. auto.
  apply GoodInvAsrt_Aarray.
  split.
  unfold AOSTCBPrioTbl.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split.
  unfold GAarray. unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto. apply GoodInvAsrt_Aarray.
  splits; auto.  split. simpl. auto. intros. simpl. auto.
  split.
  unfold AOSIntNesting.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. simpl. auto.
  split.
  unfold AOSTCBList'.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  splits.
  intros.  splits; auto.
  simpl. auto.
  unfold tcbdllseg. apply GoodInvAsrt_dllseg.
  simpl. auto.
  unfold tcbdllseg. apply GoodInvAsrt_dllseg.
  splits; auto.
  apply GoodInvAsrt_tcbdllflag.
  intros.
  splits; auto.
  simpl. auto. simpl. auto.
  unfold tcblist.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split; auto.
  unfold tcbdllseg. apply GoodInvAsrt_dllseg.
  unfold TCB_Not_In.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  auto.
  apply GoodInvAsrt_tcbdllflag.
  split.
  unfold AOSTCBFreeList'.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split. simpl. auto. split. simpl. split; auto.
  split. apply GoodInvAsrt_sll. apply GoodInvAsrt_sllfreeflag.
  unfold TCBFree_Eq.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros.
  splits; auto.
  apply GoodInvAsrt_Astruct.
  simpl. auto.
  intros. splits; simpl; auto.
  apply GoodInvAsrt_sll.
  apply GoodInvAsrt_sllfreeflag.
  split.
  unfold AOSRdyTblGrp.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  splits; auto.
  unfold AOSRdyTbl.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split; auto.
  unfold GAarray. unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto.
  apply GoodInvAsrt_Aarray.
  unfold AOSRdyGrp. simpl. splits; auto.
  split.
  simpl. auto.
  splits; auto.
  simpl. splits; auto.

  unfold AOBJ.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. splits; auto.
  unfold AObjs.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  splits; auto.
  unfold AObjArr. 
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto. split; auto.
  unfold Aarray_new.
  apply GoodInvAsrt_Aarray_new'.

  unfold tcbllsegobjaux. 
  unfold GoodInvAsrt. fold GoodInvAsrt.  
  apply GoodInvAsrt_llsegobjaux.

  simpl. auto.
Qed.  


Lemma goodinv_aemp :
  GoodInvAsrt aemp_isr_is.
Proof.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  unfold GoodInvAsrt; auto.
Qed.

Lemma invprop_aemp :
  inv_prop aemp_isr_is.
Proof.
  unfolds; split.
  unfolds; destruct_s s; intros.
  simpl in H, H0; simpljoin1; intros; auto.

  unfolds; split; intros.
  destruct_s s.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; split; auto.

  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
  
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
  
  unfold isr_is_prop in *; intros.
  apply H14 in H.
  unfolds.
  destruct(beq_nat i x); auto.
  unfolds; auto.
  
  split; intros.
  destruct_s s.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
  
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
    
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.

  unfold isr_is_prop in *; intros.
  unfold isrupd.
  destruct( beq_nat i x ) eqn :eq1.
  false; apply H; simpl; left.
  apply beq_nat_true in eq1; auto.
  apply H14; intro; apply H.
  simpl; right; auto. 
  unfolds; auto.

  split; intros.
  destruct_s s; simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.

  
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
 
  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; eauto.
  split.
  apply map_join_emp.
  split.
  splits; eauto.
  unfolds; auto.
  splits; eauto.
  
  unfold isr_is_prop in *; unfold get_isr_s in H0; unfold get_is_s in H1; intros.
  destruct( beq_nat i x ) eqn :eq1.
  apply beq_nat_true in eq1; substs; auto.
  apply H16; intro; apply H; substs.
  simpl in H2; destruct H2; substs.
  rewrite <- beq_nat_refl in eq1; tryfalse.
  auto.
  unfolds; auto.

  destruct_s s; simpl in H; simpl; simpljoin1.
  simpl in H0; substs.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; split; auto.

  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; eauto.
  split.
  apply map_join_emp.
  split.
  splits; eauto.
  unfolds; auto.
  splits; eauto.
  unfolds.
  intros.
  unfolds; auto.
  unfolds; auto.
Qed. 


Lemma atoy_inv'_precise' :
  forall e e0 M1 M2 i i0 i1 c o1 o2 a,
    (e, e0, M1, i, (i0, i1, c), o1, a) |= atoy_inv' ->
    (e, e0, M2, i, (i0, i1, c), o2, a) |= atoy_inv' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o0 : osabst,
       sub o1 o0 -> sub o2 o0 -> o1 = o2).
Proof.
  intros.
  unfold atoy_inv' in *.
  simpl in H, H0; simpljoin1; split; auto; intros.
  rewrite H13 in H4; inverts H4.
  eapply mapstoval_true_mem_eq; eauto.
Qed.

Lemma atoy_inv'_precise :
  forall e e0 M1 M2 i i0 i1 c o1 o2 a,
    (e, e0, M1, i, (i0, i1, c), o1, a) |= atoy_inv' ->
    (e, e0, M2, i, (i0, i1, c), o2, a) |= atoy_inv' ->
    (forall (M : mem) (o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).      
Proof.
  intros e e0 M1 M2 i i0 i1 c o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply atoy_inv'_precise';eauto.
Qed.


Lemma OSInv_prop :
  forall o O O' aop,
    (o, O, aop) |= OSInv -> disjoint O O' -> O' = empabst.
Proof.
  intros.
  unfold OSInv in H.
  sep normal in H; sep destruct H.
  
  eapply join_lib.extensionality; intros.
  rewrite emp_sem.
  destruct a.
  
  sep_rmb_trms_in H (Aabsdata abstcblsid). 
  simpl in H; simpljoin1.
  eapply osabst_disjoint_join_sig_get_none; eauto.

  sep_rmb_trms_in H (Aabsdata absecblsid).
  simpl in H; simpljoin1.
  eapply osabst_disjoint_join_sig_get_none; eauto.
  
  sep_rmb_trms_in H (Aabsdata ostmid).
  simpl in H; simpljoin1.
  eapply osabst_disjoint_join_sig_get_none; eauto.
  
  sep_rmb_trms_in H (Aabsdata curtid).
  simpl in H; simpljoin1.
  eapply osabst_disjoint_join_sig_get_none; eauto.

  (* (* get O' absptlsid = None *)  *)
  (* unfold AOSTCBPrioTbl in H. *)
  (* sep_rmb_trms_in H (Aabsdata absptlsid). *)
  (* simpl in H; simpljoin1. *)
  (* eapply osabst_disjoint_join_sig_get_none; eauto. *)

  (* get O' absobjsid = None *) 
  unfold AOBJ in H.
  sep normal in H. sep destruct H.
  sep_lift_context_in H (absobjsid).
  sep remember (1:: nil)%nat in H.
  simpl in H; simpljoin1.
  eapply osabst_disjoint_join_sig_get_none; eauto.
Qed.

  
Lemma goodinv_atoy :
  GoodInvAsrt atoy_inv.
Proof.
  unfold atoy_inv.
  unfold atoy_inv'.
  unfold A_isr_is_prop.
  unfold GoodInvAsrt; simpl;auto.
Qed.


Lemma invprop_atoyinv :
  inv_prop atoy_inv.
Proof.
  unfolds; split.
  
  {
    unfolds; intros; destruct_s s; unfold substmo in *; unfold substaskst in *.
    unfold atoy_inv in *.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.

    lets Hx1: atoy_inv'_precise _H _H0.
    lets Hx2: A_isr_is_prop_precise H H0.
    assert (x = x3 /\ x1 = x5).
    { apply (Hx1 M o);mem_join_sub_solver. } destruct H9;subst.
    assert (x0 = x4 /\ x2 = x6).
    { apply (Hx2 M o);mem_join_sub_solver. } destruct H9;subst.
    split;jeat.
  }
  
  unfolds.
  split; intros. 
  unfold atoy_inv in *.
  destruct_s s.
  unfold set_isr_s; unfold get_isr_s.
  solve_sat_auto.
  unfold A_isr_is_prop in *.
  simpl in H5; simpljoin1.
  simpl.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  clear - H12.
  unfold isr_is_prop in *; intros.
  apply H12 in H.
  unfold isrupd.
  destruct(beq_nat i x); auto.
  unfolds; auto.
  
  split; intros.
  destruct_s s.
  unfold set_isisr_s; unfold get_is_s; unfold get_isr_s.
  unfold atoy_inv in *.
  solve_sat_auto.
  simpl in H5; simpljoin1.
  simpl.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  clear - H12.
  unfold isr_is_prop in *; intros.
  unfold isrupd.
  destruct(beq_nat i x) eqn : eq1.
  false; apply H.
  simpl; left.
  apply beq_nat_true in eq1; auto.
  apply H12.
  intro; apply H.
  simpl; right; auto.
  unfolds; auto.
  
  split; intros.
  destruct_s s.
  unfold set_isr_s, get_is_s, get_isr_s in *.
  unfold atoy_inv in *.
  solve_sat_auto.
  unfold set_is_s.
  simpl in H7; simpljoin1.
  simpl.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; auto.
  split.
  apply map_join_emp.
  repeat (split; eauto).

  unfold isr_is_prop in *; intros.
  destruct( beq_nat i x ) eqn :eq1.
  apply beq_nat_true in eq1; substs; auto.
  apply H13; intro; apply H; substs.
  simpl in H1; destruct H1; substs.
  rewrite <- beq_nat_refl in eq1; tryfalse.
  auto.

  destruct_s s.
  unfold get_isr_s in *; substs.
  unfold atoy_inv in *.
  solve_sat_auto.
  unfold set_is_s.
  simpl in H5; simpljoin1.
  simpl.
  
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst.
  splits; eauto.

  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; auto.
  split.
  apply map_join_emp.
  repeat (split; eauto).
Qed.


Definition I (n:hid) :=
  match n with 
  | 0%nat => mkinvasrt goodinv invprop
  | 1%nat => mkinvasrt goodinv_atoy invprop_atoyinv
  | _ => mkinvasrt goodinv_aemp invprop_aemp
  end.

Lemma disj_star_elim_disj_dup:
  forall p q r, ( p \\// q )** r ==> (p ** r) \\// (q ** r).
Proof.
  intros.
  simpl in *;simpljoin.
  destruct H3;simpljoin.
  left.
  do 6 eexists;splits;eauto.
  right.
  do 6 eexists;splits;eauto.
Qed.


Lemma osq_inv_in:
  forall n e e0 m x i1 c O ab, 
    (forall i : hid, x i = false)->
    (e, e0, m, x, (false, i1, c), O, ab)
      |= invlth_isr I 0%nat n ->
    (e, e0, m, x, (false, i1, c), O, ab)
      |= EX p1 p2 tcbl1 tcbcur tcbl2 ct tcbls rtbl pf,
                (AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf) ** HCurTCB ct** Atrue.
Proof.
  inductions n.
  introv Hfor Hsat.
  unfold invlth_isr in Hsat.
  replace (0-0)%nat with (0%nat) in Hsat by omega.
  unfold starinv_isr in Hsat.
  sep destruct Hsat.
  destruct Hsat.
  simpl in H.
  simpljoin1.
  tryfalse.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H0 in H.
  remember (([|x0 0%nat = false|] //\\ Aisr x0) ) as P.
  clear HeqP.
  unfold OSInv in H.
  sep normal in H.
  sep destruct H. 
  sep_rmb_trms_in H AOSTCBList'.
  (* sep remember (10::nil)%nat in H. *)
  exists x5 x6 x7 x8 x9 x15.
  sep auto.
  
  introv Hfor Hsat.
  unfold invlth_isr in Hsat.
  replace (S n-0)%nat with (S n%nat) in Hsat by omega.
  unfold starinv_isr in Hsat.
  fold starinv_isr in Hsat.
  remember ( starinv_isr I 1%nat n) as P.
  clear HeqP.
  sep normal in Hsat.
  destruct Hsat.  
  
  apply disj_star_elim_disj_dup in H.
  destruct H.
  simpl in H.
  simpljoin1.
  tryfalse.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H0 in H.
  remember (([|x0 0%nat = false|] //\\ Aisr x0) ) as d.
  clear Heqd.
  unfold OSInv in H.
  sep auto.
Qed.


Lemma join_join_disj_copy :
  forall m1 m2 m3 m4 m5,
    TcbMod.join m1 m2 m3 -> TcbMod.join m4 m5 m2 -> TcbMod.disj m1 m4.
Proof.
  intros.
  intro.
  pose proof H a.
  pose proof H0 a.
  
  destruct (TcbMod.get m1 a);
    destruct (TcbMod.get m2 a);
    destruct (TcbMod.get m3 a);
    destruct (TcbMod.get m4 a);
    destruct (TcbMod.get m5 a);
    tryfalse; auto.
Qed.

Lemma TCBList_P_combine_copy :
  forall l1 l2 v1 v2 rtbl tcbls1 tcbls2 tcbls,
    TcbMod.join tcbls1 tcbls2 tcbls ->
    TCBList_P v1 l1 rtbl tcbls1 ->
    TCBList_P v2 l2 rtbl tcbls2 ->
    l1 <> nil ->
    V_OSTCBNext (last l1 nil) = Some v2 ->
    TCBList_P v1 (l1++l2) rtbl tcbls.
Proof.
  intros.
  destruct l1; tryfalse.
  
  clear H2.
  gen v.
  inductions l1; intros.
  simpl in H3.
  simpl.
  simpl in H0; simpljoin1.
  do 4 eexists; repeat split; eauto.

  clear - H H4.
  unfold TcbJoin in *.
  intro.
  pose proof H a; clear H.
  pose proof H4 a; clear H4.
  rewrite TcbMod.emp_sem in H.
  unfold sig in *; simpl in *.
  destruct (TcbMod.get tcbls1 a);
    destruct (TcbMod.get tcbls2 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get (TcbMod.sig x x2) a);
    tryfalse; substs; auto.
  
  rewrite <- app_comm_cons.
  unfold TCBList_P; fold TCBList_P.
  remember (a::l1) as lx.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  substs.
  simpljoin1. 
  do 4 eexists; repeat split; eauto.
  instantiate (1:=TcbMod.merge x1 tcbls2).
  clear - H H4.
  unfold TcbJoin in *.
  intro.
  pose proof H a; clear H.
  pose proof H4 a; clear H4.
  unfold sig in *; simpl in *.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get tcbls1 a);
    destruct (TcbMod.get tcbls2 a);
    destruct (TcbMod.get (TcbMod.sig x x2) a);
    tryfalse; substs; auto.

  eapply IHl1; eauto.

  clear - H H4.
  apply TcbMod.join_merge_disj.
  unfold TcbJoin in H4.
  apply TcbMod.join_comm in H.
  apply TcbMod.join_comm in H4.
  apply TcbMod.disj_sym.
  eapply join_join_disj_copy; eauto.
Qed.

Lemma tcb_list_split_by_tcbls :
  forall l tls tid htcb s head hprev tail tnext rtbl P,
    get tls tid = Some htcb ->
    TCBList_P head l rtbl tls ->
    s |= tcbdllseg head hprev tail tnext l ** P ->
    (exists l1 tcbnode l2 tls1 tls2 tail1,
        s |= tcbdllseg head hprev tail1 (Vptr tid) l1 **
          tcbdllseg (Vptr tid) tail1 tail tnext (tcbnode :: l2) ** P /\
          TCBList_P head l1 rtbl tls1 /\
          TCBList_P (Vptr tid) (tcbnode :: l2) rtbl tls2 /\
          join tls1 tls2 tls /\ l = l1 ++ tcbnode :: l2).
Proof.
  inductions l; intros.
  simpl in H0; substs.
  rewrite TcbMod.emp_sem in H; tryfalse.

  simpl in H0; simpljoin1.
  destruct (tidspec.beq tid x) eqn : eq1.
  pose proof tidspec.beq_true_eq tid x eq1; substs.
  exists (nil(A:=vallist)) a l TcbMod.emp tls hprev.
  simpljoin1; splits.
  sep auto.
  destruct_s s.
  simpl in H1; simpljoin1.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst; auto.
  unfolds; auto.

  unfold tcbdllseg in H1.
  unfold dllseg in H1; fold dllseg in H1.
  destruct_s s.
  sep split in H1.
  simpl_sat H1; simpljoin1.
  simpl; auto.
  simpl.
  do 4 eexists; repeat (split; eauto).
  apply TcbMod.join_emp; auto.
  rewrite app_nil_l; auto.
  
  unfold tcbdllseg in H1.
  unfold dllseg in H1; fold dllseg in H1.
  destruct_s s.
  sep split in H1.
  simpl_sat H1; simpljoin1.  
  assert((e, e0, (merge x23 x4), i, (i0, i1, c), (merge x26 x7), a0)
           |= dllseg x9 (Vptr x) tail tnext l OS_TCB_flag V_OSTCBPrev
           V_OSTCBNext ** P).
  simpl_sat_goal.
  exists x23 x4; eexists.
  exists x26 x7; eexists.
  splits; eauto.
  eapply join_merge_disj.
  eapply mem_join_join_disjoint; eauto.
  apply join_comm; eauto.
  eapply join_merge_disj.
  eapply osabst_join_join_disjoint; eauto.
  apply join_comm; eauto.

  assert(get x1 tid = Some htcb).
  clear - H H3 eq1.
  unfolds in H3.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H0.
  unfold get in H; simpl in H.
  rewrite H in H0.
  unfold get; simpl.
  destruct(TcbMod.get x1 tid); tryfalse.
  substs; auto.
  apply tidspec.beq_false_neq in eq1.
  auto.

  rewrite H2 in H14; inverts H14.
  unfold tcbdllseg at 1 in IHl.
  lets Hx: IHl H7 H5 H1.
  simpljoin1.
  
  exists (a::x0) x5 x8 (TcbMod.merge (TcbMod.sig x x2) x10) x11 x12.
  simpljoin1; splits; auto.
  simpl_sat H9; simpljoin1.
  simpl_sat_goal.
  
  exists (merge x22 x13) x14 m (merge x25 x16) x17 o.
  splits; eauto.
  clear - H14 H6 H21.

  eapply mem_join_join_join_merge_join_merge; eauto.
  
  clear - H16 H8 H23.
  eapply osabst_join_join_join_merge_join_merge; eauto.
  
  unfold tcbdllseg; unfold dllseg; fold dllseg.
  sep split; auto.
  exists x9.
  sep split; auto.
  simpl_sat_goal.
  exists x22 x13; eexists.
  exists x25 x16; eexists.
  splits; eauto.
  clear - H6 H21 H14.
  eapply join_merge_disj.
  
  eapply mem_join_join_join_merge_disjoint.
  eapply H6.
  eauto.
  eauto.

  clear - H8 H23 H16.
  eapply join_merge_disj.
  eapply osabst_join_join_join_merge_disjoint.
  eapply H8.
  eauto.
  eauto.

  exists x19 x20 x14 x24 x27 x17.
  splits; eauto.
  
  simpl; do 4 eexists; splits; eauto.
  clear - H3 H13.
  unfold TcbJoin in *.
  unfolds; intros.
  pose proof H3 a; pose proof H13 a.
  unfold sig in *; simpl in *.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get (TcbMod.sig x x2) a);
    destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tls a);
    destruct (TcbMod.get x10 a);
    destruct (TcbMod.get x11 a); tryfalse; auto.
 
  clear - H3 H13.
  unfold TcbJoin in *.
  unfolds; intros.
  simpl.
  unfolds; intros.
  pose proof H3 a; pose proof H13 a.
  unfold sig in *; simpl in *.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get (TcbMod.sig x x2) a);
    destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tls a);
    destruct (TcbMod.get x10 a);
    destruct (TcbMod.get x11 a); tryfalse; substs; auto.
Qed.

Lemma starinv_isr_osabst_emp :
  forall n i e e0 M isr st O ab,
    (i > 0)%nat ->
    (forall i0, isr i0 = false) ->
    (e, e0, M, isr, st, O, ab) |= starinv_isr I i n ->
    O = OSAbstMod.emp.
Proof.
  inductions n; intros.
  simpl in H1; simpljoin1.
  destruct H1; simpljoin1.
  destruct i.
  omega.
  destruct i.
  simpl in H6; simpljoin1.
  simpl in H6; simpljoin1.
  simpl in H1; simpljoin1.
  destruct H5; simpljoin1.
  pose proof H0 i; rewrite H1 in H2; false.
  lets Hx: IHn H6; eauto.
  destruct i.
  omega.
  destruct i.
  simpl in H9; simpljoin1.
  simpl in H9; simpljoin1.
Qed.


Lemma tcbdllseg_last_nextptr :
  forall l s head hprev tail tid h P,
    s |= tcbdllseg head hprev tail (Vptr tid) (h::l) ** P ->
    V_OSTCBNext (last (h :: l) nil) = Some (Vptr tid).
Proof.
  inductions l; intros.
  destruct_s s.
  unfold tcbdllseg in H; unfold dllseg in H.
  simpl_sat H; simpljoin1.
  simpl; auto.

  remember (a::l) as xxx.
  unfold tcbdllseg in *.
  unfold dllseg in H; fold dllseg in H.
  sep pure.
  destruct_s s.
  sep remember (1::nil)%nat in H.
  simpl_sat H; simpljoin1.
  lets Hx: IHl H8.
  simpl last in *; auto.
Qed.


Lemma atoy_inv_osabst_emp :
  forall e e0 M isr st o ab,
    (e, e0, M, isr, st, o, ab) |= atoy_inv ->
    o = OSAbstMod.emp.
Proof.
  intros.
  simpl in H; simpljoin1.
Qed.


Lemma GoodSched_GetHPrio : GoodSched GetHPrio.
Proof.
  unfolds.
  splits; intros.
  unfold GetHPrio in *; simpljoin1.
  do 3 eexists.
  splits; eauto.
  eapply join_get_l; eauto.

  unfold GetHPrio in *; simpljoin1.
  do 2 eexists; splits; eauto.  
  
  unfold GetHPrio in *; simpljoin1.
  assert (get O abtcblsid = Some (abstcblist x2)).
  { eapply join_get_l; eauto. }
  rewrite H1 in H8; inverts H8.
  do 3 eexists; splits; eauto.
Qed.

Lemma aemp_isr_elim_dup:
  forall o O ab P,
    (o, O , ab) |= aemp_isr_is ** P -> (o, O, ab) |= P.
Proof.
  introv Hsat.
  simpl in Hsat.
  simpljoin.
  destruct o as [[[[]]]].
  simpl in *.
  destruct l.
  destruct p.
  assert (m=x0) by join auto.
  assert (O=x3) by join auto.
  subst.
  auto.
Qed.

Lemma atoy_abst_elim_dup :
  forall o O ab P,
    (o,O,ab) |= atoy_inv ** P ->
    exists o', (o',O,ab) |= P.
Proof.
  introv Hsat.
  unfold atoy_inv in Hsat.
  simpl in Hsat.
  simpljoin.
  destruct o as [[[[]]]].
  simpl in *.
  simpljoin.
  destruct l.
  destruct p.
  eexists .
  assert (O = x3) by join auto.
  subst.
  eauto.
Qed.

Require Import invariant_prop. 

Lemma mapstoval_false_join_load_vptr :
  forall l x a m1 m2 m,
    mapstoval l (Tptr x) false (Vptr a) m1 ->
    join m1 m2 m ->
    load (Tptr x) m l = Some (Vptr a).
Proof.
  intros.
  unfold mapstoval in H; simpljoin1.
  unfold load.
  unfold loadm.
  destruct l.
  lets Hx: symbolic_lemmas.ptomvallist_loadbytes H1.
  lets Hx1: lmachLib.loadbytes_mono H0 Hx.
  rewrite Hx in Hx1.
  rewrite encode_val_length in Hx1.
  rewrite Hx1.
  rewrite symbolic_lemmas.type_val_mach_encode_val_decode_val; auto.
Qed.


Definition AOSTCBList'' :=
  fun (p1 p2 : val) (l1 l2 : list vallist) (rtbl : vallist)
      (hcurt : addrval) (tcbls : TcbMod.map) (pf : val) =>
    ((EX (tail1 tail2 : val) (tcbls1 tcbls2 : TcbMod.map),
      GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
         tcbdllseg p1 Vnull tail1 p2 l1 **
         tcbdllseg p2 tail1 tail2 Vnull l2 **
         [|p1 <> Vnull /\ p2 = Vptr hcurt|] **
         [|join tcbls1 tcbls2 tcbls|] **
         [|TCBList_P p1 l1 rtbl tcbls1|] **
         [|TCBList_P p2 l2 rtbl tcbls2|] **
         tcbdllflag p1 (l1 ++ l2) ** [|p2 <> pf|])
       \\//
       ( EX (tail : val),
         GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
            tcblist p1 Vnull tail Vnull (l1 ++ l2) rtbl tcbls **
            TCB_Not_In p2 p1 (l1 ++ l2) **
            tcbdllflag p1 (l1 ++ l2) **
            [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** [|p2 = pf|])).

Lemma AOSTCBList'_AOSTCBList'' :
  forall a b c d e f g h P,
    AOSTCBList' a b c d e f g h **P <==>   GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-r-> b ** AOSTCBList'' a b c d e f g h **P.
Proof.
  intros.
  unfold AOSTCBList'; unfold AOSTCBList''.
  split; intros; sep cancel P. 
  destruct H.
  sep destruct H.
  sep cancel 3%nat 1%nat.
  left.
  sep auto; eauto.
  sep destruct H.
  sep cancel 2%nat 1%nat.
  right.
  sep auto; eauto.

  sep lift 2%nat in H.
  apply disj_split in H.
  destruct H.
  left.
  sep auto; eauto.
  right.
  sep auto; eauto.
Qed.

Definition osinv'' :=
  EX (eventl : list vallist) (msgql : list EventData)
     (ectrl : list os_inv.EventCtr) (ptbl : vallist) (p1 p2 : val)
     (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
     (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
     (tcbls : TcbMod.map) (t : int32) (ct vhold : addrval) 
     (ptfree : val) (lfree : list vallist) fecbh (* ptls *),  (*增加了sifls和rvst*) 
    GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-r-> p2 **
    AOSTCBList'' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ptfree **
    AOSEventFreeList fecbh eventl **
    AECBList ectrl msgql ecbls tcbls **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl ptbl rtbl tcbls (* ptls  *)vhold **
    AOSIntNesting **
    AOSTCBFreeList' ptfree lfree ct tcbls  **
    AOSRdyTblGrp rtbl rgrp **
    AOSTime (Vint32 t) **
    HECBList ecbls **
    HTCBList tcbls **
    HTime t **
    HCurTCB ct **
    AGVars **
    (EX objl absobjs, AOBJ objl absobjs ecbls vhold p1 (tcbl1 ++ (tcbcur::tcbl2)) fecbh eventl) ** 
    [|RH_TCBList_ECBList_P ecbls tcbls ct|] ** A_isr_is_prop. 

Lemma osinv''_OSInv: forall P,
    osinv'' ** P <==> OSInv ** P.
Proof.
  unfold osinv'', OSInv.
  split.
  intros.
  sep cancel P.
  sep destruct H.
  rewrite <- AOSTCBList'_AOSTCBList'' in H.
  sep auto.
  intros.

  sep cancel P.
  sep destruct H.
  sep eexists.
  rewrite <- AOSTCBList'_AOSTCBList'' .
  sep auto.
Qed.

Lemma tcblist_indom_ptr_in_tcblist :
  forall vltcb head rtbl tcbls ct,
    TCBList_P head vltcb rtbl tcbls ->
    indom tcbls ct ->
    ptr_in_tcblist (Vptr ct) head vltcb.
Proof.
  inductions vltcb; intros.
  simpl in H; substs.
  unfolds in H0; destruct H0.
  rewrite emp_sem in H; tryfalse.

  unfold1 TCBList_P in H; simpljoin1.
  unfold ptr_in_tcblist.
  unfold1 ptr_in_tcbdllseg.
  destruct (beq_val (Vptr ct) (Vptr x)) eqn : eq1; auto.
  rewrite H1.
  eapply IHvltcb; eauto.
  clear - H2 H0 eq1.
  unfold indom in *; simpljoin1.
  exists x0.
  unfolds in H2.
  assert (ct <> x).
  intro; substs.
  unfold beq_val in eq1.
  unfolds in eq1.
  destruct x.
  rewrite beq_pos_Pos_eqb_eq in eq1.
  rewrite Int.eq_true in eq1.
  assert (b = b) by auto.
  apply Pos.eqb_eq in H0.
  rewrite H0 in eq1.
  simpl in eq1; tryfalse.
  clear eq1.
  hy.
Qed.

Lemma tcbdllseg_sll_neq :
  forall ct lfree pf s tid x x7 x8 x11 H,
    s |= tcbdllseg (Vptr tid) x11 x ct (x7 :: x8) ** assertion.sll pf lfree OS_TCB_flag V_OSTCBNext ** H -> 
    pf <> Vptr tid.
Proof.
  intros.
  intro; substs.
  unfold assertion.sll in H0.
  destruct lfree.
  unfold sllseg in H0; fold sllseg in H0; sep split in H0; tryfalse.
  unfold sllseg in H0; fold sllseg in H0.
  unfold tcbdllseg in H0.
  unfold dllseg in H0; fold dllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0; simpljoin1.
  inverts H1; inverts H3.
  sep lifts (1::3::nil)%nat in H0.
  eapply os_inv.node_OS_TCB_dup_false; eauto.
Qed.

Ltac get_hsat Hs := 
  match goal with
    H: _ |= _ |- _ => rename H into Hs
  end.

Lemma AOSTCBList'_AOSTCBFreeList_set_curtid_not_indom : 
  forall (p1 p2 : val) (l1 : list vallist) (curtcb : vallist)
         (l2 : list vallist) (rtbl : vallist) (ct : addrval)
         (tcbls : TcbMod.map) (lfree : list vallist) 
         (pf : val) (P : asrt) (tid : Modules.tid)
         objl absobjs ecbls vhold fecbh fecbvl 
         e e0 isr st ab M O Mx Ox MM OO,
    RH_CurTCB tid tcbls ->
    ~indom tcbls ct ->
    (e, e0, M, isr, st, O, ab)
      |= AOSTCBList'' p1 p2 l1 (curtcb :: l2) rtbl ct tcbls pf **
           AOSTCBFreeList' pf lfree ct tcbls ** 
           AOBJ objl absobjs ecbls vhold p1 (l1++(curtcb::l2)) fecbh fecbvl ** P -> 
    join M Mx MM ->
    join O Ox OO ->
    (e, e0, Mx, isr, st, Ox, ab) |= EX lg : list logicvar, OSLInv ct lg -> 
    exists l1' curtcb' l2' pf' lfree',
      (e, e0, MM, isr, st, OO, ab)
        |= AOSTCBList'' p1 (Vptr tid) l1' (curtcb' :: l2') rtbl tid tcbls pf' **
             AOSTCBFreeList' pf' lfree' tid tcbls **
             AOBJ objl absobjs ecbls vhold p1 (l1'++(curtcb'::l2')) fecbh fecbvl ** P. 
Proof.
  intros.
  rename H0 into H_indom.
  rename H1 into H0.
  unfold AOSTCBList'' in H0.
  unfold AOSTCBFreeList' in H0.
  
  (*4 cases*)
  apply disj_split in H0.
  destruct H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.

  (*1 false*)
  simpljoin1.
  unfold1 TCBList_P in H7.
  simpljoin1.
  inverts H7.
  clear - H5 H10 H_indom.
  false.
  apply H_indom.
  unfold indom.
  exists x6.
  unfolds in H10.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.
  apply get_sig_some.

  (*2 false*)
  unfold TCBFree_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.
  
  (*3 false*)
  unfold TCBFree_Not_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  (*4*)
  simpljoin1.
  unfold TCBFree_Eq in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0; simpljoin1.
  unfolds in H; simpljoin1.
  sep_lift_context_in H0 tcblist.
  (* sep lift 6%nat in H0. *)
  unfold tcblist in H0.
  sep split in H0.
  lets Hx: tcb_list_split_by_tcbls H H5 H0.
  simpljoin1.
  match goal with
    H: _ |= tcbdllseg _ _ _ _ ?x1 ** tcbdllseg _ _ _ _ (?x2 :: ?x3) ** _ |- _ =>
      exists x1 x2 x3
  end.
  get_hsat Hsat.
  match type of Hsat with
    context [Astruct _ _ ?x1] =>
      match type of Hsat with
        context [sllfreeflag _ ?x0] => exists (Vptr ct) (x1 :: x0) 
      end
  end.
  unfold AOSTCBList''.
  apply disj_split.
  left.
  sep_lifts_trms AOSTCBFreeList'.
  unfold AOSTCBFreeList'.
  sep normal.
  match type of Hsat with
    _ |= tcbdllseg _ _ _ _ _ ** tcbdllseg _ ?x1 ?x2 _ _ ** _ => 
      exists x1 x2
  end.
  match goal with
    H: join ?xa ?xb tcbls |- _ => exists xa xb
  end.
  (* exists x14 x x12 x13. *)
  sep_lift_context Adisj.
  apply disj_split.
  left.
  sep split; auto.
  unfold TCB_Not_In in Hsat.
  sep split in Hsat.
  sep_rmb_trms_in Hsat (Astruct, flag_off, loc_off, ptr_off, sll, sllfreeflag).
  sep_rmb_trms_in Hsat H16.
  (* sep remember (7::nil)%nat in Hsat.  *)
  sep_lifts_trms_in  Hsat H17.
  simpl in Hsat; simpljoin1.
  sep_rmb_trms TCBFree_Not_Eq.
  (* sep remember (1::nil)%nat. *)
  simpl_sat_goal.
  exists (merge x14 Mx) x15 MM. 
  (* exists (merge x13 Mx) x14 MM. *)
  exists (merge x17 Ox) x18 OO.
  (* exists (merge x16 Ox) x17 OO. *)
  splits; eauto.
  eapply mem_join_join_merge13_join'; eauto.
  eapply join_join_merge1; eauto.
  apply join_comm in H3; eauto.
  assert (
      (e, e0, merge x14 Mx, isr, st, merge x17 Ox, ab)
        |= (EX lg : list logicvar, OSLInv ct lg) ** Astruct ct OS_TCB_flag x1 **
        PV get_off_addr ct flag_off @ Tint8 |-r-> Vint32 (Int.repr 0) **
           PV get_off_addr ct loc_off @ Tint8 |-r-> x3 **
           PV get_off_addr ct ptr_off @ Tptr OS_EVENT |-r-> x4 ** 
         assertion.sll x2 x0 OS_TCB_flag V_OSTCBNext ** sllfreeflag x2 x0
    ).
  {
    sep remember (1::nil)%nat.
    simpl_sat_goal.
    exists Mx x14; eexists.
    exists Ox x17; eexists.
    splits; eauto.
    apply join_comm.
    apply join_merge_disj.
    clear - H19 H2.
    eapply mem_join_join_disjoint; eauto.
    apply join_comm.
    apply join_merge_disj.
    eapply osabst_join_join_disjoint; eauto.
  }
  unfold OSLInv in H17.
  sep normal in H17.
  sep destruct H17.
  sep split in H17; simpljoin1.
  sep_lifts_skp_in H17 ((ptr_off, _N_ 0), (ptr_off, _N_ 1)).
  (* sep lifts (5::11::nil)%nat in H17. *)
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17.
  sep_lifts_skp_in H17 ((loc_off, _N_ 0), (loc_off, _N_ 1)).
  (* sep lifts (5::10::nil)%nat in H17. *)
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17.
  sep_lifts_skp_in H17 ((flag_off, _N_ 0), (flag_off, _N_ 1)). 
  (* sep lifts (5::9::nil)%nat in H17. *)
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17. 
  
  unfold TCBFree_Not_Eq.
  sep split.
  unfold assertion.sll in *.
  unfold1 sllseg.
  unfold sllfreeflag in *.
  unfold1 sllsegfreeflag.
  sep normal.
  sep eexists.
  sep split; eauto.
  inverts H24.
  unfold node; sep normal.
  sep eexists.
  sep split; eauto.
  assert (x19 = (Vint32 (Int.repr 0))).
  {
    (* assert (x18 = (Vint32 (Int.repr 0))). *)
    clear -H27 H20.
    (* clear - H10 H20. *)
    unfolds in H20; destruct H20.
    substs.
    simpl in H27; tryfalse.
    auto.
  }
  substs.
  instantiate (1:=x22).
  instantiate (1:=x21).
  sep auto.

  clear - H H_indom.
  intro.
  inverts H0.
  unfolds in H_indom.
  apply H_indom.
  unfold indom.
  eauto.

  substs.
  sep auto.
  rewrite <- H15.
  auto.

  clear - H H_indom.
  intro.
  inverts H0.
  unfolds in H_indom.
  apply H_indom.
  unfold indom.
  eauto.
Qed.

Lemma AOSTCBList'_AOSTCBFreeList_set_curtid_indom :
  forall p1 p2 l1 curtcb l2 rtbl ct tcbls lfree pf s P tid objl absobjs ecbls vhold fecbh fecbvl, 
    RH_CurTCB tid tcbls ->
    indom tcbls ct ->
    s |= AOSTCBList'' p1 p2 l1 (curtcb::l2) rtbl ct tcbls pf **
      AOSTCBFreeList' pf lfree ct tcbls **
      AOBJ objl absobjs ecbls vhold p1 (l1++(curtcb::l2)) fecbh fecbvl ** P -> 
    exists l1' curtcb' l2' pf' lfree',
      s |= AOSTCBList'' p1 (Vptr tid) l1' (curtcb' :: l2') rtbl tid tcbls pf' **
        AOSTCBFreeList' pf' lfree' tid tcbls **
        AOBJ objl absobjs ecbls vhold p1 (l1'++(curtcb'::l2')) fecbh fecbvl ** P. 
Proof.
  intros.
  rename H0 into H_indom.
  rename H1 into H0.
  unfold AOSTCBList'' in H0.
  unfold AOSTCBFreeList' in H0.
  
  (*4 cases*)
  apply disj_split in H0.
  destruct H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.

  (*1*)
  unfold TCBFree_Not_Eq in H0.
  sep split in H0; simpljoin1.
  unfolds in H; simpljoin1.
  sep_lifts_skp_in H0 ((tcbdllseg, _N_ 0), (tcbdllseg, _N_ 1)). 
  (* sep lifts (4::5::nil)%nat in H0. *)
  pose proof H2 tid.
  unfold get in H; simpl in H.
  rewrite H in H7.
  destruct (TcbMod.get x1 tid) eqn : eq1;
    destruct (TcbMod.get x2 tid) eqn : eq2;
    tryfalse.
  substs.
  (*tid in x1*)
  lets Hx : tcb_list_split_by_tcbls eq1 H3 H0.
  simpljoin1.
  assert (H7_bak := H7). 
  sep lifts (2::3::nil)%nat in H7.
  assert (V_OSTCBNext (last (x6 :: x7) nil) = Some (Vptr ct)) as H_last.
  eapply tcbdllseg_last_nextptr in H7; auto.
  eapply tcbdllseg_compose in H7.
  
  lets Hx: TCBList_P_combine_copy H9 H4.
  instantiate (1:=merge x9 x2).
  clear - H2 H10.
  eapply TcbMod.join_merge_disj.
  apply join_comm in H10.
  eapply TcbMod.join_join_disj_l; eauto.
  assert (x6 :: x7 <> nil) by auto.
  apply Hx in H11; auto; clear Hx.
  replace ((x6 :: x7) ++ curtcb :: l2) with (x6 :: x7 ++ curtcb :: l2) in H7, H11.
  exists x5 x6 (x7 ++ curtcb :: l2) pf lfree.
  unfold AOSTCBList''.
  apply disj_split.
  left.
  sep normal.
  do 4 eexists.
  sep split; eauto.
  sep cancel 5%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 1%nat 1%nat.
  replace ((x5 ++ x6 :: x7) ++ curtcb :: l2) with (x5 ++ x6 :: x7 ++ curtcb :: l2) in H7.
  sep cancel 3%nat 1%nat.
  sep cancel AOBJ. 
  unfold AOSTCBFreeList'.
  sep auto.
  left.
  unfold TCBFree_Not_Eq.
  sep auto.
  clear - H7_bak.
  sep remember (2::4::nil)%nat in H7_bak; clear HeqH.
  clears.
  eapply tcbdllseg_sll_neq; eauto.
  
  rewrite <- app_assoc.
  auto.
  
  clear - H7_bak.
  sep remember (2::4::nil)%nat in H7_bak; clear HeqH.
  clears.
  assert (pf <> Vptr tid).
  eapply tcbdllseg_sll_neq; eauto.
  auto.
  clear - H2 H10.
  eapply join_merge23_join; eauto.
  rewrite app_comm_cons; auto.

  (*tid in x2*)
  substs.
  sep lift 2%nat in H0.
  lets Hx : tcb_list_split_by_tcbls eq2 H4 H0.
  simpljoin1.
  assert (H7_bak := H7). 
  exists (l1 ++ x5) x6 x7 pf lfree. 
  unfold AOSTCBList''.
  apply disj_split.
  left.
  sep normal.
  exists x10 x0 (merge x1 x8) x9.
  sep split; eauto.
  sep cancel 6%nat 1%nat.
  sep cancel 2%nat 2%nat.
  rewrite H11 in H7_bak.
  replace (l1 ++ x5 ++ x6 :: x7) with ((l1 ++ x5) ++ x6 :: x7) in H7_bak.
  sep cancel 5%nat 2%nat.
  sep cancel AOBJ. 
  unfold AOSTCBFreeList'.
  sep auto.
  sep lift 2%nat.
  apply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  sep lifts (2::1::nil)%nat in H7_bak.
  eapply tcbdllseg_compose in H7_bak.
  sep auto.

  clear - H7.
  sep lifts (2::4::nil)%nat in H7.
  eapply tcbdllseg_sll_neq; eauto.
  
  rewrite <- app_assoc.
  auto.

  assert (pf <> Vptr tid).
  sep lifts (2::4::nil)%nat in H7.
  eapply tcbdllseg_sll_neq; eauto.
  auto.

  clear - H1 H3 H8 H10 H2 H7.
  destruct l1.
  rewrite app_nil_l.
  simpl in H3; simpljoin1.
  sep remember (3::nil)%nat in H7.
  destruct_s s.
  simpl in H7; simpljoin1.
  rewrite jl_merge_emp'.
  auto.
  eapply TCBList_P_combine_copy; eauto.
  clear - H2 H10.
  eapply TcbMod.join_merge_disj.
  apply join_comm in H2.
  apply TcbMod.disj_comm.
  eapply TcbMod.join_join_disj_l; eauto.
  sep lift 3%nat in H7.
  eapply tcbdllseg_last_nextptr; eauto.

  clear - H2 H10.
  eapply join_join_join_merge; eauto.

  (*2 false*)
  unfold TCBFree_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.
  
  (*3 false*)
  unfold TCBFree_Not_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  (*4*)
  simpljoin1.

  unfold TCB_Not_In in H0.
  unfold tcblist in H0.
  sep split in H0.
  lets Hx: tcblist_indom_ptr_in_tcblist H2 H_indom.
  simpljoin1.
  false; apply H3; auto.
Qed.


Lemma OSInv_set_curtid1 :
  forall e e0 M M' isr st O ab b tp tp0 tid ct P,
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) M (b, 0) (Vptr tid) = Some M' ->
    (e, e0, M, isr, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M, isr, st, O, ab) |= OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr ct ** P ->
    exists tls,
      get O abtcblsid = Some (abstcblist tls) /\
        (indom tls ct /\
           (e, e0, M', isr, st, set O curtid (oscurt tid), ab)
             |= OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid ** P \/
         ~ indom tls ct /\
           (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
               satp (e, e0, Mx, isr, st) Ox (EX lg, OSLInv ct lg) ->
               join M' Mx MM ->
               join O Ox OO ->
               (e, e0, MM, isr, st, set OO curtid (oscurt tid), ab)
                 |=  OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid ** P)).
Proof.
  intros.
  rewrite <- osinv''_OSInv in H2.
  unfold osinv'' in H2.
  sep normal in H2.
  sep destruct H2.
  get_hsat Hsat.
  match type of Hsat with
    context [HTCBList ?x] => 
      assert (get O abtcblsid = Some (abstcblist x))
  end.
  {
    sep_rmb_trms_in Hsat (Aabsdata abstcblsid).
    simpl in Hsat; simpljoin1. 
    eapply join_get_l; eauto.
  }
  eexists.
  split; eauto.
  

  assert (os_ucos_h.OS_TCB = tp0).
  {
    sep_lifts_skp_in Hsat ((OSTCBCur, _N_ 0), (OSTCBCur, _N_ 1)).
    sep remember (1::2::nil)%nat in Hsat. 
    (* sep remember (2::22::nil)%nat in H2. (*21改成23*) *) 
    simpl in Hsat; simpljoin1.
    rewrite H27 in H18; inverts H18.
    auto.
  }
  subst tp0.
  
  assert (x4 = Vptr x13).
  {
    sep_rmb_trms_in Hsat AOSTCBList''.
    (* sep remember (3::nil)%nat in H2. *)
    simpl in Hsat; simpljoin1.
    destruct H8; simpljoin1; auto.
  }
  substs.
  sep_lifts_skp_in Hsat ((OSTCBCur, _N_ 0), (OSTCBCur, _N_ 1)).
  sep remember (1::2::nil)%nat in Hsat. 
  (* sep remember (2::22::nil)%nat in H2. (*21改成23*) *) 
  eapply sep_combine_lemmas.GV_combine_ro_frm in Hsat.
  sep split in Hsat.
  simpl in Hsat; simpljoin1.
  
  assert (x13 = ct).
  {
    clear - H4.
    simpl in H4.
    destruct x13; destruct ct.
    inverts H4; auto.
  }
  substs.
  
  assert (Hor: indom x11 ct \/ ~ indom x11 ct).
  { tauto. }
  destruct Hor.
  (*indom tcbls ct*)
  left.
  split; auto.
  rewrite <- osinv''_OSInv.
  unfold osinv''.
  sep normal.
  unfolds in H14; simpl in H14.
  rewrite H in H14; inverts H14.
  lets Hx: lmachLib.store_mapstoval_frame H15 H6 H0.
  simpljoin1.

  sep_lifts_trms_in H10 (AOSTCBList'', AOSTCBFreeList', AOBJ).
  (* sep lifts (1::10::nil)%nat in H10. *)
  lets Hx: AOSTCBList'_AOSTCBFreeList_set_curtid_indom H10; auto.
  unfolds.
  instantiate (TEMP11 := tid).
  clear - H1 H2.
  simpl in H1; simpljoin1.
  unfolds in H4; simpljoin1.
  assert (get O abtcblsid = Some (abstcblist x)).
  { eapply join_get_l; eauto. }
  rewrite H2 in H5.
  inverts H5.
  eauto.
  simpljoin1.
  sep eexists.

  sep_lifts_skp ((OSTCBCur, _N_ 0), (OSTCBCur, _N_ 1)).  
  (* sep lifts (2::22::nil)%nat. (*21改成23*) *)
  eapply sep_combine_lemmas.GV_combine_ro'_frm; eauto.
  sep remember (1::nil)%nat.
  simpl.
  exists x13 x20.  
  do 4 eexists.
  splits; eauto.
  eapply join_emp; eauto.
  do 7 eexists.
  splits; eauto.
  eapply join_emp; eauto.
  eapply join_emp; eauto.
  eexists.
  unfold emposabst; splits; eauto.
  unfolds.
  eexists; splits; eauto.
  unfolds in H15; simpljoin1.
  unfold store in H5.
  lets Hx: lmachLib.storebytes_ptomvallist_eqlen_infer p H5.
  simpl.
  destruct tid; destruct ct; simpl; auto.
  auto.
  unfolds; auto.
  substs.
  sep_rmb_trms_in H4 curtid.
  (* sep remember (16::nil)%nat in H5. *)
  simpl in H4; simpljoin1.
  sep_rmb_trms curtid. 
  (* sep remember (16::nil)%nat. *) 
  simpl.
  do 6 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_sig_set; eauto.
  substs.
  sep auto.


  (*not indom 13 ct*)
  right.
  split; auto.
  intros.

  pose proof H5 ab.
  rewrite <- osinv''_OSInv.
  unfold osinv''.
  sep normal.
  unfolds in H14; simpl in H14.
  rewrite H in H14; inverts H14.
  lets Hx: lmachLib.store_mapstoval_frame H15 H6 H0.
  simpljoin1.

  sep_rmb_trms_in H10 AOSTCBList''. 
  (* sep remember (2::nil)%nat in H10. *)
  assert ((e, e0, M', isr, st, O, ab) |= 
            GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-> (Vptr tid) **
            AOSTCBList'' x3 (Vptr ct) x5 (x6 :: x7) x8 ct x11 x15 ** H4). 
  {
    substs.
    sep remember (1::nil)%nat.
    simpl.
    do 6 eexists.
    splits; eauto.
    apply join_emp; auto.
    do 7 eexists.
    splits; eauto.
    eapply join_emp; eauto.
    apply join_emp; eauto.
    eexists.
    splits; eauto.
    unfolds; auto.
    unfolds.
    eexists; splits; eauto.
    unfolds in H15; simpljoin1.
    eapply lmachLib.storebytes_ptomvallist_eqlen_infer; eauto.
    simpl; destruct tid, ct; auto.
    unfolds; auto.
  }
  substs.
  sep_lifts_trms_in H13 (AOSTCBList'', AOSTCBFreeList', AOBJ). 
  (* sep lifts (2::11::nil)%nat in H13. *)
  lets Hx: AOSTCBList'_AOSTCBFreeList_set_curtid_not_indom H13 H7 H8 H9.
  unfolds.
  instantiate (TEMP10 := tid).
  clear - H1 H2.
  simpl in H1; simpljoin1.
  unfolds in H4; simpljoin1.
  assert (get O abtcblsid = Some (abstcblist x)).
  { eapply join_get_l; eauto. }
  rewrite H2 in H5.
  inverts H5.
  eauto.
  auto.
  simpljoin1.
  sep eexists.
  sep_lifts_skp ((OSTCBCur, _N_ 0), (OSTCBCur, _N_ 1)). 
  (* sep lifts (2::22::nil)%nat. (*21改成23*) *)
  eapply sep_combine_lemmas.GV_combine_ro'_frm; eauto.
  sep_rmb_trms_in H4 curtid. 
  (* sep remember (17::nil)%nat in H5. *)
  simpl in H4; simpljoin1.
  sep_rmb_trms curtid. 
  (* sep remember (17::nil)%nat. *)
  simpl.
  exists empmem MM.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_sig_set; eauto.
  substs.
  sep auto.
Qed.


Lemma AHprio_starinv_isr_atoy_inv_false :
  forall e e0 M M1 M2 isr st O o1 o2 ab n i tid,
    join o1 o2 O -> (i > 0)%nat -> (forall i : hid, isr i = false) ->
    (e, e0, M, isr, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M1, isr, st, o2, ab) |= starinv_isr I i n ->
    (e, e0, M2, isr, st, o1, ab) |= atoy_inv ->
    False.
Proof.
  intros.
  apply starinv_isr_osabst_emp in H3; auto.
  apply atoy_inv_osabst_emp in H4; auto.
  substs.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  pose proof H5 abtcblsid.
  pose proof H abtcblsid.
  rewrite OSAbstMod.emp_sem in H8.
  destruct (OSAbstMod.get O abtcblsid) eqn : eq1; tryfalse.
  destruct (OSAbstMod.get x2 abtcblsid) eqn: eq2; tryfalse.
  destruct (OSAbstMod.get x3 abtcblsid); tryfalse.
  destruct (OSAbstMod.get x3 abtcblsid) eqn : eq3; tryfalse.
  unfold get in H2; simpl in H2; rewrite H2 in eq2; tryfalse.
Qed.

Lemma starinv_isr_set_highest_tid :
  forall n low i0 e e0 m c O ab tid b tp tp' ct M' x11 i,
    (forall i : hid, x11 i = false) ->
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) m (b, 0) (Vptr tid) = Some M' ->
    (e, e0, m, x11, (i, i0, c), O, ab) |= AHprio GetHPrio tid ** Atrue -> 
    (e, e0, m, x11, (i, i0, c), O, ab) |= GV OSTCBCur @ Tptr tp' |-r-> Vptr ct ** starinv_isr I low n ->
    (exists tls,
        get O abtcblsid = Some (abstcblist tls) /\
          (indom tls ct /\
             (e, e0, M', x11, (i, i0, c), set O curtid (oscurt tid), ab)
               |= starinv_isr I low n ** (EX tp0 : type, GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid) \/
             ~ indom tls ct /\
               (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
                   satp (e, e0, Mx, x11, (i, i0, c)) Ox (EX lg, OSLInv ct lg) ->
                   join M' Mx MM ->
                   join O Ox OO ->
                   (e, e0, MM, x11, (i, i0, c), set OO curtid (oscurt tid), ab)
                     |= starinv_isr I low n ** (EX tp0 : type, GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid)))).
Proof.
  inductions n; intros.
  unfold starinv_isr in *.
  destruct low.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1.
  tryfalse. 
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.

  unfold I in *; unfold getinv in *.
  

  assert ((e, e0, m, x, (i, i0, c), O, ab)
            |= OSInv ** GV OSTCBCur @ Tptr tp' |-r-> Vptr ct ** Aemp).
  sep auto.
  lets Hx: OSInv_set_curtid1 H0 H1 H2 H3.
  simpljoin1.
  eexists.
  splits; eauto.
  destruct H5; simpljoin1.
  left.
  split; auto.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  right.
  split; auto.
  intros.
  lets Hx: H6 H7 H10 H11.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  substs.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  sep auto.

  destruct low.
  simpl getinv in *.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.
  unfold atoy_inv in H9.
  unfold A_isr_is_prop in H9.
  unfold atoy_inv' in H9.
  simpl in H9; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H7; simpljoin1.
  apply map_join_pos in H6; simpljoin1.
  rewrite emp_sem in H2; tryfalse.
  
  simpl getinv in *.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.
  unfold aemp_isr_is in H9.
  unfold A_isr_is_prop in H9.
  simpl in H9; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  apply map_join_pos in H5; simpljoin1.
  rewrite emp_sem in H2; tryfalse.

  (*ind case*)
  unfold starinv_isr in *; fold starinv_isr in *.
  sep normal in H3; destruct H3.
  (*  sep normal; exists x. *)
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.

  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  eapply OSInv_set_curtid1 in H9; eauto.
  simpljoin1.
  destruct H4; simpljoin1.
  eexists; splits; eauto.
  left.
  split; auto.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.

  eexists.
  splits; eauto.
  right.
  split; eauto.
  intros.
  lets Hx: H5 H6 H7 H9.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  
  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  false.


  simpl_sat H9; simpljoin1.
  simpl in H13; simpljoin1.
  eapply AHprio_starinv_isr_atoy_inv_false with (i:=2%nat); eauto.

  sep remember (1::nil)%nat in H9.
  simpl_sat H9; simpljoin1.
  simpl in H9; simpljoin1.
  lets Hx: IHn H H0 H1 H2 H10.
  simpljoin1.
  eexists; splits; eauto.
  destruct H4; simpljoin1.
  left.
  split; auto.
  sep normal in H5; destruct H5.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  simpl getinv.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  sep auto.

  right.
  split; auto.
  intros.
  lets Hx: H5 H6 H7 H9.
  sep normal in Hx; destruct Hx.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  simpl getinv.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  sep auto.
Qed.


Lemma GoodI_I :
  GoodI I GetHPrio OSLInv.
Proof.
  intros.
  unfold GoodI.
  splits.
-
  unfolds INUM.
  intros.
  unfold starinv_noisr in H.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H1 in H.
  assert (getinv (I 1%nat) = atoy_inv) by auto. 
  assert (getinv (I 2%nat) = aemp_isr_is ) by auto.
  assert (getinv (I 3%nat) = aemp_isr_is) by auto.
  rewrite H3 in H.  
  rewrite H2 in H.
  rewrite H4 in H.
  sep lift 4%nat in H.
  apply aemp_isr_elim_dup in H.
  sep lift 3%nat in H.
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H.
  apply atoy_abst_elim_dup in H.
  simpljoin1.
  eapply OSInv_prop; eauto.
  eapply my_join_disj; eauto.

-
  introv Hsw.
  unfold SWINVt in Hsw.
  destruct o as [[[[]]]].
  simpl_sat Hsw; simpljoin1.
  simpl in H4; simpljoin1.
  exists x11 x5.
  splits; eauto.
  simpl get_mem.
  apply join_comm in H0.
  eapply mapstoval_false_join_load_vptr; eauto.
  
  unfold SWINV in H3.
  simpl_sat H3; simpljoin1.
  unfold getie in *; unfold gettaskst in *.
  destruct l; destruct p.
  simpl in H12.
  simpl in H18; simpljoin1.
  lets Hres : osq_inv_in H2 H12.
  sep destruct Hres.

  simpl_sat Hres; simpljoin1.
  simpl in H15; simpljoin1.
  unfold AOSTCBList' in H5.
  destruct H5.
  do 4 destruct H.
  sep split in H.
  simpljoin1.
  clear H3 H5 H8 H9 H10; clears.
  sep remember (3::nil)%nat in H.
  simpl in H; simpljoin1.
  rewrite H6 in H17; inverts H17.
  assert (Vptr tid = Vptr x8 /\ x0 = x2).
  eapply mapstoval_false_rule_type_val_match_eq with (M := m) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto. 
  eapply join_sub_r; eauto.

  apply join_sub_l in H5; apply sub_trans with (m2 := x13); auto.
  apply join_sub_l in H1; apply sub_trans with (m2 := x); auto.
  apply join_sub_l in H0; apply sub_trans with (m2 := m); auto.
  unfold sub.
  eexists emp.
  apply join_comm.
  apply join_emp; auto.

  destruct H; substs.
  inverts H.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.

  destruct H.
  sep split in H.
  simpljoin1.
  sep remember (2::nil)%nat in H.
  simpl in H; simpljoin1.
  rewrite H6 in H18; inverts H18.
  assert (Vptr tid = Vptr x8 /\ x0 = x2).
  eapply mapstoval_false_rule_type_val_match_eq with (M := m) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto. 
  eapply join_sub_r; eauto.

  apply join_sub_l in H8; apply sub_trans with (m2 := x13); auto.
  apply join_sub_l in H1; apply sub_trans with (m2 := x); auto.
  apply join_sub_l in H0; apply sub_trans with (m2 := m); auto.
  unfold sub.
  eexists emp.
  apply join_comm.
  apply join_emp; auto.

  destruct H; substs.
  inverts H.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.

-
  introv Hsw Hpr Hget Hs.
  destruct o as [[[[]]]].
  simpl in Hget.
  unfold get_smem in Hs; unfold get_mem in Hs.
  unfold SWINVt in *.
  unfold substaskst.
  unfold SWINV in *.
  sep normal in Hsw.
  destruct Hsw; destruct H.

  sep remember (2::4::5::nil)%nat in H.
  simpl in H; simpljoin1.
  destruct l; destruct p.
  substs.

  unfold invlth_isr in *.
  rewrite Nat.sub_0_r in *.
  lets Hx: starinv_isr_set_highest_tid H18 Hget Hs Hpr H15.
  simpljoin1.
  eexists.
  splits;eauto.
  destruct H0; simpljoin1.
  left.
  split; auto.
  sep normal in H1; destruct H1.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  substs.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep normal.
  sep eexists.
  rewrite Nat.sub_0_r.
  sep remember (2::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  auto.

  right.
  split; auto.
  intros.
  lets Hx: H1 H2 H3 H4.
  sep normal in Hx.
  destruct Hx.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  substs.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep normal.
  pose proof H2 ab.
  destruct H6.
  unfold OSLInv in H6.
  destruct H6.
  simpl in H6; simpljoin1.
  sep eexists.
  rewrite Nat.sub_0_r.
  sep remember (2::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.

- apply GoodSched_GetHPrio.
  
Qed.
