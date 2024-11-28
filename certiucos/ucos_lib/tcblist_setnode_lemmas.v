Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import symbolic_lemmas.
(* Require Import OSQPostPure. *)
Local Open Scope code_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Lemma tcbdllflag_set_node :
  forall vltcb vltcb' p s P head vl vl',
    s |= tcbdllflag head vltcb ** P ->
    tcblist_get p head vltcb = Some vl ->
    set_node p vl' head vltcb = vltcb' ->
    same_prev_next vl vl' ->
    s |= tcbdllflag head vltcb' ** P.
Proof.
  inductions vltcb; intros.
  simpl in H0; tryfalse.

  unfold tcblist_get in H0; fold tcblist_get in H0.
  unfold set_node in H1; fold set_node in H1.
  destruct(beq_val p head) eqn : eq1.
  inverts H0.
  substs.
  unfold tcbdllflag in *; unfold dllsegflag in *; fold dllsegflag in *.
  sep normal in H; do 2 destruct H; sep split in H.
  sep normal; sep eexists.
  sep split; eauto.
  clear - H2 H1.
  unfolds in H2.
  rewrite H1 in H2.
  destruct (V_OSTCBNext vl');
    destruct (V_OSTCBPrev vl);
    destruct (V_OSTCBPrev vl'); tryfalse; simpljoin; auto.    

  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  substs.
  unfold tcbdllflag in *; unfold dllsegflag in *; fold dllsegflag in *.
  sep normal in H.
  do 2 destruct H.
  sep split in H.
  sep normal; sep eexists; sep split; eauto.
  sep cancel 1%nat 1%nat.
  remember(set_node p vl' (nth_val' 0 a) vltcb) as vltcb'.
  rewrite eq2 in H3; inverts H3.
  eapply IHvltcb; eauto.
  unfolds in eq2.
  apply nth_val_nth_val'_some_eq in eq2; rewrite eq2 in Heqvltcb'.
  auto.
Qed.

Lemma tcblist_get_set_node_split :
  forall vltcb head p vl vl',
    tcblist_get p head vltcb = Some vl ->
    exists vltcb1 vltcb2,
      vltcb = vltcb1++vl::vltcb2 /\
      set_node p vl' head vltcb = vltcb1++vl'::vltcb2.
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.
  unfold tcblist_get in H; fold tcblist_get in H.
  unfold set_node; fold set_node.
  destruct(beq_val p head) eqn : eq1.
  inverts H.
  do 2 eexists.
  rewrite app_nil_l; eauto.

  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  lets Hx : IHvltcb v p vl vl' H. 
  destruct Hx; destruct H0; destruct H0.
  substs.
  exists (a::x) x0.
  rewrite <- app_comm_cons; split; auto.
  unfolds in eq2.
  apply nth_val_nth_val'_some_eq in eq2.
  rewrite eq2.
  rewrite H1.
  rewrite <- app_comm_cons; auto.
Qed.

Definition rtbl_set_one_bit rtbl rtbl' prio :=
  exists row bitx,
    0 <= Int.unsigned prio < 64 /\
(*    array_type_vallist_match Int8u rtbl /\ length rtbl = ∘ OS_RDY_TBL_SIZE /\
    array_type_vallist_match Int8u rtbl' /\ length rtbl' = ∘ OS_RDY_TBL_SIZE /\ *)
    nth_val' (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Vint32 row /\
    nth_val' (Z.to_nat (Int.unsigned (prio&ᵢ$ 7))) OSMapVallist = Vint32 bitx /\
    rtbl' = update_nth_val (Z.to_nat (Int.unsigned(prio>>ᵢ$ 3))) rtbl (Vint32 (Int.or row bitx)).

Definition get_last_tcb_ptr (l: list vallist) (x : val) :=
  match l with
    | nil => Some x
    |  _ => V_OSTCBNext (last l nil)
  end.

Lemma get_last_tcb_ptr_prop:
  forall l1 a x1 x z,
    V_OSTCBNext a = Some x1 ->
    get_last_tcb_ptr l1 x1 = Some x ->
    get_last_tcb_ptr (a :: l1) z = Some x.
Proof.
  inductions l1; intros; simpl in *; auto.
  inverts H0.
  auto.
Qed.

Lemma TCBList_P_Split:
  forall l1 x l2 rtbl tcbls,
    TCBList_P x (l1 ++ l2) rtbl tcbls ->
    exists y tls1 tls2,
      get_last_tcb_ptr l1 x  = Some y /\
      TcbMod.join tls1 tls2 tcbls /\
      TCBList_P x l1 rtbl tls1 /\
      TCBList_P y l2 rtbl tls2.
Proof.
  inductions l1.
  intros.
  simpl in H.
  exists x TcbMod.emp tcbls.
  simpl.
  splits; simpljoin1; auto.
  apply TcbMod.join_emp; auto.
  intros.
  simpl in H.
  simpljoin1.
  lets Hx : IHl1 H3.
  simpljoin1.
  lets Has : get_last_tcb_ptr_prop (Vptr x0)  H0 H.
  exists x.
  lets Hab : tcbjoin_join_ex  H1 H4.
  simpljoin1.
  exists x6 x5.
  splits; eauto.
  simpl.
  unfold TcbJoin in H7.
  do 4 eexists; splits; eauto.
Qed.

Fixpoint vptr_next (head:val) (vltcb:list vallist) :=
  match vltcb with
    | nil => True
    | vl::vltcb' =>
      exists a, head = Vptr a /\
                match V_OSTCBNext vl with
                  | Some vn => vptr_next vn vltcb'
                  | None => False
                end
  end.

Require Import new_inv. 

Definition distinct_tcbdllseg_next_ptr_vnull (head : val) (l : list vallist) :=
  distinct_tcbdllseg_next_ptr head l /\ get_last_tcb_ptr l head = Some Vnull /\
  vptr_next head l.

Lemma tcbdllseg_vptr_next :
  forall vltcb head headprev tail tailnext s P,
    s |= tcbdllseg head headprev tail tailnext vltcb ** P ->
    vptr_next head vltcb.
Proof.
  inductions vltcb; intros.
  simpl; auto.

  unfold tcbdllseg in H.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  sep remember (1::nil)%nat in H.
  destruct s as [[[[[]]]]].
  destruct l as [[]].
  unfold sat in H; fold sat in H.
  simpl getmem in H; simpl getabst in H; simpl substmo in H.
  simpljoin.
  eapply IHvltcb in H8.
  unfold vptr_next; fold vptr_next.
  rewrite H0.
  unfold node in H7; sep normal in H7.
  destruct H7.
  sep split in H.
  simpljoin.
  eauto.
Qed.

Lemma tcbdllseg_get_last_tcb_ptr :
  forall vl head headprev tail tailnext P s,
    s |= tcbdllseg head headprev tail tailnext vl ** P ->
    get_last_tcb_ptr vl head = Some tailnext.
Proof.
  induction vl; intros.
  destruct_s s; simpl in H; simpljoin.
  simpl; auto.

  unfold tcbdllseg in H; unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s s.
  unfold sat in H; fold sat in H.
  Ltac simpl_state := simpl substmo in *; simpl getmem in *; simpl getabst in *.
  simpl_state; simpljoin1.
  unfold tcbdllseg in IHvl.
  lets Hx: IHvl H8.
  simpl.
  destruct vl; auto.
  simpl in Hx; inverts Hx; auto.
Qed.

Lemma tcbdllseg_distinct_tcbdllseg_next_ptr_vnull :
  forall vltcb head headprev tail s P,
    s |= tcbdllseg head headprev tail Vnull vltcb ** P ->
    distinct_tcbdllseg_next_ptr_vnull head vltcb.
Proof.
  intros.
  unfolds.
  split.
  -
    inductions vltcb; intros.
    + 
      unfolds.
      simpl.
      unfold tcbdllseg in H.
      unfold dllseg in H.
      sep split in H.
      substs.
      auto.
    +
      unfold tcbdllseg in H.
      unfold dllseg in H; fold dllseg in H.
      sep normal in H.
      destruct H.
      sep split in H.
      destruct s as [[[[[[]]]]]].
      destruct l as [[]].
      assert
        (
          (e, e0, m, i, (i0, i1, c), o, a0)
            |= node head a OS_TCB_flag **
            dllseg x head tail Vnull vltcb OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
            P
        ) as H_bak by auto.
      sep remember (1::nil)%nat in H.
      simpl_sat H; simpljoin.
      unfold tcbdllseg in IHvltcb.
      lets Hx: IHvltcb H8.

      unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
      rewrite H0.
      destruct vltcb; auto.
      split; auto.
      eapply not_ptr_in_tcbdllseg1; eauto.
  -
    split.
    eapply tcbdllseg_get_last_tcb_ptr; eauto.
    eapply tcbdllseg_vptr_next; eauto.
Qed.

Lemma app_cons_not_nil :
  forall {A} (vl1:list A) v vl2,
  exists a vl', vl1++v::vl2 = a::vl'.
Proof.
  inductions vl1; intros.
  rewrite app_nil_l; eauto.
  rewrite <- app_comm_cons.
  pose proof IHvl1 v vl2.
  simpljoin.
  rewrite H.
  exists a (x::x0).
  auto.
Qed.

Lemma ptr_in_tcbdllseg1_preserv :
  forall vltcb1 vl vl' vltcb2 head p,
    ptr_in_tcbdllseg1 p head (vltcb1 ++ vl :: vltcb2) ->
    same_prev_next vl vl' ->
    ptr_in_tcbdllseg1 p head (vltcb1 ++ vl' :: vltcb2).
Proof.
  inductions vltcb1; intros.
  rewrite app_nil_l in *.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val p head) eqn : eq1; auto.
  unfolds in H0.
  destruct (V_OSTCBNext vl); tryfalse.
  destruct (V_OSTCBNext vl'); tryfalse.
  simpljoin; auto.
  rewrite <- app_comm_cons in *.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val p head) eqn : eq1; auto.
  destruct (V_OSTCBNext a); tryfalse.
  eapply IHvltcb1; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_preserve :
  forall vltcb1 vltcb2 vl vl' head,
    distinct_tcbdllseg_next_ptr_vnull head (vltcb1++vl::vltcb2) ->
    same_prev_next vl vl' ->
    distinct_tcbdllseg_next_ptr_vnull head (vltcb1++vl'::vltcb2).
Proof.
  inductions vltcb1; intros.
  -
    rewrite app_nil_l in *.
    unfold distinct_tcbdllseg_next_ptr_vnull in *; fold distinct_tcbdllseg_next_ptr_vnull in *.
    destruct H.
    destruct H1.
    unfold distinct_tcbdllseg_next_ptr in *; fold distinct_tcbdllseg_next_ptr in *.
    unfold get_last_tcb_ptr in *; fold get_last_tcb_ptr in *.
    split.
    destruct vltcb2; auto.
    unfolds in H0.
    destruct (V_OSTCBNext vl) eqn : eq1; tryfalse.
    destruct (V_OSTCBNext vl'); tryfalse.
    destruct H0; substs.
    auto.
    split.
    destruct vltcb2.
    simpl in *.
    unfolds in H0.
    rewrite H1 in H0.
    destruct (V_OSTCBNext vl'); tryfalse.
    destruct H0; substs; auto.
    unfold last in *; fold last in *.
    auto.
    unfold vptr_next in *; fold vptr_next in *.
    destruct H2.
    exists x.
    destruct H2.
    split; auto.
    unfolds in H0.
    destruct (V_OSTCBNext vl); tryfalse.
    destruct (V_OSTCBNext vl'); tryfalse.
    destruct H0; substs; auto.
  -
    rewrite <- app_comm_cons in H.
    rewrite <- app_comm_cons.
    unfold distinct_tcbdllseg_next_ptr_vnull in *.
    destruct H.
    unfold distinct_tcbdllseg_next_ptr in *; fold distinct_tcbdllseg_next_ptr in *.
    pose proof app_cons_not_nil vltcb1 vl vltcb2.
    pose proof app_cons_not_nil vltcb1 vl' vltcb2.
    simpljoin.
    rewrite H3.
    rewrite H2 in H.
    destruct (V_OSTCBNext a) eqn: eq1; tryfalse.
    rewrite H2 in H1.
    unfold get_last_tcb_ptr in H1.
    pose proof IHvltcb1 vltcb2 vl vl' v.
    assert(
        distinct_tcbdllseg_next_ptr v (vltcb1 ++ vl :: vltcb2) /\
          get_last_tcb_ptr (vltcb1 ++ vl :: vltcb2) v = Some Vnull /\
          vptr_next v (vltcb1 ++ vl :: vltcb2)
      ).
    rewrite H2.
    destruct H.
    split; auto.
    split; auto.
    rewrite H2 in H4. 
    unfold vptr_next in H4; fold vptr_next in H4.
    destruct H4.
    destruct H4.
    destruct(V_OSTCBNext a); tryfalse.
    unfold vptr_next; fold vptr_next.
    inverts eq1.
    destruct H7.
    eauto.
    
    apply H5 in H6; auto; clear H5.
    rewrite H3 in H6.
    destruct H6.
    destruct H6.
    split.
    split; auto.
    rewrite <- H3 in *.
    rewrite <- H2 in *.
    destruct H.
    clear - H H0.
    intro.
    apply H.

    eapply ptr_in_tcbdllseg1_preserv; eauto.
    eapply same_prev_next_sym; auto.
    split; auto.
    unfold vptr_next in *; fold vptr_next in *.
    rewrite eq1.
    destruct H4.
    destruct H4.
    exists x3.
    split; auto.
Qed.

Lemma tcblist_get_split :
  forall vltcb p head vl,
    tcblist_get p head vltcb = Some vl ->
    exists vltcb1 vltcb2, vltcb = vltcb1++vl::vltcb2.
Proof.
  inductions vltcb; intros.
  simpl in H; tryfalse.

  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val p head) eqn : eq1.
  inverts H.
  exists (nil (A:=vallist)) vltcb.
  rewrite app_nil_l; auto.

  destruct(V_OSTCBNext a) eqn: eq2; tryfalse.

  lets Hx: IHvltcb H; simpljoin.
  rewrite app_comm_cons.
  eauto.
Qed.

Lemma get_last_tcb_ptr_last :
  forall vltcb vl head,
    get_last_tcb_ptr (vltcb++vl::nil) head = Some Vnull ->
    V_OSTCBNext vl = Some Vnull.
Proof.
  inductions vltcb; intros.
  rewrite app_nil_l in H.
  simpl in H; auto.
  rewrite <- app_comm_cons in H.
  eapply IHvltcb with (head:=head).
  unfold get_last_tcb_ptr in *.

  pose proof app_cons_not_nil (A:=vallist) vltcb vl nil.
  do 2 destruct H0.
  rewrite H0.
  rewrite H0 in H.
  unfold last in *; auto.
Qed.

Lemma ptr_in_tcbdllseg1_true :
  forall vltcb1 vltcb2 vl vl' head p,
    V_OSTCBNext vl = Some p ->
    vptr_next head (vltcb1 ++ vl :: vl' :: vltcb2) ->
    ptr_in_tcbdllseg1 p head (vltcb1 ++ vl :: vl' :: vltcb2).
Proof.
  inductions vltcb1; intros.
  rewrite app_nil_l.
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  rewrite H.
  rewrite beq_val_true.
  destruct (beq_val p head); auto.

  rewrite <- app_comm_cons in *. 
  unfold ptr_in_tcbdllseg1; fold ptr_in_tcbdllseg1.
  unfold vptr_next in H0; fold vptr_next in H0; simpljoin.
  destruct (beq_val p (Vptr x)); auto.
  destruct (V_OSTCBNext a); tryfalse.
  eapply IHvltcb1; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_vnull_dup_node_false :
  forall vltcb1 vltcb2 head vl,
    distinct_tcbdllseg_next_ptr_vnull head (vl :: vltcb1 ++ vl :: vltcb2) ->
    False.
Proof.
  intros.
  destruct vltcb2.
  unfolds in H; simpljoin.
  rewrite app_comm_cons in H0.

  apply get_last_tcb_ptr_last in H0.
  unfold vptr_next in H1; fold vptr_next in H1.
  simpljoin.
  destruct (V_OSTCBNext vl) eqn : eq1; tryfalse.
  inverts H0.
  destruct vltcb1.
  rewrite app_nil_l in H2.
  unfold vptr_next in H2; simpljoin; tryfalse.
  rewrite <- app_comm_cons in H2.
  unfold vptr_next in H2; simpljoin; tryfalse.

  unfolds in H; simpljoin.
  unfold distinct_tcbdllseg_next_ptr in H; fold distinct_tcbdllseg_next_ptr in H.
  pose proof app_cons_not_nil (A:=vallist) vltcb1 vl (v::vltcb2).
  simpljoin.
  rewrite H2 in H.
  destruct (V_OSTCBNext vl) eqn : eq1; tryfalse.
  simpljoin.
  rewrite <- H2 in H3.

  destruct vltcb1.
  rewrite app_nil_l in H3.
  unfold distinct_tcbdllseg_next_ptr in H3; fold distinct_tcbdllseg_next_ptr in H3.
  rewrite eq1 in H3.
  destruct H3.
  unfold ptr_in_tcbdllseg1 in H3; fold ptr_in_tcbdllseg1 in H3.
  rewrite beq_val_true in H3.
  apply H3; auto.

  rewrite <- app_comm_cons in H3.
  unfold distinct_tcbdllseg_next_ptr in H3; fold distinct_tcbdllseg_next_ptr in H3.
  pose proof app_cons_not_nil (A:=vallist) vltcb1 vl (v::vltcb2); simpljoin.
  rewrite H4 in H3.
  destruct (V_OSTCBNext v1) eqn : eq2; tryfalse.
  destruct H3.
  rewrite <- H4 in H3.
  unfold vptr_next in H1; fold vptr_next in H1; simpljoin.
  rewrite eq1 in H6.
  rewrite <- app_comm_cons in H6.
  unfold vptr_next in H6; fold vptr_next in H6; simpljoin.
  destruct (V_OSTCBNext v1) eqn : eq3; tryfalse.
  inverts eq2.

  apply H3.
  eapply ptr_in_tcbdllseg1_true; auto.
Qed.

Lemma tcblist_get_distinct_tcbdllseg_next_ptr_vnull_false :
  forall vltcb head vl v p,
    distinct_tcbdllseg_next_ptr_vnull head (vl :: vltcb) ->
    V_OSTCBNext vl = Some v ->
    tcblist_get p v vltcb = Some vl ->
    False.
Proof.
  intros.
  eapply tcblist_get_split in H1; simpljoin.
  eapply distinct_tcbdllseg_next_ptr_vnull_dup_node_false; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_vnull_tail :
  forall vltcb vl head v,
    distinct_tcbdllseg_next_ptr_vnull head (vl :: vltcb) ->
    V_OSTCBNext vl = Some v ->
    distinct_tcbdllseg_next_ptr_vnull v vltcb.
Proof.
  inductions vltcb; intros.
  unfold distinct_tcbdllseg_next_ptr_vnull in *; simpljoin.
  split.
  unfold distinct_tcbdllseg_next_ptr in *; auto.
  split.
  simpl in *.
  rewrite H1 in H0; auto.
  simpl; auto.

  assert(distinct_tcbdllseg_next_ptr_vnull head (vl :: a :: vltcb)) as H_bak.
  auto.
  unfolds in H.
  simpljoin.
  unfold distinct_tcbdllseg_next_ptr in H; fold distinct_tcbdllseg_next_ptr in H.
  rewrite H0 in H.
  destruct H.
  destruct vltcb.
  unfolds.
  simpl.
  split; auto.
  split.
  simpl in H1; auto.
  simpl in H2.
  destruct H2.
  destruct H2.
  rewrite H0 in H4.
  eauto.
  destruct(V_OSTCBNext a) eqn : eq2; tryfalse.
  assert(distinct_tcbdllseg_next_ptr_vnull head (a :: v0 :: vltcb)).
  unfolds.
  destruct H3.
  splits; auto.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  rewrite eq2.
  split; auto.
  intro.
  apply H.
  clear - eq2 H5.
  unfold ptr_in_tcbdllseg1 in *; fold ptr_in_tcbdllseg1 in *.
  destruct (beq_val head v) eqn : eq1; auto.
  rewrite eq2.
  auto.

  unfold vptr_next in *; fold vptr_next in *.
  rewrite  eq2 in *.
  destruct H2.
  destruct H2.
  rewrite H0 in H5.
  simpljoin.
  destruct (V_OSTCBNext v0); tryfalse.
  eauto.

  eapply IHvltcb in H4; eauto.
  unfold distinct_tcbdllseg_next_ptr_vnull in *.
  simpljoin.
  splits; auto.
  unfold distinct_tcbdllseg_next_ptr; fold distinct_tcbdllseg_next_ptr.
  rewrite eq2.
  split; auto.

  unfold vptr_next in H9; fold vptr_next in H9.
  rewrite eq2 in H9; rewrite H0 in H9.
  simpljoin.
  unfold vptr_next; fold vptr_next.
  rewrite eq2.
  eexists.
  splits; eauto.
Qed.

Lemma distinct_tcbdllseg_next_ptr_vnull_tcblist_get_get_last_tcb_ptr :
  forall vltcb1 vltcb2 vl head tid p,
    tcblist_get (Vptr tid) head (vltcb1++vl::vltcb2) = Some vl ->
    get_last_tcb_ptr vltcb1 head = Some p ->
    distinct_tcbdllseg_next_ptr_vnull head (vltcb1++vl::vltcb2) ->
    p = (Vptr tid).
Proof.
  induction vltcb1; intros.
  simpl in H0; inverts H0.
  rewrite app_nil_l in H.
  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val (Vptr tid) p) eqn : eq1.
  apply beq_val_true_eq in eq1; auto.
  destruct(V_OSTCBNext vl) eqn : eq2; tryfalse.
  rewrite app_nil_l in H1.
  false.
  eapply tcblist_get_distinct_tcbdllseg_next_ptr_vnull_false; eauto.

  rewrite <- app_comm_cons in H.
  unfold tcblist_get in H; fold tcblist_get in H.
  destruct (beq_val (Vptr tid) head) eqn : eq1.
  inverts H.
  rewrite <- app_comm_cons in H1. 

  false.
  eapply distinct_tcbdllseg_next_ptr_vnull_dup_node_false; eauto.
  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  eapply IHvltcb1; eauto.
  unfold get_last_tcb_ptr in *; fold get_last_tcb_ptr in *.
  destruct vltcb1.
  simpl in H0.
  rewrite eq2 in H0; inverts H0; auto.
  auto.
  eapply distinct_tcbdllseg_next_ptr_vnull_tail; eauto.
Qed.

Lemma prio_set_rdy_in_tbl:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0 rtbl ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  rewrite H0 in Fnth'.
  inverts Fnth'.
  eapply or_and_combine; eauto.
  eapply Fpit; trivial.
  rewrite <- H; trivial.
  unfolds in H.
  eapply prio_bit_and_zero; eauto.
  subst.

  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) rtbl = Some (Vint32 z)).
  eapply nth_upd_neq.
  eapply neq_comm.
  eapply H.
  eapply Fnth'.
  eapply Fpit; auto.
Qed.

Lemma prio_set_rdy_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_in_tbl prio0 rtbl.
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  inverts Fnth'.
  rewrite H in H0.
  rewrite H in Fpit.
  lets Hzz: Fpit H0; eauto.
  rewrite -> Fnth in H2.
  inverts H2.
  eapply or_and_distrib; eauto.
  eapply prio_bit_and_zero; eauto.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) 
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = Some (Vint32 z)). 
  eapply nth_upd_neqrev; eauto.
  rewrite Fy in Fnth'. trivial.
  eapply Fpit; auto.
Qed.

Lemma RLH_RdyI_P_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_RdyI_P vl rtbl (prio0, stat) ->
    RLH_RdyI_P vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Frdy.
  unfolds in Frdy.
  unfolds.
  introv Frdy_tcb.
  eapply Frdy; eauto.
  unfolds.
  unfolds in Frdy_tcb.
  simpljoin1;split; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H6 in *.
  eapply prio_set_rdy_in_tbl_rev; eauto.
Qed.  

Lemma RdyTCBblk_rtbl_add:
  forall prio0 prio rtbl grp vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RdyTCBblk vl rtbl prio0 ->
    RdyTCBblk vl 
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
              prio0.
Proof.
  introv Fp0 Fp Fneq Fnth.
  unfold RdyTCBblk.
  intuition; trivial.
  eapply prio_set_rdy_in_tbl; eauto.
Qed.

Lemma RHL_RdyI_P_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_RdyI_P vl rtbl (prio0, stat) ->
    RHL_RdyI_P vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Frdy.
  unfolds in Frdy.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply RdyTCBblk_rtbl_add; eauto.
  eapply Frdy; eauto.
  eapply Frdy; eauto.
Qed.

Lemma prio_set_rdy_not_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_not_in_tbl prio0
                    (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                    (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_not_in_tbl prio0 rtbl.
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  inverts Fnth'.
  rewrite H in H0.
  rewrite H in Fpit.
  lets Hzz: Fpit H0; eauto.
  rewrite -> Fnth in H2.
  inverts H2.
  eapply or_and_distrib_zero; eauto.
  eapply prio_bit_and_zero; eauto.
  
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) 
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = Some (Vint32 z)). 
  eapply nth_upd_neqrev; eauto.
  rewrite Fy in Fnth'. trivial.
  eapply Fpit; auto.
Qed.

Lemma RLH_WaitS_P_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_WaitS_P vl rtbl (prio0, stat) ->
    RLH_WaitS_P vl 
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
         (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
      (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  introv Fwait_tcb Fst.
  eapply Fwait; eauto.
  unfolds.
  unfolds in Fwait_tcb.
  simpljoin1;splits; auto.
  rewrite Fvp in H.
  inversion H.
  rewrite <- H6 in *.
  eapply prio_set_rdy_not_in_tbl_rev; eauto.
Qed.  

Lemma RLH_Wait_all_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_TCB_Status_Wait_P vl rtbl (prio0, stat) ->
    RLH_TCB_Status_Wait_P vl 
                          (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                                          (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
                          (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intuition; trivial.
  eapply RLH_WaitS_P_rtbl_add; eauto.
Qed.
  
Lemma prio_set_rdy_not_in_tbl:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_not_in_tbl prio0 rtbl ->
    prio_not_in_tbl prio0
      (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
         (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_not_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
           ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
            (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
            Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  rewrite H0 in Fnth'.
  inverts Fnth'.
  eapply or_and_combine_zero; eauto.
  eapply Fpit; trivial.
  rewrite <- H; trivial.
  unfolds in H.
  eapply prio_bit_and_zero; eauto.
  subst.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) rtbl = Some (Vint32 z)).
  eapply nth_upd_neq.
  eapply neq_comm.
  eapply H.
  eapply Fnth'.
  eapply Fpit; auto.
Qed.

Lemma WaitTCBblk_rtbl_add:
  forall prio0 prio rtbl grp vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    WaitTCBblk vl rtbl prio0 ->
    WaitTCBblk vl 
               (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                               (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
               prio0.
Proof.
  introv Fp0 Fp Fneq Fnth.
  unfold WaitTCBblk.
  intuition; trivial.
  eapply prio_set_rdy_not_in_tbl; eauto.
Qed.

Lemma RHL_WaitS_P_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_WaitS_P vl rtbl (prio0, stat) ->
    RHL_WaitS_P vl 
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
         (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
      (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  inversion H.
  rewrite <- H1 in *.
  clear H1; subst.
  splits.
  eapply WaitTCBblk_rtbl_add; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
  eapply Fwait; eauto.
Qed.

Lemma RHL_Wait_all_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_TCB_Status_Wait_P vl rtbl (prio0, stat) ->
    RHL_TCB_Status_Wait_P vl 
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
         (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
      (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  intuition.
  eapply RHL_WaitS_P_rtbl_add; eauto.
Qed.

Lemma R_TCB_Status_P_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    R_TCB_Status_P vl rtbl (prio0, stat) ->
    R_TCB_Status_P vl 
      (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
         (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
      (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Fwait.
  unfolds in Fwait.
  unfolds.
  intros.
  intuition.
  eapply RLH_RdyI_P_rtbl_add; eauto.
  eapply RHL_RdyI_P_rtbl_add; eauto.
  eapply RLH_Wait_all_rtbl_add; eauto.
  eapply RHL_Wait_all_rtbl_add; eauto.
Qed.

Lemma TCBNode_P_rtbl_add:
  forall prio0 prio rtbl grp stat vl,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    V_OSTCBPrio vl = Some (Vint32 prio0) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    TCBNode_P vl rtbl (prio0, stat) ->
    TCBNode_P vl 
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7)))))
              (prio0, stat).
Proof.
  introv Fp0 Fp Fneq Fvp Fnth Ftcb.
  unfolds in Ftcb.
  unfolds.
  intros.
  intuition.
  eapply R_TCB_Status_P_rtbl_add; eauto.
Qed.

Require Import Lia.

Lemma TCBNode_P_prio:
  forall vl rtbl p t,
    TCBNode_P vl rtbl (p, t) ->
    0 <= Int.unsigned p < 64 /\ V_OSTCBPrio vl = Some (Vint32 p).
Proof.
  intros.
  unfolds in H.
  destruct H as (Hv2 & Hv3 & Hvs).
  unfolds in Hv3.
  fsimpl.
  rewrite Hv2 in H.
  inverts H.
  split; try lia; auto.
Qed.

Lemma TCBList_P_rtbl_add_simpl_version:
  forall vl vptr rtbl tcbls prio grp,
    0<= Int.unsigned prio < 64 ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    (forall tid p s, TcbMod.get tcbls tid  = Some (p, s) -> p <> prio 
    ) ->
    TCBList_P vptr vl rtbl tcbls ->
    TCBList_P vptr vl
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio &ᵢ$ 7))))) 
              tcbls.
Proof.
  inductions vl.
  intros; simpl in *; auto.
  intros.
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin1.
  exists x x0 x1 x2.
  splits; auto.
  destruct x2; destruct p.
  eapply TCBNode_P_rtbl_add; eauto.
  eapply TCBNode_P_prio; eauto.
  eapply H1; eauto.
  unfolds in H4.
  eapply TcbMod.join_sig_get; eauto.
  eapply TCBNode_P_prio; eauto.
  
  eapply IHvl; eauto.
  intros; eapply H1.
  eapply tcbjoin_get_get; eauto.
Qed.

Lemma get_last_tcb_ptr_prop':
  forall l1 a x1 x z,
    l1 <> nil ->
    V_OSTCBNext a = Some x1 ->
    get_last_tcb_ptr (a :: l1) z = Some x->
    get_last_tcb_ptr l1 x1 = Some x.
Proof.
  inductions l1; intros; simpl in *; auto; tryfalse.
Qed.

Lemma TCBList_P_Combine:
  forall l1 x l2 rtbl y tls1 tls2 tcbls,
    get_last_tcb_ptr l1 x  = Some y ->
    TcbMod.join tls1 tls2 tcbls ->
    TCBList_P x l1 rtbl tls1 ->
    TCBList_P y l2 rtbl tls2 ->
    TCBList_P x (l1 ++ l2) rtbl tcbls.
Proof.
  inductions l1.
  intros.
  simpl in *.
  inverts H.
  subst.
  apply TcbMod.join_meq in H0.
  apply TcbMod.meq_eq in H0.
  subst.
  auto.
  intros.
  simpl.
  simpl in H1.
  simpljoin1.
  assert (l1 = nil \/ l1 <> nil) by tauto.
  destruct H1.
  subst.
  assert ( get_last_tcb_ptr nil x1 = Some x1).
  simpl; auto.
  simpl in H6.
  subst.
  do 4 eexists; splits; try eapply H; eauto.
  unfolds in H4.
  apply TcbMod.join_comm in H4.
  apply TcbMod.join_meq in H4.
  apply TcbMod.meq_eq in H4.
  subst.
  auto.
  lets Hbcd : get_last_tcb_ptr_prop' H1 H3 H.
  lets Hds : tcbjoin_join_ex2 H4 H0.
  destruct Hds as (z & Hxa & Hxb).
  unfold TcbJoin in Hxb.
  do 4 eexists;  splits; eauto.
Qed.

(* important lemma *)
Lemma set_node_elim : 
  forall tid tcbls vltcb P s head tail t_rdy vl vl' prio st st' rtbl rtbl',
    ptr_in_tcbdllseg (Vptr tid) head (set_node (Vptr t_rdy) vl' head vltcb) ->
    tcblist_get (Vptr t_rdy) head vltcb = Some vl ->
    TCBList_P head vltcb rtbl tcbls ->
    get tcbls t_rdy = Some (prio, st) -> (*prove this*)
    TCBNode_P vl' rtbl' (prio, st') -> (*prove this*)
    rtbl_set_one_bit rtbl rtbl' prio -> (*prove this*)
    R_Prio_No_Dup tcbls ->
    same_prev_next vl vl' ->
    s |= tcbdllseg head Vnull tail Vnull (set_node (Vptr t_rdy) vl' head vltcb) ** P ->
    s |=
      EX (l1 l2 : list vallist) (tcb_cur:vallist) (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
  tcbdllseg head Vnull tail1 (Vptr tid) l1 **
    tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur::l2) **
    [| (set_node (Vptr t_rdy) vl' head vltcb) = l1 ++ (tcb_cur :: l2)|] **
    [|TcbMod.join tcbls1 tcbls2 (TcbMod.set tcbls t_rdy (prio, st'))|] **
    [|TCBList_P head l1 rtbl' tcbls1|] **
    [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl' tcbls2|] ** P.
Proof.
  intros.
  assert(TCBList_P head  (set_node (Vptr t_rdy) vl' head vltcb) rtbl' (TcbMod.set tcbls t_rdy (prio, st'))).
  lets Hx: tcblist_get_set_node_split H0.
  instantiate (1:=vl') in Hx.
  simpljoin.
  rewrite H9.
  lets Hx: TCBList_P_Split H1; simpljoin.
  assert(x1 = (Vptr t_rdy)).
  rewrite H9 in H7.    
  lets Hx: tcbdllseg_distinct_tcbdllseg_next_ptr_vnull H7.

  eapply distinct_tcbdllseg_next_ptr_preserve with (vl':=vl) in Hx.
  eapply distinct_tcbdllseg_next_ptr_vnull_tcblist_get_get_last_tcb_ptr; eauto.
  apply new_inv.same_prev_next_sym; auto.
  substs.

  assert(TcbMod.get x3 t_rdy = Some (prio, st)) as tcbls2_get_prio.
  unfold TCBList_P in H12; fold TCBList_P in H12; simpljoin.
  inverts H12.
  clear - H10 H14 H2.
  unfold get in H2; simpl in H2.
  assert(get x3 x1 = Some x6).
  clear -H14.
  eapply join_sig_get; eauto.
  assert (get tcbls x1 = Some x6).
  assert (join x2 x3 tcbls) by eauto.
  clear - H H0.
  jeat.
  unfold get in H0; simpl in H0.
  rewrite H2 in H0; inverts H0.
  unfold get in H; simpl in H; auto.
  
  assert(TCBList_P head x rtbl' x2).
  clear -H4 H5 H10 H11 tcbls2_get_prio.
  unfolds in H4; simpljoin.
  assert(x1 = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H H3.
  mauto.
  substs.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  eapply nth_val'_imp_nth_val_int; auto.
  clear - H5 tcbls2_get_prio H10.
  intros.
  unfolds in H5.
  assert(tid <> t_rdy).
  intro; substs.
  pose proof H10 t_rdy.
  destruct(TcbMod.get x2 t_rdy);
    destruct(TcbMod.get x3 t_rdy);
    destruct(TcbMod.get tcbls t_rdy); tryfalse.
  assert(TcbMod.get tcbls t_rdy = Some (prio, st)).
  eapply TcbMod.join_get_r; eauto.
  assert(TcbMod.get tcbls tid = Some(p, s)).
  eapply TcbMod.join_get_l; eauto.
  eapply H5; eauto.

  assert(TCBList_P (Vptr t_rdy) (vl'::x0) rtbl' (set x3 t_rdy (prio, st'))).
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin.
  inverts H12.
  unfolds in H6.
  rewrite H14 in H6.
  destruct (V_OSTCBNext vl'); tryfalse.
  do 4 eexists.
  splits; eauto.
  instantiate (1:=x5).
  clear - H15.
  eapply joinsig_set; eauto.

  destruct H6; substs.
  clear - H10 H15 H17 tcbls2_get_prio H4 H5.
  unfolds in H4; simpljoin.

  assert(x4 = ($ 1<<ᵢ(prio&ᵢ$ 7))).
  eapply math_mapval_core_prop; auto.
  clear - H H3.
  mauto.
  substs.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  eapply nth_val'_imp_nth_val_int; auto.
  assert(get x3 x1 = Some x6).
  clear - H15.
  join auto.
  unfold get in H2; simpl in H2.
  rewrite tcbls2_get_prio in H2; inverts H2.
  clear - H5 tcbls2_get_prio H15 H10.
  intros.
  unfolds in H5.
  assert(tid <> x1).
  intro; substs.
  pose proof H15 x1.
  rewrite TcbMod.get_sig_some in H0.
  rewrite H in H0; tryfalse.
  assert(TcbMod.get tcbls x1 = Some (prio, st)).
  eapply TcbMod.join_get_r; eauto.
  assert(TcbMod.get tcbls tid = Some(p, s)).
  eapply TcbMod.join_get_r; eauto.
  clear - H15 H.
  unfold TcbJoin in H15.
  unfold join, sig in H15; simpl in H15.
  eapply TcbMod.join_get_r; eauto.
  eapply H5; eauto.
  
  assert(join x2 (set x3 t_rdy (prio, st')) (set tcbls t_rdy (prio, st'))).
  clear - H10 tcbls2_get_prio.
  eapply join_set_r; eauto.
  unfold indom.
  eauto.
  
  eapply TCBList_P_Combine; eauto.
  eapply new_inv.tcbdllseg_split' in H7; eauto.
  do 5 destruct H7.
  destruct x0.
  unfold tcbdllseg in H7.
  simpl dllseg in H7.
  sep split in H7; tryfalse.

  sep auto; eauto.
Qed.

Lemma TCBList_P_tcblist_get_TCBNode_P :
  forall vltcb head rtbl tcbls tid vl abstcb,
    TCBList_P head vltcb rtbl tcbls ->
    tcblist_get (Vptr tid) head vltcb = Some vl ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBNode_P vl rtbl abstcb.
Proof.
  inductions vltcb; intros.
  simpl in H0; tryfalse.

  unfold tcblist_get in H0; fold tcblist_get in H0.
  unfold TCBList_P in H; fold TCBList_P in H; simpljoin.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  inverts H0.
  apply new_inv.beq_val_true_eq in eq1; inverts eq1.
  assert(TcbMod.get tcbls x = Some x2).
  eapply TcbMod.join_sig_get.
  unfold TcbJoin in H3.
  unfold join, sig in H3; simpl in H3.
  eauto.
  rewrite H1 in H; inverts H; auto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  inverts H2.
  eapply IHvltcb; eauto.

  clear - H3 H1 eq1.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H.
  destruct(TcbMod.get x1 tid);
    destruct(TcbMod.get tcbls tid); tryfalse.
  substs; auto.
  intro; substs.
  simpl in eq1.
  rewrite beq_addrval_true in eq1; tryfalse.
Qed.

Lemma set_node_elim_hoare : 
  forall spec sd linv inv r ri tid tcbls vltcb P s q head tail t_rdy vl vl' prio st st' rtbl rtbl',
    ptr_in_tcbdllseg (Vptr tid) head (set_node (Vptr t_rdy) vl' head vltcb) ->
    tcblist_get (Vptr t_rdy) head vltcb = Some vl ->
    TCBList_P head vltcb rtbl tcbls ->
    get tcbls t_rdy = Some (prio, st) -> (*prove this*)
    TCBNode_P vl' rtbl' (prio, st') -> (*prove this*)
    rtbl_set_one_bit rtbl rtbl' prio -> (*prove this*)
    R_Prio_No_Dup tcbls ->
    same_prev_next vl vl' ->
    
    {|spec, sd, linv, inv, r, ri|} |- tid
      {{EX (l1 l2 : list vallist) (tcb_cur:vallist) (tail1 : val) (tcbls1 tcbls2 : TcbMod.map),
      tcbdllseg head Vnull tail1 (Vptr tid) l1 **
      tcbdllseg (Vptr tid) tail1 tail Vnull (tcb_cur::l2) **
      [| (set_node (Vptr t_rdy) vl' head vltcb) = l1 ++ (tcb_cur :: l2)|] **
      [|TcbMod.join tcbls1 tcbls2 (TcbMod.set tcbls t_rdy (prio, st'))|] **
      [|TCBList_P head l1 rtbl' tcbls1|] **
      [|TCBList_P (Vptr tid) (tcb_cur :: l2) rtbl' tcbls2|] ** P
       }} s {{q}} ->
    {|spec, sd, linv, inv, r, ri|} |- tid {{tcbdllseg head Vnull tail Vnull (set_node (Vptr t_rdy) vl' head vltcb) ** P }} s {{q}}.
Proof.
  intros.
  eapply backward_rule1.
  intros.
  eapply set_node_elim; eauto.
  auto.
Qed.

Lemma R_Prio_No_Dup_tid_eq :
  forall tcbls prio tid tid' st st',
    R_Prio_No_Dup tcbls ->
    TcbMod.get tcbls tid = Some (prio, st) ->
    TcbMod.get tcbls tid' = Some (prio, st') ->
    st = st'.
Proof.
  intros.
  unfolds in H.
  destruct (tidspec.beq tid tid') eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  rewrite H1 in H0; inverts H0; auto.
  apply tidspec.beq_false_neq in eq1.
  lets Hx: H eq1 H0 H1; tryfalse.
Qed.

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 

Lemma prio_in_tbl_orself :
  forall prio v'37 vx,
    prio_in_tbl prio
                (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                                (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  intros.
  unfolds.
  intros.
  subst.
  apply nth_upd_eq in H1.
  inverts H1.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  rewrite Int.and_or_absorb.
  auto.
Qed.

Lemma TCBNode_P_set_rdy :
  forall next prev p_event st msg' msg1 dly stat stat' prio prio1 tcbx tcby tcbbitx tcbbity rtbl row y bitx,
    0 <= Int.unsigned prio < 64 ->
    nth_val (Z.to_nat (Int.unsigned (prio>>ᵢ$ 3))) rtbl = Some (Vint32 row) ->
    Int.unsigned row <= 255 ->
    stat' = Int.zero ->
    y = (prio >>ᵢ $ 3) ->
    bitx = ($ 1<<ᵢ(prio&ᵢ$ 7)) ->
    TCBNode_P
      (     next
              :: prev
              :: p_event
              :: msg1
              :: dly
              :: Vint32 stat
              :: prio1
              :: tcbx :: tcby :: tcbbitx :: tcbbity :: nil)
      rtbl (prio, st) ->
    TCBNode_P
      (    next
             :: prev
             :: Vnull
             :: msg'
             :: Vint32 Int.zero
             :: Vint32 stat'
             :: prio1
             :: tcbx :: tcby :: tcbbitx :: tcbbity :: nil)
      (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl
                      (Vint32 (Int.or row bitx)))
      (prio, rdy).
Proof.
  introv.
  do 4 intro.
  intros Hy Hbitx.
  rewrite Hy in *; clear Hy.
  rewrite Hbitx in *; clear Hbitx.
  intro.
  unfolds in H3.
  unfolds.
  simpljoin.
  splits; eauto.

  mttac RL_TCBblk_P ltac:(fun H => unfolds in H; simpljoin).
  unfolds.
  do 6 eexists.
  splits; eauto.
  unfolds; simpl; eauto.
  splits; eauto.
  unfold V_OSTCBEventPtr; simpl.
  eexists; splits; eauto.

  mttac V_OSTCBPrio ltac:(fun H => unfolds in H; simpl in H; inverts H).
  mttac R_TCB_Status_P ltac: (fun H => unfolds in H; simpljoin).
  unfolds; splits.
  
  clear - H2.
  unfolds; intros.
  unfolds in H.
  simpljoin.
  unfolds in H; simpl in H; inverts H.
  splits; try solve [unfolds; simpl; auto].
  eauto.

  unfolds; intros.
  match goal with H: (_, _) = (_, _) |- _ => inverts H end.
  splits; try solve [unfolds; simpl; auto].
  unfolds.
  splits; try solve [unfolds; simpl; auto].
  apply prio_in_tbl_orself ; auto.

  mttac RLH_TCB_Status_Wait_P ltac:(fun H => unfolds in H; simpljoin).
  (* rename H13 into Hpostq1. *)
  unfolds.
  unfolds.
  intros.
  mttac V_OSTCBStat ltac:(fun H => unfolds in H; simpl in H; inverts H).
  
  unfolds.
  try solve [unfolds; introv Hf; inverts Hf].
Qed.

Lemma tcblist_get_TCBList_P_get :
  forall vltcb tcbls head rtbl tid vl prio,
    tcblist_get (Vptr tid) head vltcb = Some vl ->
    V_OSTCBPrio vl = Some (Vint32 prio) ->
    TCBList_P head vltcb rtbl tcbls ->
    exists st, get tcbls tid = Some (prio, st).
Proof.
  inductions vltcb; intros.
  - 
    simpl in H; tryfalse.
  -
    unfold tcblist_get in H; fold tcblist_get in H.
    destruct (beq_val (Vptr tid) head) eqn : eq1.
    inverts H.
    unfold TCBList_P in H1; fold TCBList_P in H1.
    simpljoin.
    (* Require Import new_inv. *)
    apply beq_val_true_eq in eq1; inverts eq1.
    destruct x2.
    unfolds in H3; simpljoin.
    rewrite H0 in H; inverts H.
    join auto.

    destruct (V_OSTCBNext a) eqn: eq2; tryfalse.
    unfold TCBList_P in H1; fold TCBList_P in H1; simpljoin.
    rewrite eq2 in H2; inverts H2.
    lets Hx: IHvltcb H H0 H5.
    clear - H3 Hx.
    destruct Hx.
    exists x0.
    eapply join_get_r; eauto.
Qed.


(*
Lemma TCBList_P_tcblist_get_TCBNode_P :
  forall vltcb head rtbl tcbls tid vl abstcb,
    TCBList_P head vltcb rtbl tcbls ->
    tcblist_get (Vptr tid) head vltcb = Some vl ->
    TcbMod.get tcbls tid = Some abstcb ->
    TCBNode_P vl rtbl abstcb.
Proof.
  inductions vltcb; intros.
  simpl in H0; tryfalse.

  unfold tcblist_get in H0; fold tcblist_get in H0.
  unfold TCBList_P in H; fold TCBList_P in H; simpljoin.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  inverts H0.
  apply new_inv.beq_val_true_eq in eq1; inverts eq1.
  assert(TcbMod.get tcbls x = Some x2).
  eapply TcbMod.join_sig_get.
  unfold TcbJoin in H3.
  unfold join, sig in H3; simpl in H3.
  eauto.
  rewrite H1 in H; inverts H; auto.

  destruct (V_OSTCBNext a) eqn : eq2; tryfalse.
  inverts H2.
  eapply IHvltcb; eauto.

  clear - H3 H1 eq1.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H.
  destruct(TcbMod.get x1 tid);
    destruct(TcbMod.get tcbls tid); tryfalse.
  substs; auto.
  intro; substs.
  simpl in eq1.
  rewrite beq_addrval_true in eq1; tryfalse.
Qed.
*)


Lemma set_node_eq_dllflag :
  forall tcbl ptr  v'82 v'83 v'84 v'85 v'86 v'87 v'88 v'89 v'90 v'91 v'92 v'83' v'84' v'85' v'86' v'87' v'88' v'89' v'90' v'91' head,
    tcblist_get ptr head tcbl = 
      Some
        (v'82 :: v'83 :: v'84 :: v'85 :: v'86 :: v'87 :: v'88
           :: v'89 :: v'90 :: v'91 :: v'92 :: nil) ->
    eq_dllflag tcbl (set_node ptr (v'82 :: v'83' :: v'84' :: v'85' :: v'86' :: v'87' :: v'88'
                                     :: v'89' :: v'90' :: v'91' :: v'92 :: nil) head tcbl).
Proof.
  induction tcbl.
  intros.
  simpl.
  auto.
  intros.
  simpl.
  remember (beq_val ptr head).
  destruct b.
  unfold tcblist_get in H.
  rewrite <- Heqb in H.
  simpl in H.
  inverts H.
  splits; auto.
  Focus 2.
  splits; auto.
  eapply IHtcbl.
  unfolds in H.
  rewrite <- Heqb in H.
  destruct a.
  simpl in H.
  inversion H.
  simpl in H.
  fold tcblist_get in H.
  exact H.

  apply eq_dllflag_refl.
Qed.


Lemma eq_dllflag_trans :
  forall l1 l2 l3,
    eq_dllflag l1 l2 ->
    eq_dllflag l2 l3 ->
    eq_dllflag l1 l3.
Proof.
  induction l1.
  intros.
  simpl in H.
  destruct l2; tryfalse.

  simpl in H0.
  destruct l3; tryfalse.
  auto.
  intros.
  simpl in H.
  destruct l2; tryfalse.
  simpl in H0.
  destruct l3; tryfalse.
  simpl.
  simpljoin.
  splits.
  rewrite H.
  auto.
  rewrite H3.
  auto.
  eapply IHl1.
  eauto.
  eauto.
Qed.

