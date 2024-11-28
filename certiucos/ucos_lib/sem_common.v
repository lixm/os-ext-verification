Require Export sem_lab.
Require Export absop_rules.
Require Import Lia.

Import os_ucos_h.

Open Scope code_scope.

Lemma sem_H_get_none:
  forall els eid,
    EcbMod.get els eid = None ->
    ~(exists n wls, EcbMod.get els eid = Some (abssem n, wls)).
  intros.
  unfold not.
  intros.
  destruct H0.
  destruct H0.
  rewrite H in H0.
  tryfalse.
Qed.

Ltac mytac :=
  heat; jeauto2.
  
Lemma eventsearch_after_get_H:
  forall p ectrl1 a b ectrl2 msgqls1 msgq msgqls2 mqls tcbls  qid mqls1 mqls' mq mqls2,
    length ectrl1 = length msgqls1 ->
    ECBList_P p Vnull 
              (ectrl1 ++ ((a,b)::nil) ++ ectrl2)
              (msgqls1 ++ (msgq::nil) ++ msgqls2)
              mqls tcbls ->
    ECBList_P p (Vptr qid) ectrl1 msgqls1 mqls1 tcbls ->
    EcbMod.join mqls1 mqls' mqls ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    EcbMod.get mqls qid = Some mq.
  intros.
  apply ecblist_p_decompose in H0; auto.
  mytac.
  
  assert (x1 = Vptr qid /\ x = mqls1).
    eapply ecblist_p_eqh with (ecbls:=mqls); eauto.
    EcbMod.solve_map.
    EcbMod.solve_map.

  mytac.
  lets Hx:EcbMod.join_joinsig_get H2 H3.
  auto.
Qed.

Lemma semacc_eventtype_neq_sem:
  forall s P p ectrl1 a b ectrl2 msgqls1 msgq msgqls2 mqls tcbls  qid mqls1 mqls' mq mqls2 t,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    length ectrl1 = length msgqls1 ->
    ECBList_P p Vnull 
              (ectrl1 ++ ((a,b)::nil) ++ ectrl2)
              (msgqls1 ++ (msgq::nil) ++ msgqls2)
              mqls tcbls ->
    ECBList_P p (Vptr qid) ectrl1 msgqls1 mqls1 tcbls ->
    EcbMod.join mqls1 mqls' mqls ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    V_OSEventType a = Some (Vint32 t) ->
    Int.eq t ($ OS_EVENT_TYPE_SEM) = false ->
    s |= AEventData a msgq ** 
         [| ~ exists n wls, EcbMod.get mqls qid = Some (abssem n, wls)|] ** P.
  intros.
  assert (EcbMod.get mqls qid = Some mq).
    eapply eventsearch_after_get_H; eauto.
  
  unfold AEventData in *.
  destruct msgq eqn:Hmsgq.
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.
  
  sep split in H.
  rewrite H9 in H6.
  inverts H6.
  rewrite Int.eq_true in H7.
  tryfalse.
Qed. 

Lemma semacc_triangle_sem:
  forall s P a msgq mq n,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (V$OS_EVENT_TYPE_SEM) ->
    V_OSEventCnt a = Some (Vint32 n) ->
    s |= AEventData a msgq ** 
         [| exists wls, msgq = DSem n /\ mq = (abssem n, wls) |] ** P.
  intros.
  sep pauto.
  unfold AEventData in *.
  destruct msgq eqn:Hmsgq; sep split in H. 
  rewrite H1 in H3; tryfalse.

  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  rewrite H2 in H4. inverts H4.
  inverts H0.
  exists w.
  auto.
Qed. 

Lemma semacc_ltu_trans: 
  forall x y,
    Int.ltu Int.zero x = true ->
    Int.ltu x y = true ->
    Int.ltu (Int.sub x Int.one) y = true.
  int auto.
  int auto.
Qed.

Lemma semacc_compose_EcbList_P:
  forall p qid a b tcbls i n x2 x3 vn msgq mq ectrl1 msgqls1 mqls1 ectrl2 msgqls2 mqls2 mqls' mqls,
    R_ECB_ETbl_P qid (a,b) tcbls ->
    a = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 n :: x2 :: x3 :: vn :: nil) ->
    RLH_ECBData_P msgq mq ->
    ECBList_P p (Vptr qid) ectrl1 msgqls1 mqls1 tcbls ->
    ECBList_P vn Vnull ectrl2 msgqls2 mqls2 tcbls ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull (ectrl1 ++ ((a,b)::nil) ++ ectrl2) 
              (msgqls1 ++ (msgq::nil) ++ msgqls2)
              mqls tcbls.
  intros.
  subst.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.

(**************************** from post *****************************)

Lemma sem_eventtype_neq_sem:
   forall s P a msgq mq t,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (Vint32 t) ->
    Int.eq t ($ OS_EVENT_TYPE_SEM) = false ->
    s |= AEventData a msgq **
         [| (~ exists n wls, mq = (abssem n, wls)) |] ** P.
  intros.

  unfold AEventData in *.
  destruct msgq eqn:Hmsgq.
  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.
  
  sep split in H.
  rewrite H3 in H1.
  inverts H1.
  rewrite Int.eq_true in H2.
  tryfalse.
Qed. 

(* new copy form Mbox_common.v *)

Definition semcre_RL_Tbl_init_prop:
  RL_Tbl_Grp_P INIT_EVENT_TBL (Vint32 Int.zero).
Proof.
  unfolds.
  intros.
  splits.
  intros.
  inverts H1.
  split.
  simpl in H0.
  intros.
  destruct H.
  lets Hex : nat8_des H2 H0.
  auto.
  intros.
  rewrite Int.and_zero_l.
  auto.
  inverts H1.
  split.
  rewrite Int.and_zero_l.
  intros.
  apply leftmoven in H.
  unfold Int.zero in H1.
  tryfalse.
  simpl in H0.
  lets Hesx : nat8_des H H0.
  intros.
  unfold Int.zero in Hesx.
  int auto.
  remember (zlt 0 (Int.unsigned v)) as Hb.
  destruct Hb; 
  tryfalse.
  assert (Int.unsigned v = 0).
  subst v.
  apply unsigned_zero.
  lia.
Qed.

Notation INIT_EVENT_PTBL :=
  (Vint32 Int.zero
   :: Vint32 Int.zero
      :: Vint32 Int.zero
         :: Vint32 Int.zero
            :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil).

Lemma semcre_ECBList_P:
  forall mqls tcbls ct sid ecbls p l i v1,
    RH_TCBList_ECBList_P mqls tcbls ct ->
    get mqls sid = None ->
    ECBList_P p Vnull l ecbls mqls tcbls ->
    ECBList_P (Vptr sid) Vnull
      ((V$OS_EVENT_TYPE_SEM
          :: Vint32 Int.zero :: Vint32 i :: Vnull :: v1 :: p :: nil,
         INIT_EVENT_TBL) :: l) (DSem i :: ecbls)
      (set mqls sid (abssem i, nil))
      tcbls.
Proof.
  intros.
  unfolds.
  fold ECBList_P.
  eexists.
  split; eauto.
  split.
  unfolds.
  split.
  unfolds.
  unfolds in H.
  unfolds.
  intros.

  unfolds in H2.
  mytac.
  simpl in H6.
  lets Hres : prio_prop H2 H8; eauto.
  assert (∘(Int.unsigned (Int.shru ($ prio) ($ 3))) < 8)%nat.
  {
    eapply Z_le_nat; eauto.
    split; auto.
    apply Int.unsigned_range_2.
  }
  remember (∘(Int.unsigned (Int.shru ($ prio) ($ 3)))) as  Heq.
  assert (x1=Int.zero) by (eapply nat8_des;eauto).
  subst x1.
  apply int_land_zero in H7; tryfalse.

  splits.
  unfolds.
  unfolds. 
  intros.
  match goal with
    H: context[RH_TCBList_ECBList_P] |- _ => unfolds in H; destruct H as (Hab & Hac)
  end.
  lets Hre : Hac H2. 
  destruct Hre as (xx & wt & Hec & Hin).
  change ((fun x => x = None) (get mqls sid)) in H0.
  rewrite Hec in H0.
  tryfalse.

  unfolds.
  simpl; auto. 
  
  do 3 eexists.
  unfold V_OSEventListPtr.
  simpl nth_val .
  splits; eauto.
  instantiate (1:= (abssem i, nil)).
  eapply ecbmod_get_sig_set; eauto.
  unfolds.
  splits.
  auto.
  unfolds.
  split; intros; [reflexivity | tryfalse].
Qed.

Ltac tryfalse' :=
  repeat match goal with
           | H1: get ?x ?t = None, H2: get ?x ?t = Some _ |- _ =>
             change ((fun y => y = None) (get x t)) in H1;
             rewrite H2 in H1
           | H1: get ?x ?t = Some ?v1, H2: get ?x ?t = Some ?v2 |- _ =>
             change ((fun y => y = Some v1) (get x t)) in H1;
             rewrite H2 in H1
         end;
  tryfalse.

(* new copy form OSTimeDlyPure.v *)

Lemma semcre_RH_TCBList_ECBList_P:
  forall v'37 x i v'38 v'40,
    get v'37 x = None ->
    RH_TCBList_ECBList_P v'37 v'38 v'40 ->
    RH_TCBList_ECBList_P
      (set v'37 x (abssem i, nil))
      v'38 v'40.
Proof.
  intros.
  unfolds.
  unfolds in H0.
  rename H0 into Ha2. 

  destruct Ha2.
  unfolds.
  split.
  intros.
  rewrite set_sem in H2.
  destruct (dec x eid).
  destruct H2.
  inverts H2.
  simpl in H3; tryfalse.
  eapply H0; eauto.
  intros.
  rewrite set_sem.
  lets Hres : H1 H2.
  destruct Hres as (n & wls & Hec & Hin).
  remember (dec x eid) as Hbool.
  destruct Hbool.
  apply eq_sym in HeqHbool.
  subst x.
  tryfalse'.
  do 2 eexists; splits; eauto.
Qed. 

(** move to join_lib **)
Lemma map_join_get_none':
  forall (A B T : Type) (PermMap : PermMap A B T) 
    (x y z : T) (t : A) v,
    join x y z ->
    get x t = None ->
    get y t = v ->
    get z t = v.
  intros.
  assert (get z t = get y t) by jeauto2.
  subst.
  auto.
Qed.

Lemma semcre_ecblist_star_not_inh :
  forall v'28 v'24  eid  v'27 v'37 v'38 s vl P,
    ECBList_P v'24 Vnull v'28 v'27 v'37 v'38 ->
    s |= Astruct eid OS_EVENT vl ** evsllseg v'24 Vnull v'28 v'27 ** P -> 
    get v'37 eid = None.
Proof.
  inductions v'28;intros.
  - 
    simpl in H; mytac.
  -
  unfold ECBList_P in H.
  fold ECBList_P in H.
  mytac.
  destruct v'27.
  tryfalse.
  destruct a.
  mytac.
  unfold evsllseg in H0.
  fold evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  sep lower 2%nat in H0. 
  sep lower 3%nat in H0.
  sep lower 1%nat in H0.
  lets Hrs : IHv'28 H4 H0.
  unfold AEventNode in H0.
  unfold AOSEvent in H0.
  unfold node in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  mytac.
  inverts H5.
  sep lift 3%nat in H0.
  lets Hs : astruct_neq_ptr H0.
  intro Hf.
  unfolds in Hf.
  destruct Hf as [Hx | Hf].
  mytac.
  tryfalse.
  destruct Hf.
  mytac.
  tryfalse.
  tryfalse.
  intro Hf.
  unfolds in Hf.
  destruct Hf as [Hx | Hf].
  mytac.
  tryfalse.
  destruct Hf.
  mytac.
  tryfalse.
  tryfalse.
  unfold TcbJoin in H2.
  eapply map_join_get_none'; jeauto2.
Qed.  
  
Lemma sempend_ltu_ass1:
  forall x, Int.ltu x x = false.
  int auto.
Qed.

Lemma sempend_ltu_ass2:
  Int.ltu Int.zero Int.one = true.
  int auto.
Qed.

Lemma join_prop2_my':
  forall m1 m2 m12 b1 prio st m3 ma3 m4,
    join m1 m2 m12 ->
    TcbJoin (b1, Int.zero) (prio, st) m3 ma3 ->
    join m4 ma3 m2 ->
    join m1 (set m2 (b1, Int.zero) (prio, rdy)) (set m12 (b1, Int.zero) (prio, rdy)).
Proof.
  unfold TcbJoin.
  intros.
  eapply my_join_sig_abc.
  unfold usePerm; simpl; auto.
  eapply H1.
  trivial.
  unfold joinsig.
  eapply H0.
Qed.

Lemma statsem_and_not_statsem_eq_rdy :
  Int.eq ($ OS_STAT_SEM&ᵢInt.not ($ OS_STAT_SEM)) ($ OS_STAT_RDY) = true.
Proof.
  unfold OS_STAT_SEM, OS_STAT_RDY.
  unfold Int.not.
  unfold Int.xor.
  unfold Z.lxor.
  int auto.
  compute.
  split; intros; tryfalse.
  int auto.
  compute.
  intro; tryfalse.
  compute.
  intro; tryfalse.
  compute.
  split; intros; tryfalse.
Qed.
