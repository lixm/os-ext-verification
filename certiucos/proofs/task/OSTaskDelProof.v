
Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import new_inv.
Require Import task_pure.
Require Import protect.
Require Import Lia.

Require Import seplog_pattern_tacs. 

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Set Nested Proofs Allowed.

Local Ltac sifs := 
  match goal with
    | |- context[if ?e then _ else _] => destruct e; sifs
    | |- _ <> _ => try solve [simpl; intro; tryfalse]
    | _ => idtac
  end.


Lemma absimp_taskdel_prio_invalid:
  forall P v3 sch,
    can_change_aop P ->
    Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true ->
    (* Int.eq (Int.repr OS_PRIO_SELF) v3 = false -> *)
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absimp_taskdel_prio_is_idle:
  forall P v3 sch,
    can_change_aop P ->
    Int.eq (Int.repr OS_IDLE_PRIO) v3 = true ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.


Lemma absimp_taskdel_prio_no_such_tcb:
  forall P v3 sch mqls tls t ct,
    can_change_aop P ->
    (~ exists tid st, TcbMod.get tls tid= Some (v3, st)) ->
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
                     ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) ||>
          ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
Proof.
  infer_solver 1%nat.
Qed.

Lemma hl_get_ecb_can_split_ecblist:
  forall l hd tl ecbls hecbls tcbls tid he ,
    EcbMod.get hecbls tid = Some he ->
    ECBList_P hd tl l ecbls hecbls tcbls ->
    exists l1 l2 pt pt2 ecbls1 ecbls2 hecbls1 hecbls2, 
      join hecbls1 hecbls2 hecbls /\
      l = l1 ++ (pt :: l2) /\
      ecbls = ecbls1 ++ (pt2 :: ecbls2) /\
      ECBList_P hd (Vptr tid) l1 ecbls1 hecbls1 tcbls /\ 
      ECBList_P (Vptr tid) tl (pt::l2) (pt2::ecbls2) hecbls2 tcbls.
Proof.
  induction l.
  intros.
  simpl in H0.
  simpljoin.
  false.
  intros.
  unfold1 ECBList_P in H0.
  simpljoin.
  destruct ecbls.
  tryfalse.
  destruct a.
  simpljoin.
  unfold TcbJoin in H2.
  assert (get (sig x x0) tid = Some he \/ get x1 tid = Some he).
  unfold get,sig,join in *; simpl in *.
  eapply  EcbMod.join_get_or.
  exact H2.
  auto.
  destruct H5.
  Focus 2.
  lets bb: IHl H5 H4.
  repeat destruct bb.
  repeat destruct H6.
  exists ( (v,v0) :: x3).
  exists x4.
  exists x5.
  exists x6.
  exists (e::x7).
  exists x8.
  assert (exists bb, join (sig x x0) x9 bb).
  eexists.
  join auto.
  destruct H8.
  exists x11.
  exists x10.
  splits.
  join auto.
  simpl.
  simpljoin.
  simpljoin.
  auto.
  unfold1 ECBList_P.
  simpljoin.
  repeat tri_exists_and_solver1.
  simpljoin; auto.
  cut ( x = tid).
  intro.
  exists (@nil (os_inv.EventCtr)).
  exists l.
  exists (v, v0).
  exists e.
  exists (@nil EventData).
  exists ecbls.
  do 2 eexists.
  splits.
  2:eauto.
  2:eauto.
  2:simpl.
  2:splits; auto.
  instantiate (1:= hecbls).
  join auto.
  Focus 2.
  unfold1 ECBList_P.
  repeat tri_exists_and_solver1.
  subst; auto.
  subst; auto.
  subst; auto.
  
  unfold get,sig,join in *; simpl in *.
  assert (x = tid \/ x <> tid) by tauto.
  destruct H6; auto.
  rewrite EcbMod.get_a_sig_a' in H5.
  inversion H5.
  go.
Qed.

Lemma evsllseg_split:
  forall l1 l1' l2 l2' hd tl  P,
    length l1 = length l1' ->
    evsllseg hd tl (l1 ++ l2) (l1' ++ l2')  ** P ==>
             EX pp, evsllseg hd pp l1 l1' ** evsllseg pp tl l2 l2' ** P.
Proof.
  induction l1.
  intros.
  simpl in H.
  destruct l1'; tryfalse.
  unfold evsllseg at 1.
  sep pauto.
  intros.
  destruct l1'; tryfalse.
  unfold1 evsllseg.
  destruct a.
  sep normal .
  change ( (((v, v0) ::l1 ) ++ l2) ) with ( (v,v0) :: l1++l2) in H0.
  change ( ((e ::l1' ) ++ l2') ) with ( e :: l1'++l2') in H0.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep lift 3%nat in H0.
  simpl in H.
  assert (length l1 = length l1') by lia.
  lets bbb: IHl1 H1 H0.
  sep destruct bbb.
  clear H0.
  sep pauto.
Qed.

Lemma ecblistp_evsllseg_tlsame:
  forall ls1 hd tl tl' ls2 hls tcbls P s,
       ECBList_P hd tl ls1 ls2 hls tcbls ->
       s |= evsllseg hd tl' ls1 ls2 ** P ->
       tl  = tl'.
Proof.
  induction ls1.
  intros.
  simpl in H.
  simpljoin.
  unfold evsllseg in H0.
  sep split in H0.
  tauto.
  intros.
  unfold1 ECBList_P in H.
  simpljoin.
  destruct ls2; tryfalse.
  destruct a; simpljoin.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H5.
  inverts H5.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
Qed.

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 
 
Lemma OSTCBflag_des:
  forall v'11,
    struct_type_vallist_match OS_TCB_flag v'11 ->
    exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10,
    exists a11,
      v'11 = (a1::a2::a3::a4::a5::a6::Vint32 a7::a8::a9::a10::a11::nil).
Proof.
  intros.
  destruct v'11; simpl in H; tryfalse.
  destruct v'11; simpl in H; simpljoin; tryfalse.
  destruct v'11; simpl in H; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v5; tryfalse.
  repeat tri_exists_and_solver1.
Qed.
  
Theorem TaskDeleteProof:
  forall  vl p r tid, 
    Some p =
    BuildPreA' os_api OSTaskDel taskdelapi vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api OSTaskDel taskdelapi vl  OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OSTaskDel = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  destruct v'.
  2: { hoare_lifts_trms_pre Aop. apply absabort_rule. }
  
  hoare unfold.
  hoare forward.
  math simpls.
  sifs.
  
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_is_idle.
  go.
  (* left. *)
  change OS_IDLE_PRIO with 63 in *.
  int auto.
  hoare forward.
  hoare forward.
  hoare unfold.
  assert (v': val) by trivial.
  hoare forward.
  math simpls.
  sifs.
  math simpls.
  sifs.
  sifs.
  (* math simpls.
   * sifs.
   * sifs.
   * sifs. *)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_prio_invalid.
  go.
  change OS_LOWEST_PRIO with 63 in *.
  change OS_IDLE_PRIO with 63 in *.
  change OS_PRIO_SELF with 255 in *.
  int auto.
  destruct H.
  inversion H.
  inversion H.
  hoare forward.
  (* change OS_LOWEST_PRIO with 63 in *.
   * change OS_IDLE_PRIO with 63 in *.
   * change OS_PRIO_SELF with 255 in *.
   * int auto.
   * false.
   * apply H0.
   * simpl.
   * change  (Int.ltu Int.zero Int.zero) with false.
   * change  (Int.ltu Int.zero Int.one) with true.
   * simpl.
   * change  (Int.ltu Int.zero Int.one) with true.
   * change  (Int.ltu Int.zero (Int.notbool Int.one)) with false.
   * simpl.
   * auto.
   * hoare forward. *)

  hoare forward.
  hoare unfold.
  hoare forward prim.
  hoare unfold.
  unfold AOSTCBList.
  hoare normal pre.
  hoare_split_pure_all.
  unfold1 tcbdllseg.
  unfold1 dllseg.
  unfold node.
  hoare normal pre.
  hoare_split_pure_all.
  simpljoin.
  inverts H12.
(* ** ac:   Check OSTCBflag_des. *)
                               
  lets bb: OSTCBflag_des H16.
  simpljoin.
                              
  hoare unfold.
  assert (Int.unsigned i < 64).
  {
    clear -H0.
    change OS_LOWEST_PRIO with 63 in *.
    int auto.
    destruct H0;
      tryfalse.
  }
  assert (Int.unsigned i <> 63).
  {
    clear -H.
    change OS_IDLE_PRIO with 63 in *.
    destruct H; int auto.
  }
  clear H H0.
  rename H13 into H.
  rename H14 into H0.
  

  unfold  OS_LOWEST_PRIO in *.
  assert ( rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned i)) v'6) = true).
  {
    eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
    rewrite H7.
    clear -H.
    mauto.
    auto.
  }

  hoare forward.
  math simpls.
  assumption.
  
  assert (exists t , TcbMod.get v'15 ((v'29, Int.zero)) = Some (x5, t)).
  {
    unfold1 TCBList_P in H11.
    simpljoin.
    unfolds in H18.
    destruct x11. 
    simpljoin.
    mttac V_OSTCBPrio ltac:(fun H=> inverts H).
    mttac R_TCB_Status_P ltac:(fun H=> unfolds in H; simpl in H).
    inverts H11.
    unfold join,sig,get in *; simpl in *.
    unfold join,sig,get in *; simpl in *.
    eexists.
    go.
  }
  destruct H14 as (hello & kitty).
  protect kitty.
 
  hoare forward.
  
  (* hoare forward. *)
  (* unfolds in H14. *)
  (* clear -H14. *)
  destruct ( nth_val' (Z.to_nat (Int.unsigned i)) v'6 ); tryfalse.
  intro; tryfalse.
  intro; tryfalse.
  unfold val_eq in H17.
  destruct a; tryfalse.
  
  hoare unfold.
  hoare abscsq.

  apply noabs_oslinv.
  eapply absimp_taskdel_prio_no_such_tcb.
  go.
  {
    intro.
    apply H14.
    destruct H13.
    2: { 
      simpljoin.
      rewrite H13.
      simpl.
      destruct x10.
      reflexivity.
    }
    false.
    simpljoin.
    unfolds in H6.
    simpljoin.
    lets bb: H20 H19.
    simpljoin.
    unfold nat_of_Z in H22.
    apply nv'2nv in H13.
    rewrite H13 in H22.
    inverts H22.
    intro; tryfalse.
  }

  hoare forward prim.
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel 4%nat 1%nat.
  
  unfold tcbdllseg.
  unfold1 dllseg.
  sep pauto.
  unfold node.
  sep pauto.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat .
  sep cancel 2%nat 1%nat.
  sep cancel AOBJ.
  sep cancel 2%nat 1%nat.
  sep cancel p_local.
  eauto.
  go.
  go.
  go.
  go.
  go.
  go.
  go.
  hoare forward.

  (* ptcb ′ .. OSTCBDly =ₑ ′ 0;ₛ *) 
  hoare forward.
  hoare_split_pure_all.

  (* hoare forward. *)
  unfold os_task.PlaceHolder.
  hoare unfold.
  assert (exists p, (nth_val' (Z.to_nat (Int.unsigned i)) v'6) = Vptr p).
  {
    clear -H13 H14.
    destruct H14.
    unfolds in H13.
    
    destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'6); tryfalse.
    destruct H13; tryfalse.
    assumption.
    destruct (nth_val' (Z.to_nat (Int.unsigned i)) v'6); tryfalse.
    destruct a; simpl in H.
    tryfalse.
  }
  clear H13 H14.
  simpljoin.
  rewrite H13.
  
  eapply seq_rule.
  {
    eapply ift_rule''.
    intro.
    intros.
    eapply symbolic_lemmas.bop_rv.
    sep_get_rv.
    eapply symbolic_lemmas.addrof_gvar_rv.
    gen_notin_lenv H14 OSPlaceHolder.
    eapply symbolic_lemmas.dom_lenv_imp_notin_lenv.
    eauto.
    sep cancel A_dom_lenv.
    sep cancel Agvarenv'.
    eauto.
    eauto.
    simpl.
    destruct x; destruct v'17.
    destruct ( Int.eq i0 i1 ); destruct (peq b b0); simpl; intro; tryfalse.
    simpl.
    eauto.
    hoare unfold.
    instantiate (1:=Afalse).
    hoare abscsq.
    apply noabs_oslinv.
    eapply   absimp_taskdel_prio_no_such_tcb.
    go.
    {
      intro.
      apply H14.
      assert (x <> v'17 \/ x = v'17) by tauto.
      destruct H20.
      simpl.
      destruct x; destruct v'17.
      remember (peq b b0).
      destruct s.
      subst.
(* ** ac:       SearchAbout (Int.eq ). *)
      rewrite Int.eq_false.
      reflexivity.
      intro; tryfalse.
      reflexivity.
      subst x.
      simpl.
      false.
      simpljoin.
      unfolds in H6.
      simpljoin.
      lets bb: H20 H19.
      simpljoin.
      unfold nat_of_Z in H22.
      apply nv'2nv in H13.
      rewrite H13 in H22.
      inverts H22.
      apply H23; reflexivity.
      intro; tryfalse.
    }
    hoare forward prim.
    unfold AOSTCBPrioTbl.
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllflag.
    sep cancel 4%nat 1%nat.
    sep cancel AOBJ.
    
    unfold tcbdllseg.
    unfold1 dllseg.
    unfold node.
    sep pauto.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat .
    sep cancel 2%nat 1%nat.
    eauto.
    go.
    go.
    go.
    go.
    go.
    go.
    go.
    hoare forward.
  }

  (********)
  hoare forward.
  (* rename H20 into some_pure_hyp. *)

  (* hoare forward. *)
  (* change (Int.eq ($ 0) ($ 1)) with false. *)
  (* (* simpl; intro;tryfalse. *) *)
  (* hoare unfold. *)
  (* false. *)
  (* clear -H14. *)
  (* int auto. *)
  (* instantiate (1:=Afalse). *)
  (* hoare forward. *)
  (* hoare unfold. *)
  (* clear H18. *)

  (**********************)
  
  Lemma valinjbopevallemma:
    forall x v'19, val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
        Vint32 Int.zero \/
        val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
        Vnull -> x <> v'19.
  Proof.
    intros.
    destruct H.
    simpl in H.
    destruct x; destruct v'19.
    intro.
    inverts H0.
    rewrite peq_true in H.
    rewrite Int.eq_true in H.
    inverts H.
    simpl in H.
    destruct x; destruct v'19.
    destruct (peq b b0); destruct (Int.eq i i0); tryfalse.
  Qed.

  hoare unfold.
  apply valinjbopevallemma in H14.
  unfold AOSTCBList.
  hoare unfold.
  (* change (dllseg v'26 (Vptr (v'27, Int.zero)) v'23 Vnull v'13 OS_TCB_flag
   *                (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ) with (tcbdllseg v'26 (Vptr (v'27, Int.zero)) v'23 Vnull v'13).
   * change (dllseg v'9 Vnull v'22 (Vptr (v'27, Int.zero)) v'11 OS_TCB_flag
   *                (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ) with (tcbdllseg v'9 Vnull v'22 (Vptr (v'27, Int.zero)) v'11). *)
  rename v'17 into vhold.
  rename v'29 into cur_tcb_blk.
  rename v'15 into tcbmap.
  rename v'6 into priotbl.
  rename x into todelptr.
  assert (exists st, TcbMod.get tcbmap todelptr = Some (i, st)).
  {
    unfolds in H6.
    simpljoin.
    apply H6.
    splits.
    clear; int auto.
    lia.
    unfold nat_of_Z.
    eapply nv'2nv.
    assumption.
    intro; tryfalse.
    assumption.
  }
  simpljoin.
  rename v'11 into l2.
  rename v'9 into l1.
  remember  (v'28
         :: v'24
            :: x1
               :: x2 :: x3 :: x4 :: Vint32 x5 :: x6 :: x7 :: x8 :: x9 :: nil) as tcbcur.
  protect Heqtcbcur.

  eapply backward_rule1.
  intro.
  intros.
  Set Printing Depth 999.
(* ** ac:   Show. *)

  instantiate (1 := (
                     [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'7 (l1++ tcbcur::l2)|] **
                       tcbdllseg v'7 Vnull v'25 Vnull (l1++tcbcur::l2) **
                       [|TCBList_P v'7 (l1++tcbcur::l2) v'12 tcbmap|] **
                       <|| taskdelcode (Vint32 i :: nil) ||>  **
                       GV OSTCBList @ OS_TCB ∗ |-> v'7 **
           (* tcbdllseg v'9 Vnull v'10 (Vptr (cur_tcb_blk, Int.zero)) l1 ** *)
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           (* tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'10 v'12 Vnull
            *   (tcbcur :: l2) ** *)
           Aie false **
           Ais nil **
           Acs (true :: nil) **
           Aisr empisr **
           AECBList v'5 v'4 v'14 tcbmap **
           tcbdllflag v'7 (l1 ++ tcbcur :: l2) **
           AOSRdyTblGrp v'12 v'13 **
           AOSTCBPrioTbl priotbl v'12 tcbmap vhold **
           AOBJ v'21 v'22 v'14 vhold v'7 (l1 ++ tcbcur :: l2) v'20 v'3 **
           HECBList v'14 **
           HTCBList tcbmap **
           HCurTCB (cur_tcb_blk, Int.zero) **
           A_isr_is_prop **
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           LV ptcb @ OS_TCB ∗ |-> Vptr todelptr **
           AOSEventFreeList v'20 v'3 **
           (* AOSQFreeList v'4 ** *)
           (* AOSQFreeBlk v'5 ** *)
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           AOSTCBFreeList v'18 v'19 **
           AOSTime (Vint32 v'16) **
           HTime v'16 **
           AGVars **
           atoy_inv' **
           LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
           LV ptr @ OS_EVENT ∗ |-> v'0 **
           LV prio @ Int8u |-> Vint32 i **
           A_dom_lenv
             ((prio, char_t)
              :: (ptr, OS_EVENT ∗)
                 :: (ptcb, OS_TCB ∗)
                    :: (os_code_defs.x, OS_TCB ∗) :: nil)
                   )). 
  eapply tcbdllseg_combine.
  sep pauto.
  sep cancel Aop.
  unfold tcbdllseg at 1.
  sep cancel 3%nat 1%nat.
  unfold tcbdllseg at 1.
  unfold dllseg; fold dllseg.
  sep pauto.
  sep cancel dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct.
  sep cancel tcbdllflag.

  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  unfold AOSTCBPrioTbl.
  sep pauto.
  {
    unprotect Heqtcbcur; subst tcbcur; go.
  }
  {
    unprotect Heqtcbcur; subst tcbcur; go.
  }
  eauto.
  eauto.
  auto.

  hoare_split_pure_all.
  assert (ptr_in_tcbdllseg (Vptr todelptr) v'7 (l1++tcbcur ::l2)).
  Lemma tcbget_ptr_in_tcblist:
     forall tcblst head rtbl tcbmap x xx,
      TCBList_P head tcblst rtbl tcbmap ->
      get tcbmap x = Some xx ->
      ptr_in_tcbdllseg (Vptr x) head tcblst.
  Proof.
    induction tcblst.
    intros.
    simpl in H.
    subst tcbmap.
(* ** ac:     SearchAbout (get empenv _ = _). *)
    rewrite map_emp_get in H0.
    inverts H0.
    intros.
    unfold1 ptr_in_tcbdllseg.
    remember (beq_val (Vptr x) head).
    destruct b.
    auto.
    unfold1 TCBList_P in H.
    simpljoin.
    rewrite H1.
    eapply IHtcblst.
    exact H4.
    assert ( x <> x0).
    intro.
    subst x0.
(* ** ac:     SearchAbout beq_val. *)
    rewrite beq_val_true in Heqb.
    tryfalse.
    unfold join,get,sig in *; simpl in *.
    eapply TcbMod.join_get_or in H2.
    destruct H2; eauto.
    rewrite TcbMod.get_a_sig_a' in H2.
    inverts H2.
    go.
    eauto.
  Qed.

  eapply tcbget_ptr_in_tcblist.
  eauto.
  eauto.
  
  eapply backward_rule1.
  intro.
  intros.
  get_hsat Hs.
  eapply tcbdllseg_split' in Hs.
  eauto.
  { (* ptr_in_tcbdllseg ... *)
    exact H20.
  }
  eauto.
  clear Heqtcbcur.
  remember (l1  ++ tcbcur :: l2) as tcblst.
  protect Heqtcblst.
  hoare unfold.
  clear dependent v'26.
  clear dependent v'27.
  (*v*)
  destruct v'8.
  simpl.
  unfold tcbdllseg.
  simpl.
  hoare unfold.
  inverts H9.

  unfold tcbdllseg.
  unfold1 dllseg .
  unfold node.
  hoare_split_pure_all.
  simpljoin .
  inverts H9.
  rename v'17 into todelblock.
  hoare unfold.
  hoare forward.
  (* intro; tryfalse. *)
  go.
  {
    clear -H9.
    destruct H9; subst; simpl; intro; tryfalse.
    simpljoin; subst; tryfalse.
    simpl in H0.
    destruct x; tryfalse.
  }
  hoare unfold.

  
  Lemma absimp_taskdel_prio_HAS_NO_NEXT:
    forall P v3 sch mqls tls t ct,
      can_change_aop P ->
      absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||>
                       ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
        ( <|| END (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) ||>
            ** HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P) .
  Proof.
    infer_solver 3%nat.
  Qed.

  hoare abscsq.
  apply noabs_oslinv.
  {
    apply absimp_taskdel_prio_HAS_NO_NEXT.
    go.
  }
  remember
    (v'15
       :: v'9
       :: x21
       :: x20
       :: Vint32 i13
       :: Vint32 i12
       :: Vint32 i11
       :: Vint32 i10
       :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: nil) 
    as todelblk.
  rename v'8 into l2'.
  rename v'6 into l1'.
  eapply backward_rule1.
  intro.
  intros.
  Set Printing Depth 999.
  (* ** ac:   Show. *)
  instantiate (1:= (
                     [|ptr_in_tcbdllseg (Vptr (todelblock, Int.zero)) v'7 (l1'++ todelblk::l2')|] **
                    tcbdllseg v'7 Vnull v'25 Vnull (l1'++todelblk::l2') **
                    [|TCBList_P v'7 (l1'++todelblk::l2') v'12 tcbmap|] **
                    <|| END Some (V$ OS_TASK_DEL_HAS_NO_NEXT) ||> **
           HECBList v'14 **
           HTCBList tcbmap **
           HTime v'16 **
           HCurTCB (cur_tcb_blk, Int.zero) **
           (* Astruct (todelblock, Int.zero) OS_TCB_flag todelblk ** *)
           (* dllseg v'28 (Vptr (todelblock, Int.zero)) v'12 Vnull l2'
            *   OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
            *   (fun vl : vallist => nth_val 0 vl) **
            * dllseg v'9 Vnull v'13 (Vptr (todelblock, Int.zero)) l1'
            *   OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
            *   (fun vl : vallist => nth_val 0 vl) ** *)
           GV OSTCBList @ OS_TCB ∗ |-> v'7 **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           Aie false **
           Ais nil **
           Acs (true :: nil) **
           Aisr empisr **
           AECBList v'5 v'4 v'14 tcbmap **
           tcbdllflag v'7 (l1' ++ todelblk :: l2') **
           AOSRdyTblGrp v'12 v'13 **
           AOSTCBPrioTbl priotbl v'12 tcbmap vhold **
           AOBJ v'21 v'22 v'14 vhold v'7 (l1' ++ todelblk :: l2') v'20 v'3 **
           A_isr_is_prop **
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           (* LV self @ Int8u |-> (V$ 0) ** *) 
           LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           AOSEventFreeList v'20 v'3 **
           (* AOSQFreeList v'4 ** *)
           (* AOSQFreeBlk v'5 ** *)
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           AOSTCBFreeList v'18 v'19 **
           AOSTime (Vint32 v'16) **
           AGVars **
           atoy_inv' **
           LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
           LV ptr @ OS_EVENT ∗ |-> v'0 **
           LV prio @ Int8u |-> Vint32 i **
           A_dom_lenv
           ((prio, Int8u)
              :: (ptr, OS_EVENT ∗)
              :: (ptcb, OS_TCB ∗)
              :: (os_code_defs.x, OS_TCB ∗) :: nil)
              )).

  eapply tcbdllseg_combine.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel Aop.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  go.
  go.
  go.
  go.
  hoare_split_pure_all.
  unprotect Heqtcblst.
  instantiate (1:=Afalse).
  eapply backward_rule1.
  intros.
  get_hsat Hs.
  eapply tcbdllseg_split' in Hs.
  eauto.
  { (* ptr_in_tcbdllseg ... *)
    exact H18.
  }
  eauto.
  hoare unfold.
  destruct v'8.
  unfold tcbdllseg; unfold dllseg.
  hoare_split_pure_all.
  inverts H53.
  rewrite H49.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold AOSTCBList.
  sep pauto.

  go.
  go.
  go.
  go.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  assert (exists n, v'15 = Vptr n).
  {
    clear -H9 H10.
    destruct H10; simpljoin; destruct H9; simpljoin; subst; simpl in *; tryfalse.
    eauto.
    eauto.
  } 
  clear H9 H10.
  simpljoin.
  rename v'6 into l1'.
  rename v'8 into l2'.
  
  lets backup: H24.
  unfold1 TCBList_P in H24.
  simpljoin.
  inverts H9.
  inverts H10.
  unfolds in H24. 
  destruct x13.
  simpljoin.
  mttac V_OSTCBPrio ltac: (fun H => inverts H).
  assert ((p, t) = (i, x)).
  {
    clear -H11 H17 H22.
    assert (get tcbmap (todelblock, Int.zero) = Some  (p, t)).
    {
      unfold get,sig, join in *; simpl in *.
      unfold get,sig, join in *; simpl in *.
      go.
    }
    unfold get,sig, join in *; simpl in *.
    unfold get,sig, join in *; simpl in *.
    rewrite H in H17.
    inverts H17.
    reflexivity.
  }
  inverts H9.
  unfolds in H10.
  simpljoin.
  mttac V_OSTCBPrio ltac: (fun H => inverts H); 
  mttac V_OSTCBStat ltac: (fun H => inverts H); 
  mttac V_OSTCBEventPtr ltac: (fun H => inverts H); 
  mttac V_OSTCBY ltac: (fun H => inverts H); 
  mttac V_OSTCBBitX ltac: (fun H => inverts H); 
  mttac V_OSTCBX ltac: (fun H => inverts H); 
  mttac V_OSTCBBitY ltac: (fun H => inverts H).
  (* inverts H20; inverts H56; inverts H63; inverts H30. *)
  (* inverts H54; inverts H21; inverts H55. *)

  change ((OSRdyTbl ′ [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
                  If(OSRdyTbl ′ [ptcb ′ → OSTCBY] ==ₑ ′ 0)
                  { OSRdyGrp ′ &= ∼ ptcb ′ → OSTCBBitY }  )) with
    (inline_call inline_bittbl_clearbit ((OSRdyGrp ′) :: (OSRdyTbl ′) :: 
      (ptcb ′ → OSTCBBitX) :: (ptcb ′ → OSTCBBitY) :: (ptcb ′ → OSTCBY) :: nil)). 
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold GAarray.
  unfold AOSRdyGrp.
  unfold Agvarmapsto at 3.
  hoare unfold.

  Ltac inline_forward :=
    match goal with
    | |- {| _ , _ , _, _, _, _|} |- _ {{ _ }} inline_call ?inline_record _ {{ _ }} =>
        eapply backward_rule2;
        [eapply (inl_proof inline_record)  |
          intro;intros;inline_pre_unfolder inline_record | idtac..] 
    end.
  eapply seq_rule.

  inline_forward.
  2: { 
    sep pauto.
    sep cancel Aop.
    sep cancel 4%nat 2%nat.
    sep cancel 2%nat 1%nat.
    eauto.
    (* unfold AOSRdyGrp in H56.
     * sep normal in H56.
     * sep lift 21%nat in H56. *)
    instantiate (1 := x10).
    lia.
    go.
    math simpls.
    go.
    go.
    clear -H.
    mauto.

    2:go.

    
    intro.
    intros.
    (* rewrite H9 in H45. *)
    lrv_solver.
    go.
    go.
    go.
  }
  intro.
  intros.
  linv_solver.
  inline_post_unfolder inline_bittbl_clearbit.
  hoare unfold.
  inverts H52.
  eapply backward_rule1.
  intro.
  intros.
  get_hsat Hs.
  sep_lifts_trms_in Hs Aarray.
  sep_lifts_trms_in Hs OSRdyTbl.
  eapply GrefArray in Hs.
  sep lift 3%nat in Hs.
  sep lift 4%nat in Hs.
  apply GrefPV in Hs.
  eauto.
  hoare unfold.
  (* rewrite H9. *)
  hoare forward.
  (* intro; tryfalse. *)
  go.

  Lemma absimp_taskdel_succ:
    forall P v3 sch t tls mqls ct ,
      can_change_aop P ->
      (* Int.lt ($ 63) v3 = false ->
       * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
       * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
       * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
      absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
        ( <|| taskdel_clear_waitls_bit (|((Vint32 v3) :: nil)|) ;;
          sdel ((Vint32 v3):: nil);; isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **
          HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  Proof.
    intros.
    unfold taskdelcode.
    infer_branch 5%nat.
    unfold sdel.
    eapply absinfer_eq.
  Qed.

(* ** ac: Show. *)

  Lemma absimp_taskdel_rdy_succ:
    forall P v3 sch t tls mqls ct ,
      can_change_aop P ->
      (* Int.lt ($ 63) v3 = false ->
       * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
       * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
       * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
      absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                       HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
        ( <|| sdel ((Vint32 v3):: nil);; isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **
          HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  Proof.
    intros.
    unfold taskdelcode.
    infer_branch 4%nat.
    unfold sdel.
    eapply absinfer_eq.
  Qed.

  destruct H56.

  { (* ... = $ OS_STAT_RDY *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskdel_rdy_succ.
    go.


    (* not in wait list *)
    subst x22.
    rewrite (H58 (eq_refl  ($ OS_STAT_RDY))). 
    hoare forward.
    (* intro; tryfalse. *)
    (* intro; tryfalse. *)
    hoare_split_pure_all.
    false.
    clear -H52.
    int auto.
    instantiate (1:=Afalse).
    hoare forward.
    hoare unfold.
    clear H52.
    hoare forward.
    hoare forward.
    
    Require Import taskdelete_ready.
    
    eapply task_delete_ready; eauto.
  }
  
  { (* ... = x22 = $ OS_STAT_SEM *)  
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskdel_succ.
    go.

    lets bb: TcbIsWait H24 H52.
    simpljoin.
    rename v'14 into ecbmap.

   
    lets bbackup: H2.
      
    rewrite <- poi_is_rtep in H2.
    unfolds in H2.
    simpljoin.
    mttac poi_R_TE ltac: (fun H => unfolds in H; lets cc: H H17).
    (* unfolds in H61. *)
    (* lets cc: H61 H72 H23. *)
    simpljoin.
      

    unfold AECBList.
    hoare normal pre.
    hoare unfold.
    lets cc: hl_get_ecb_can_split_ecblist H55 H66.
    simpljoin.

    hoare lift 2%nat pre.
    eapply backward_rule1.
    eapply evsllseg_split.
(* ** ac:     SearchAbout (length _ = length _). *)
    eapply ecblistp_length_eq_1; eauto.
    hoare normal pre.
    hoare_split_pure_all.
    hoare_assert_pure (v'4 = Vptr x10).
    {
      symmetry.
      eapply ecblistp_evsllseg_tlsame; eauto.
    }

    hoare unfold.
    unfold1 evsllseg.
    destruct x15.
    hoare unfold.
    unfold AEventNode.
    unfold AOSEvent.
    unfold node.
    unfold AOSEventTbl.
    hoare unfold.

    hoare forward.
    (* intro; tryfalse. *)
    (* intro; tryfalse. *)
    change (
        (ptr ′ → OSEventTbl) [ptcb ′ → OSTCBY] &= ∼ ptcb ′ → OSTCBBitX;ₛ
         If((ptr ′ → OSEventTbl) [ptcb ′ → OSTCBY] ==ₑ ′ 0)
         {ptr ′ → OSEventGrp &= ∼ ptcb ′ → OSTCBBitY}
      ) with (
        inline_call inline_bittbl_clearbit (
            (ptr′→OSEventGrp) :: (ptr′→OSEventTbl) ::
            (ptcb ′ → OSTCBBitX) :: (ptcb ′ → OSTCBBitY) :: (ptcb ′ → OSTCBY) :: nil)).  

    hoare_split_pure_all.
    inline_forward.
    
    2: { 
      sep pauto.
      sep cancel Aop.
      sep cancel 2%nat 2%nat.
      
      8: { (* RL_Tbl_Grp_P *) exact H78. }
      get_hsat Hs.
      unfold Astruct in Hs at 1.
      unfold OS_EVENT in Hs at 1.
      unfold Astruct' in Hs.
      
      sep normal in Hs.
      sep cancel 2%nat 1%nat.
      eauto.
      instantiate (1:= v'40).
      clear -H59; lia. 
      unfolds.
      math simpls.
      assumption.
      assumption.
      clear -H59; mauto.
      intro; intros.
      lrv_solver.
      

      Theorem struct_member_array_rv'':
        forall s x t l (* vl *) tid decl id t' n P ad perm,
          s |=  LV x @ (Tptr t) |=> Vptr l @ perm  (* ** Astruct l t vl  *)** P->
          t = Tstruct tid decl ->
          good_decllist decl = true ->
          ftype id decl = Some (Tarray t' n) ->
          id_addrval l id t = Some ad ->
          s |= Rv (efield (ederef (evar x)) id) @ (Tarray t' n) == Vptr ad.
      Proof.
        Import DeprecatedTactic.
        intros.
        destruct s as [[[[[[]]]]]].
        simpl in *;mytac.
        rewrite H12.
        rewrite H2.
        unfold load;unfold loadm.
        rewrite Int.unsigned_zero in H13.
        lets Hf: mapstoval_loadbytes H13.
        simpl;auto.
        destruct Hf.
        destruct H.
        lets Hf: loadbytes_local H4 H.
        assert ( loadbytes m (x13, 0%Z) (typelen (Tptr (Tstruct tid decl))) = Some x2);auto.
        rewrite H5.
        rewrite H0.
        destruct l.
        unfold getoff.
        unfold evaltype.
        rewrite H12.
        unfold id_addrval in H3.
        remember (field_offset id decl ) as X.
        destruct X;tryfalse.
        rewrite Int.repr_unsigned.
        simpl.
        rewrite Int.repr_unsigned.
        inverts H3;auto.
        rewrite H12.
        auto.
        intro; tryfalse.
      Qed.

      eapply struct_member_array_rv''.
      sep cancel 13%nat 1%nat.
      eauto.
      unfold OS_EVENT.
      auto.
      unfolds; simpl.
      reflexivity.

      unfolds; simpl.
      reflexivity.

      assumption.

      Theorem struct_member_lv:
        forall s x t (* vl *) tid decl id t' a b off,
          s |= Rv (evar x) @ (Tptr t) == Vptr (a, b)  (* Astruct l t vl ** *) ->
          t = Tstruct tid decl ->
          good_decllist decl = true ->
          ftype id decl = Some t' ->
          field_offset id decl = Some off ->
          s |= Lv (efield (ederef (evar x)) id) @ t' == (a, b +ᵢ off).
      Proof.
        intros.
        destruct s as [[[[[[]]]]]].
        simpl in *.

        unfold getoff.
        simpl.
        simpljoin.
        destruct (get e0 x).
        destruct p.
        rewrite H.
        destruct l.
        inverts H4.
        splits; auto.
        rewrite H3.
        rewrite Int.repr_unsigned.
        auto.

        destruct (get e x).
        destruct p.
        rewrite H.
        inverts H4.
        rewrite H3.
        splits; auto.

        rewrite Int.repr_unsigned.
        auto.
        inverts H4.
        
      Qed.
      (* ** ac:     Show. *)

      eapply struct_member_lv.
      symbolic_execution.
      unfold OS_EVENT; auto.
      unfolds; reflexivity.
      reflexivity.
      reflexivity.
      go.
      go.
      go.
    }

    linv_solver.

    hoare forward.

    2: {
      hoare unfold.
      false.
      clear -H69.
      destruct H69; int auto.
    }

    
    inline_post_unfolder inline_bittbl_clearbit.
    hoare unfold.
    inverts H69. 
    hoare forward.
    hoare forward.
    hoare unfold.
    hoare forward.
    math simpls.
    clear H92 H93 H94.

    (* destruct H39; clear H43.
     * false; subst x11; apply H35; reflexivity. *)

    (* simpljoin.
     * clear H41. *)
    destruct l2'.
    unfold1 dllseg.
    hoare unfold.
    inverts H92.
    unfold1 dllseg.
    unfold node.
    hoare unfold.

    Require Import taskdelete_waiting.
    eapply task_deletewaiting; eauto. 

  }
  
Qed.

