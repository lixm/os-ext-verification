
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
(* Require Import OSQPostPure. *)
Require Import Lia.

Require Import seplog_pattern_tacs. 

Require Import objauxvar_lemmas.
Require Import objaux_pure.

Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.

Set Nested Proofs Allowed.

Lemma absimp_taskdel_rdy_succ:
  forall P v3 sch t tls mqls ct ,
    can_change_aop P ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch ( <|| taskdelcode ((Vint32 v3) :: nil) ||> **
                     HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      ( <|| sdel ((Vint32 v3):: nil);; isched;; END (Some (Vint32 (Int.repr NO_ERR))) ||> **
                                                  HECBList mqls ** HTCBList tls ** HTime t ** HCurTCB ct ** P). 
Proof.
  intros.
  unfold taskdelcode.
  infer_branch 4%nat.
  unfold sdel.
  eapply absinfer_eq.
Qed.

Lemma lowready_not_wait4ecb:
  forall v'1 x23 x20 i13 v'40 v'26 x ecbid, 
    R_TCB_Status_P
      (Vptr (v'1, Int.zero)
         :: Vnull
         :: x23
         :: x20
         :: Vint32 i13
         :: V$ OS_STAT_RDY
         :: Vint32 v'40
         :: Vint32 (v'40&ᵢ$ 7)
         :: Vint32 (v'40 >>ᵢ $ 3)
         :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
         :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) v'26
      (v'40, x)
    ->
      x <> wait ecbid.
Proof.
  intros.
  unfolds in H.
  simpljoin.
  clear -H2.
  unfolds in H2.
  simpljoin.

  intro Hf.
  subst x.
  
  {
    clear -H2.
    unfolds in H2.
    lets bb: H2 (eq_refl  (v'40, wait ecbid) ).
    simpljoin;  tryfalse.
  }
Qed.

Lemma ECBLP_hold4del_a_tcb_rdy:
  forall lowl head tail highl ecbmap tcbmap v'40 x tcbmap_left tcb_block,
    ECBList_P head tail lowl highl ecbmap tcbmap ->
    TcbMod.joinsig (tcb_block, Int.zero) (v'40, x) tcbmap_left tcbmap ->
    (~exists eid, x = wait eid) -> 
    ECBList_P head tail lowl highl ecbmap tcbmap_left .
Proof.
  induction lowl.
  -
    simpl.
    intros.
    auto.
  -
    intros.
    unfold1 ECBList_P in *.
    simpljoin.
    destruct highl; tryfalse.
    destruct a.
    simpljoin.
    repeat tri_exists_and_solver1.
    rewrite R_ECB_ETbl_P_is_poi.
    rewrite R_ECB_ETbl_P_is_poi in H2.
    unfold poi_RLEHT in *.
    simpljoin.
    splits; auto.

    unfold poi_RHT_LE in *.
    intros.
    assert (get tcbmap tid0 = Some (prio, wait x0)).
    unfold get in *; simpl in *.
    go.
    eapply H2; eauto.
    
    unfold poi_RLE_HT in *.
    intros.

    lets bb: H6 H8.
    simpljoin.

    eapply join_get_or in H9.
    2: auto.
    2: exact H0.
    destruct H9.
    2: {
      repeat tri_exists_and_solver1.
    }
    false.
    apply H1.
    assert ( x4 = (tcb_block, Int.zero) \/ x4 <> (tcb_block, Int.zero)) by tauto.
    destruct H11; subst;
      unfold get in *; simpl in *.
    rewrite TcbMod.get_a_sig_a in H9.
    inverts H9.
    repeat tri_exists_and_solver1.
    go.


    rewrite TcbMod.get_a_sig_a' in H9.
    inverts H9.
    go.
Qed.      

Lemma poi_RH_T_E_P_hold_for_tcbdel_rdy:
  forall todel v'43 x tcbmap_left tcbmap v'16,
    TcbMod.joinsig todel (v'43, x) tcbmap_left tcbmap -> 
    (~exists eid, x = wait eid) ->
    poi_RH_T_E_P v'16 tcbmap ->
    poi_RH_T_E_P v'16 tcbmap_left.
Proof.
  intros.
  unfold poi_RH_T_E_P in *; simpljoin.
  splits; auto.

  unfold poi_R_TE in *.
  intros.
  assert (get tcbmap tid = Some (p, wait eid)).
  {
    unfold get in *; simpl in *.
    go.
  }
  lets bb: H1 H4.
  auto.

  unfold poi_R_ET in *.
  intros.
  lets bb: H2 H3.
  simpljoin.
  
  eapply join_get_or in H4; eauto.
  destruct H4; eauto.
  assert (todel = tid \/ todel <> tid) by tauto.
  unfold get in *; simpl in *.
  destruct H6; subst.
  rewrite TcbMod.get_a_sig_a in H4.
  inverts H4.
  
  false.
  apply H0.
  repeat tri_exists_and_solver1.

  go.

  rewrite TcbMod.get_a_sig_a' in H4.
  inverts H4.
  go.
  
Qed.

Set Printing Depth 999.

Lemma task_delete_ready:
  forall 
    (v'40 : int32)
    (v'26 : vallist)
    (* (v'8 : block) *)
    (v'17 : int32)
    (* (v'27 : addrval) *)
    (H1 : Int.unsigned v'40 <= 255)
    (* (v'0 v'1 v'2 v' : val)  *)
    (v'2: val) 
    (v'3 : list vallist)
    (v'4 : list EventData)
    (v'5 : list os_inv.EventCtr)
    (priotbl : vallist)
    (v'7 : val)
    (l1 l2 : list vallist)
    (v'14 : EcbMod.map)
    (tcbmap : TcbMod.map)
    (v'16 : int32)
    (vhold : addrval)
    (v'18 : val)
    (v'19 : list vallist)
    (v'20 : val)
    (v'21 : list vallist)
    (v'22 : ObjMod.map)
    (cur_tcb_blk : block)
    (H3 : RH_CurTCB (cur_tcb_blk, Int.zero) tcbmap)
    (H2 : RH_TCBList_ECBList_P v'14 tcbmap (cur_tcb_blk, Int.zero))
    (* (v'23 : val) *)
    (H4 : array_type_vallist_match OS_TCB ∗ priotbl)
    (H7 : length priotbl = 64%nat)
    (H5 : RL_RTbl_PrioTbl_P v'26 priotbl vhold)
    (H6 : R_PrioTbl_P priotbl tcbmap vhold)
    (* (v'24 v'25 : val) *)
    (v'25: val)
    (H8 : v'7 <> Vnull)
    (* (x1 x2 x3 x4 : val) *)
    (x5 : int32)
    (* (x6 x7 x8 x9 v'28 x16 x17 x18 x19 : val) *)
    (v'28 x16 x17 x18 x19 : val) 
    (i0 i1 i2 i3 i4 i5 i6 : int32)
    (H15 : Vptr (cur_tcb_blk, Int.zero) <> Vnull)
    (H12 : isptr v'28)
    (H : Int.unsigned v'40 < 64)
    (H0 : Int.unsigned v'40 <> 63)
    (hello : taskstatus)
    (kitty : ProtectWrapper (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) = Some (x5, hello)))
    (todelblock : block)
    (H14 : (todelblock, Int.zero) <> vhold)
    (H13 : nth_val' (Z.to_nat (Int.unsigned v'40)) priotbl = Vptr (todelblock, Int.zero))
    (x : taskstatus)
    (H17 : TcbMod.get tcbmap (todelblock, Int.zero) = Some (v'40, x))
    (l1' l2' : list vallist)
    (x20 : val)
    (i13 : int32)
    (v'9 : val)
    (x0 : addrval)
    (x23 : val)
    (Heqtcblst : ProtectWrapper
                (l1' ++
                 (Vptr x0
                  :: v'9
                     :: x23
                        :: x20
                           :: Vint32 i13
                              :: V$ OS_STAT_RDY
                                 :: Vint32 v'40
                                    :: Vint32 (v'40&ᵢ$ 7)
                                       :: Vint32 (v'40 >>ᵢ $ 3)
                                          :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                             :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                 :: l2' =
                 l1 ++
                 (x19
                  :: x18
                     :: x17
                        :: x16
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) :: l2))
    (H20 : ptr_in_tcbdllseg (Vptr (todelblock, Int.zero)) v'7
          (l1' ++
           (Vptr x0
            :: v'9
               :: x23
                  :: x20
                     :: Vint32 i13
                        :: V$ OS_STAT_RDY
                           :: Vint32 v'40
                              :: Vint32 (v'40&ᵢ$ 7)
                                 :: Vint32 (v'40 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) :: l2'))
    (H19 : TCBList_P v'7
          (l1' ++
           (Vptr x0
            :: v'9
               :: x23
                  :: x20
                     :: Vint32 i13
                        :: V$ OS_STAT_RDY
                           :: Vint32 v'40
                              :: Vint32 (v'40&ᵢ$ 7)
                                 :: Vint32 (v'40 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) :: l2')
    v'26 tcbmap)
    (H18 : ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'7
          (l1' ++
           (Vptr x0
            :: v'9
               :: x23
                  :: x20
                     :: Vint32 i13
                        :: V$ OS_STAT_RDY
                           :: Vint32 v'40
                              :: Vint32 (v'40&ᵢ$ 7)
                                 :: Vint32 (v'40 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) :: l2'))
    (v'10 v'11 : TcbMod.map)
    (H22 : TcbMod.join v'10 v'11 tcbmap)
    (H23 : TCBList_P v'7 l1' v'26 v'10)
    (x12 : TcbMod.map)
    (H59 : Int.unsigned v'40 < 64)
    (H51 : 0 <= Int.unsigned v'40)
    (H58 : $ OS_STAT_RDY = $ OS_STAT_RDY -> x23 = Vnull)
    (H11 : TcbJoin (todelblock, Int.zero) (v'40, x) x12 v'11)
    (H24 : R_TCB_Status_P
          (Vptr x0
           :: v'9
              :: x23
                 :: x20
                    :: Vint32 i13
                       :: V$ OS_STAT_RDY
                          :: Vint32 v'40
                             :: Vint32 (v'40&ᵢ$ 7)
                                :: Vint32 (v'40 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) v'26
          (v'40, x))
    (H46 : TCBList_P (Vptr x0) l2' v'26 x12)
    (H16 : isptr x19)
    (H21 : isptr x18)
    (H25 : isptr x17)
    (H26 : isptr x16)
    (H27 : Int.unsigned i6 <= 65535)
    (H28 : Int.unsigned i5 <= 255)
    (H29 : Int.unsigned i4 <= 255)
    (H30 : Int.unsigned i3 <= 255)
    (H31 : Int.unsigned i2 <= 255)
    (H32 : Int.unsigned i1 <= 255)
    (H33 : Int.unsigned i0 <= 255)
    (H34 : Vptr (todelblock, Int.zero) <> Vnull)
    (H35 : isptr (Vptr x0))
    (H36 : isptr v'9)
    (H37 : isptr x23)
    (H38 : isptr x20)
    (H39 : Int.unsigned i13 <= 65535)
    (H40 : Int.unsigned ($ OS_STAT_RDY) <= 255)
    (H45 : Int.unsigned ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) <= 255)
    (backup : TCBList_P (Vptr (todelblock, Int.zero))
             ((Vptr x0
               :: v'9
                  :: x23
                     :: x20
                        :: Vint32 i13
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'40
                                 :: Vint32 (v'40&ᵢ$ 7)
                                    :: Vint32 (v'40 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) :: l2')
             v'26 v'11)
    (H44 : Int.unsigned ($ 1<<ᵢ(v'40&ᵢ$ 7)) <= 255)
    (H43 : Int.unsigned (v'40 >>ᵢ $ 3) <= 255)
    (H42 : Int.unsigned (v'40&ᵢ$ 7) <= 255)
    (H41 : Int.unsigned v'40 <= 255)
    (H50 : length v'26 = ∘ OS_RDY_TBL_SIZE)
    (H9 : array_type_vallist_match char_t v'26)
    (H47 : RL_Tbl_Grp_P v'26 (Vint32 v'17))
    (H10 : Int.unsigned v'17 <= 255)
    (H48 : length v'26 = ∘ OS_RDY_TBL_SIZE)
    (H49 : prio_in_tbl ($ OS_IDLE_PRIO) v'26)
    (v'29 v'30 v'31 v'32 v'33 : expr)
    (v'37 v'38 : int32) 
    (H53 : OSRdyGrp ′
        :: OSRdyTbl ′
           :: ptcb ′ .. OSTCBBitX :: ptcb ′ .. OSTCBBitY :: ptcb ′ .. OSTCBY :: nil =
        v'30 :: v'29 :: v'31 :: v'32 :: v'33 :: nil)
    (H54 : nth_val' (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26 = Vint32 v'38)
    (H65 : Int.unsigned v'38 <= Byte.max_unsigned)
    (H57 : length
          (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))) =
        ∘ OS_RDY_TBL_SIZE)
    (H60 : rule_type_val_match char_t (Vint32 v'37) = true)
    (H61 : RL_Tbl_Grp_P
          (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7)))))))
          (Vint32 v'37))
    (H62 : forall x : int32,
        prio_in_tbl x v'26 ->
        Int.eq x v'40 = false ->
        prio_in_tbl x
          (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))))
    (H63 : prio_not_in_tbl v'40
          (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))))
    (H64 : array_type_vallist_match char_t
          (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7)))))))), 

  {|OS_spec, GetHPrio, OSLInv, I,
  fun v : option val =>
  ( <|| END v ||>  **
   p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
   ((EX v0 : val, LV prio @ char_t |-> v0) **
    (EX v0 : val, LV ptr @ OS_EVENT ∗ |-> v0) **
    (EX v0 : val, LV ptcb @ OS_TCB ∗ |-> v0) **
    (EX v0 : val, LV os_code_defs.x @ OS_TCB ∗ |-> v0) ** Aemp) **
   Aie true ** Ais nil ** Acs nil ** Aisr empisr) **
  A_dom_lenv
    ((prio, char_t)
     :: (ptr, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (os_code_defs.x, OS_TCB ∗) :: nil),
  Afalse|}|- (cur_tcb_blk, Int.zero)
  {{ <|| sdel (Vint32 v'40 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
    LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
    Astruct (todelblock, Int.zero) OS_TCB_flag
      (Vptr x0
       :: v'9
          :: Vnull
             :: x20
                :: V$ 0
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'40
                         :: Vint32 (v'40&ᵢ$ 7)
                            :: Vint32 (v'40 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) **
    HECBList v'14 **
    HTCBList tcbmap **
    HTime v'16 **
    HCurTCB (cur_tcb_blk, Int.zero) **
    LV ptr @ OS_EVENT ∗ |-> Vnull **
    GV OSRdyGrp @ char_t |-> Vint32 v'37 **
    GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE)
      (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
         (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))) **
    dllseg (Vptr x0) (Vptr (todelblock, Int.zero)) v'25 Vnull l2' OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
    dllseg v'7 Vnull v'9 (Vptr (todelblock, Int.zero)) l1' OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
    GV OSTCBList @ OS_TCB ∗ |-> v'7 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
    Aie false **
    Ais nil **
    Acs (true :: nil) **
    Aisr empisr **
    AECBList v'5 v'4 v'14 tcbmap **
    tcbdllflag v'7
      (l1' ++
       (Vptr x0
        :: v'9
           :: Vnull
              :: x20
                 :: Vint32 i13
                    :: V$ OS_STAT_RDY
                       :: Vint32 v'40
                          :: Vint32 (v'40&ᵢ$ 7)
                             :: Vint32 (v'40 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) :: l2') **
    AOSTCBPrioTbl priotbl v'26 tcbmap vhold **
    AOBJ v'21 v'22 v'14 vhold v'7
      (l1' ++
       (Vptr x0
        :: v'9
           :: Vnull
              :: x20
                 :: Vint32 i13
                    :: V$ OS_STAT_RDY
                       :: Vint32 v'40
                          :: Vint32 (v'40&ᵢ$ 7)
                             :: Vint32 (v'40 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) :: l2') v'20
      v'3 **
    A_isr_is_prop **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    AOSEventFreeList v'20 v'3 **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSIntNesting **
    AOSTCBFreeList v'18 v'19 **
    AOSTime (Vint32 v'16) **
    AGVars **
    atoy_inv' **
    LV os_code_defs.x @ OS_TCB ∗ |-> v'2 **
    LV prio @ char_t |-> Vint32 v'40 **
    A_dom_lenv
      ((prio, char_t)
       :: (ptr, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (os_code_defs.x, OS_TCB ∗) :: nil)}} 
  OSTCBPrioTbl ′ [prio ′] =ₑ NULL;ₛ
  ptcb ′ .. OSTCBEventPtr =ₑ NULL;ₛ
  IF (ptcb ′ .. OSTCBPrev ==ₑ NULL)
  {os_code_defs.x ′ =ₑ ptcb ′ .. OSTCBNext;ₛ
  os_code_defs.x ′ .. OSTCBPrev =ₑ NULL;ₛ
  OSTCBList ′ =ₑ os_code_defs.x ′}
  ELSE {os_code_defs.x ′ =ₑ ptcb ′ .. OSTCBPrev;ₛ
  os_code_defs.x ′ .. OSTCBNext =ₑ ptcb ′ .. OSTCBNext;ₛ
  os_code_defs.x ′ =ₑ ptcb ′ .. OSTCBNext;ₛ
  os_code_defs.x ′ .. OSTCBPrev =ₑ ptcb ′ .. OSTCBPrev};ₛ
  ptcb ′ .. OSTCBNext =ₑ OSTCBFreeList ′;ₛ
  OSTCBFreeList ′ =ₑ ptcb ′;ₛ
  os_task.STKFREE ptcb ′;ₛ
  ptcb ′ .. OSTCBflag =ₑ ′ 0;ₛ
  ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ
  ptcb ′ .. __OSTskPtr =ₑ NULL;ₛ
  EXIT_CRITICAL;ₛ
  OS_Sched (­);ₛ
  RETURN ′ OS_NO_ERR {{Afalse}}. 
Proof.
  intros.
  hoare unfold.
  hoare forward.
  math simpls.

  hoare forward. 

  destruct l2'.
  unfold1 dllseg.
  hoare unfold.
  inverts H67.
  unfold1 dllseg.
  unfold node.
  hoare unfold.

  destruct l1'.
  hoare_assert_pure (v'9 = Vnull).
  {
    get_hsat Hs.
    unfold1 dllseg in Hs.
    sep normal in Hs.
    sep destruct Hs.
    sep split in Hs.
    rewrite H68; reflexivity.
  }

  { (* v'9 is null, deleting first tcb node *) 
    hoare_split_pure_all.
    subst v'9.

    hoare forward.
    go.

    2: {
      hoare_split_pure_all; false.
      clear -H67; simpljoin.
      destruct H67; tryfalse.
    }

    hoare unfold.
    hoare forward.
    go.      
    hoare forward.
    hoare forward.

    hoare forward.

    2: {
      hoare_split_pure_all.
      false.
      clear -H67; destruct H67; tryfalse.      
    }

    hoare unfold.
    unfold AOSTCBFreeList.
    hoare unfold.
    hoare forward.

    eapply isptr_is_definitely_ptr.
    eapply sll_head_isptr.
    instantiate (5:=s).
    sep cancel sll.
    go.

    hoare forward.
    clear H67 H68 H69.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto.
    destruct H67.
    (* delete current *) 
    {
      subst todelblock.
      rewrite H17 in kitty.
      eapply backward_rule1.      

      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'40 :: nil);; isched;; END Some (V$ NO_ERR) ||> ** 
                      HTCBList tcbmap **
                      HCurTCB (cur_tcb_blk, Int.zero) **
                      OS [empisr, false, nil, (true::nil)] ** 
                      A_dom_lenv
                      ((prio, Int8u)
                         :: (ptr, OS_EVENT ∗)
                         :: (ptcb, OS_TCB ∗)
                         :: (os_code_defs.x, OS_TCB ∗) :: nil) **
                      GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
                      LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
                      Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
                      (v'18
                         :: Vnull
                         :: Vnull
                         :: x20
                         :: V$ 0
                         :: V$ OS_STAT_RDY
                         :: Vint32 v'40
                         :: Vint32 (v'40&ᵢ$ 7)
                         :: Vint32 (v'40 >>ᵢ $ 3)
                         :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                         :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) ** 
                      GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'1, Int.zero) **
                      LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'1, Int.zero) **
                      Astruct (v'1, Int.zero) OS_TCB_flag
                      (v'0
                         :: Vnull
                         :: x10
                         :: x9
                         :: Vint32 i12
                         :: Vint32 i11
                         :: Vint32 i10
                         :: Vint32 i9
                         :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
                      dllseg v'0 (Vptr (v'1, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                      (update_nth_val (Z.to_nat (Int.unsigned v'40)) priotbl Vnull) **
                      PV vhold @ Int8u |-> v' ** 
                      HECBList v'14 **
                      (* HTCBList tcbmap ** *)
                      HTime v'16 **
                      (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                      LV ptr @ OS_EVENT ∗ |-> Vnull ** 
                      GV OSRdyGrp @ Int8u |-> Vint32 v'37 **
                      GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                      (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
                         (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))) **
                      dllseg v'7 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag
                      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                      (* Aie false ** *)
                      (* Ais nil ** *)
                      (* Acs (true :: nil) ** *)
                      (* Aisr empisr ** *)
                      AECBList v'5 v'4 v'14 tcbmap **
                      tcbdllflag v'7
                      (nil ++
                         (Vptr (v'1, Int.zero)
                            :: Vnull
                            :: Vnull
                            :: x20
                            :: Vint32 i13
                            :: V$ OS_STAT_RDY
                            :: Vint32 v'40
                            :: Vint32 (v'40&ᵢ$ 7)
                            :: Vint32 (v'40 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                         :: (v'0
                               :: Vptr (cur_tcb_blk, Int.zero)
                               :: x10
                               :: x9
                               :: Vint32 i12
                               :: Vint32 i11
                               :: Vint32 i10
                               :: Vint32 i9
                               :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
                         :: l2') **
                      G& OSPlaceHolder @ Int8u == vhold **
                      AOBJ v'21 v'22 v'14 vhold v'7
                      (nil ++
                         (Vptr (v'1, Int.zero)
                            :: Vnull
                            :: Vnull
                            :: x20
                            :: Vint32 i13
                            :: V$ OS_STAT_RDY
                            :: Vint32 v'40
                            :: Vint32 (v'40&ᵢ$ 7)
                            :: Vint32 (v'40 >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                            :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                         :: (v'0
                               :: Vptr (cur_tcb_blk, Int.zero)
                               :: x10
                               :: x9
                               :: Vint32 i12
                               :: Vint32 i11
                               :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
                         :: l2') v'20 v'3 **
                      (* A_isr_is_prop ** *)
                      p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
                      (* LV self @ Int8u |-> (V$ 0) ** *)
                      AOSEventFreeList v'20 v'3 **
                      (* AOSQFreeList v'4 ** *)
                      (* AOSQFreeBlk v'5 ** *)
                      AOSMapTbl **
                      AOSUnMapTbl **
                      AOSIntNesting **
                      sll v'18 v'19 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
                      sllfreeflag v'18 v'19 **
                      AOSTime (Vint32 v'16) **
                      AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'40 )).  
      clear.
      intro; intros.
      sep_lifts_trms (Aisr, Ais).
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.      

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'40, x) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in *; simpl in *.
        unfold get, sig, join in *; simpl in *.
        go.
      }

      destruct H67 as (tcbmap_left & tcbmapleft_join_hyp).

      eapply seq_rule.
      eapply  derive_delself_rule.

      apply goodlinv.
      go.
      
      exact tcbmapleft_join_hyp.
      intro; intros.
      split.
      sep_get_rv.      
      { (* s |= CurLINV OSLInv (cur_tcb_blk, Int.zero) *) 
        get_hsat Hs.
        unfold p_local in Hs.
        unfold CurLINV.
        sep pauto.
        sep cancel LINV.
        simpl; auto 1.
      }

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *)
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24)  ) in Hs.
      eauto.      

      hoare_lifts_trms_pre Aop. 
      (* hoare lift 2%nat pre. *) 
      eapply seq_rule.
      eapply assign_rule'.

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 14%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }
      eapply eq_int; auto.      
      
      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      get_hsat Hs.
      sep_lifts_skp_in Hs (flag_off, _N_ 1).
      sep cancel 1%nat 1%nat.
      (* sep cancel 40%nat 1%nat. *)
      do 2 (sep cancel 2%nat 1%nat).
      simpl; auto.
      splits; eauto.
      unfolds; auto.       

      (* ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ *)
      unfold AOBJ.
      unfold tcbllsegobjaux.
      remember ((v'12
            :: Vptr (cur_tcb_blk, Int.zero)
               :: x10
                  :: x9
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10
                              :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
           :: l2') as tl.
      unfold1 llsegobjaux.
      unfold objaux_node.
      hoare unfold.      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 25) ) in Hs.
      eauto.      
      
      hoare_lifts_trms_pre Aop. 
      eapply seq_rule.
      eapply assign_rule'.

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 18%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }
      eapply eq_int; auto.      
      
      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      get_hsat Hs.
      sep_lifts_skp_in Hs (loc_off, _N_ 0).
      sep cancel 1%nat 2%nat.
      (* sep cancel 40%nat 1%nat. *)
      sep_lifts_skp_in Hs (flag_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep cancel 3%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.       
      unfolds. left; auto.

      (* ptcb ′ .. __OSTskPtr =ₑ NULL;ₛ *)
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 26) ) in Hs.
      eauto.      
      
      hoare_lifts_trms_pre Aop. 
      eapply seq_rule.
      eapply assign_rule'.

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 17%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }
      eapply eq_tnull.
      left. eexists; eauto.
      
      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      get_hsat Hs.
      sep cancel 5%nat 1%nat.
      sep cancel 2%nat 1%nat.      
      sep_lifts_skp_in Hs (ptr_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.       
      unfolds. left; auto.
      
      (* EXIT_CRITICAL;ₛ *)
      (* OS_Sched (­);ₛ *)
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      (* sep lifts (7::9::nil)%nat in H68. *)
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *)
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      introv Hs.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.      

      sep cancel 7%nat 1%nat. 
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      (* sep cancel AOSQFreeList. *)
      (* sep cancel AOSQFreeBlk. *)      
      sep cancel (Aabsdata curtid).
      sep cancel AGVars.
      sep cancel AOSMapTbl.
      sep cancel AOSUnMapTbl.
      sep cancel AOSIntNesting.
      sep cancel (Aabsdata absecblsid).
      sep cancel (Aabsdata abstcblsid).
      sep cancel AOSTime.
      sep cancel (Aabsdata ostmid).
      instantiate (19 := v'5).
      instantiate (18 := v'4).
      unfold AECBList.      
      unfold AECBList in Hs.
      sep pauto.

      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 21%nat 1%nat.
      sep cancel OSEventList.
      sep cancel evsllseg.
      sep cancel OSPlaceHolder.
      sep cancel OSTCBPrioTbl.
      
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      sep_lifts_trms Adisj.
      eapply intro_or_r.
      sep normal.
      sep eexists.
      sep cancel OSTCBCur.
      sep cancel OSTCBList.
      sep pauto.
      unfold tcblist.
      instantiate (14 := nil).
      instantiate (13 := l2').
      instantiate (10 := v'12
                           :: Vnull
                           :: x10
                           :: x9
                           :: Vint32 i12
                           :: Vint32 i11
                           :: Vint32 i10
                           :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil).

      sep normal.
      sep_lifts_trms AOBJ.
      unfold AOBJ.
      sep normal.

      exists v'27. exists v'34.
      sep cancel (Aabsdata absobjsid).
      sep cancel AObjs.
      sep split.
      sep_lifts_skp (loc_off, _N_ 0).
      sep cancel 4%nat 1%nat.
      sep_lifts_skp (ptr_off, _N_ 0).
      sep cancel 4%nat 1%nat.
      sep cancel A_isr_is_prop.
      unfold tcbllsegobjaux.
      sep cancel llsegobjaux.
      sep cancel OSRdyGrp.
      sep cancel OSRdyTbl.

      unfold TCB_Not_In.
      sep pauto.      
      
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 11%nat 1%nat.
      sep cancel 11%nat 1%nat.
      unfold1 tcbdllflag.
      unfold tcbdllflag in Hs.
      rewrite app_nil_l.
      unfold1 dllsegflag.
      unfold1 dllsegflag in Hs.
      sep normal in Hs.
      sep pauto.      

      sep cancel dllsegflag.
      sep cancel 4%nat 1%nat.
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_r. 
      unfold TCBFree_Eq.
      sep pauto.
      sep cancel sll.
      sep cancel sllfreeflag.
      eauto.      
      go.
      eapply isptr_is_definitely_ptr.
      eapply sll_head_isptr.
      instantiate (5:=s).
      sep cancel sll.
      go.
      
      { (* RL_TCBblk_P *) 
        unfolds.
        do 6 eexists.
        splits.
        go.
        go.
        go.
        go.
        go.
        go.
        go.
        splits.
        go.
        go.
        go.
        go.
        left; auto.
        repeat tri_exists_and_solver1.
        go.
        lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
        subst.
        reflexivity.        
      }
      eexists; go.
      { (* prio_not_in_tcbls v'40 tcbmap_left *) 
        unfolds in H6.
        simpljoin.
        Ltac mttac C tac :=
          match goal with H: context[C] |- _ => (tac H) end. 
        mttac (R_Prio_No_Dup tcbmap)
          ltac:(fun H=> clear -tcbmapleft_join_hyp H; rename H into Hnd).
        (* clear -tcbmapleft_join_hyp H93. *)
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in Hnd.
        assert (x0 <> (cur_tcb_blk, Int.zero)).
        {
          intro.
          subst. 
          eapply TcbMod.map_join_get_some .
          
          auto.
          eauto.
          2: exact H.
          instantiate (1:=(v'40, x)).
          unfold get in *; simpl in *.
          unfold sig in *; simpl in *.
          eapply TcbMod.get_a_sig_a.
          go.
        }
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x0 =Some (v'40, x1) ) by go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some (v'40, x) ) by go.
        lets bb: Hnd H0 H1 H2.
        apply bb.
        reflexivity.
      }      
      go.
      go.
      intro; tryfalse.
      go.
      go.
      { (* ~ptr_in_tcblist ... *)
        split.
        rewrite ptr_in_tcblist_app.
        2: simpl; auto.
        intro.
        destruct H91.
        simpl in H91.
        exact H91.
        simpl (val_inj (get_last_tcb_ptr nil (Vptr (v'1, Int.zero)))) in H91.
        gen H91.
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        2: {
          match goal with
            H: R_TCB_Status_P ?vl _ _ |- _ =>
              instantiate (1 := vl)
          end.
          go.
        }
        2:instantiate (3 :=  nil).
        simpl; auto.
        rewrite app_nil_l.

         exact backup.
         simpl.
         auto.
         eauto.                
      }
      { (* TCBList_P *)  
        rewrite app_nil_l.
        rewrite app_nil_l in H19.

        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H19.
        2: exact tcbmapleft_join_hyp.
        unfolds in H6.
        simpljoin; assumption.
      }
      { (* objref_distinct *)
        go.
      }
      {
        eapply objdel_nodup_tskdel_preserve; eauto.
      }
      {
        eapply objcre_nodup_tskdel_preserve; eauto.        
      }
      {
        assert (Hjol':
                 join (sig (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal)) v'27
                  (set v'6 (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in H89.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (cur_tcb_blk, Int.zero) Vnull) v'34 (set v'9 (cur_tcb_blk, Int.zero) Vnull)).
        {
          unfolds in H90.
          eapply join_sig_set; eauto.          
        }
        clear H89 H90.
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(cur_tcb_blk, Int.zero)) in H92. 
        eapply obj_aux_p_tsk_del_preserve; eauto.
      }

      { (* vhold_addr = vhold_addr *)
        reflexivity.
      }

      { (* RL_Tbl_Grp_P ... /\ prio_in_tbl ... *) 
        split.
        assumption.
        eapply (H62 _ H49).
        clear -H0; unfold OS_IDLE_PRIO.
        csimpl OS_LOWEST_PRIO.
        int auto.        
      }

      { go. }
      { go. }

      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }      

      {
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        lia.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.        
      }

      {
        split.
        -
          eapply array_type_vallist_match_hold.
          assumption.

          rewrite H7.
          clear -H; mauto.
          reflexivity.
        -
          rewrite hoare_assign.update_nth_val_len_eq.
          assumption.
      }

      { (* ECBList_P *) 
        assert (Hnex: ~exists eid, x = wait eid).
        {
          introv Hf. simpljoin. 
          lets H__: lowready_not_wait4ecb H24; eauto.
        }

        eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }

      {
        (* RH_TCBList_ECBList_P ... *)
        assert (Hnex: ~exists eid, x = wait eid).
        {
          introv Hf. simpljoin. 
          lets H__: lowready_not_wait4ecb H24; eauto.          
        }
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
        
      }

      splits; go.
      unfolds. right; auto.
      unfolds. left; auto.
      go.

      (* OS_Sched (-) *)
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H69.
      go.

      inverts H69.
      reflexivity.
    }

    { (* delete some tcb other than current, at head *)
      eapply backward_rule1.
      intro; intros.
      instantiate ( 1 := (
                          <|| sdel (Vint32 v'40 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                              HTCBList tcbmap **
                              HCurTCB (cur_tcb_blk, Int.zero) **
                              OS [empisr, false, nil, (true::nil)] ** 
                              (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
           A_dom_lenv
             ((prio, Int8u)
              :: (ptr, OS_EVENT ∗)
                 :: (ptcb, OS_TCB ∗)
                 :: (os_code_defs.x, OS_TCB ∗) :: nil) **
           GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
           Astruct (todelblock, Int.zero) OS_TCB_flag
             (v'18
              :: Vnull
                 :: Vnull
                    :: x20
                       :: V$ 0
                          :: V$ OS_STAT_RDY
                             :: Vint32 v'40
                                :: Vint32 (v'40&ᵢ$ 7)
                                   :: Vint32 (v'40 >>ᵢ $ 3)
                                      :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                         :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3))
                                            :: nil) **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'1, Int.zero) **
           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'1, Int.zero) **
           Astruct (v'1, Int.zero) OS_TCB_flag
             (v'0
              :: Vnull
                 :: x10
                    :: x9
                       :: Vint32 i12
                          :: Vint32 i11
                             :: Vint32 i10
                                :: Vint32 i9
                                   :: Vint32 i8
                                      :: Vint32 i7 :: Vint32 i :: nil) **
           dllseg v'0 (Vptr (v'1, Int.zero)) v'25 Vnull l2' OS_TCB_flag
             (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
             (update_nth_val (Z.to_nat (Int.unsigned v'40)) priotbl Vnull) **
           PV vhold @ Int8u |-> v' **
           HECBList v'14 **
           (* HTCBList tcbmap ** *)
           HTime v'16 **
           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
           LV ptr @ OS_EVENT ∗ |-> Vnull **
           GV OSRdyGrp @ Int8u |-> Vint32 v'37 **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
             (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
                (val_inj
                   (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))) **
           dllseg v'7 Vnull Vnull (Vptr (todelblock, Int.zero)) nil OS_TCB_flag
           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **             
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
           (* Aie false ** *)
           (* Ais nil ** *)
           (* Acs (true :: nil) ** *)
           (* Aisr empisr ** *)
           AECBList v'5 v'4 v'14 tcbmap **
           tcbdllflag v'7
             (nil ++
              (Vptr (v'1, Int.zero)
               :: Vnull
                  :: Vnull
                     :: x20
                        :: Vint32 i13
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'40
                                 :: Vint32 (v'40&ᵢ$ 7)
                                    :: Vint32 (v'40 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3))
                                             :: nil)
              :: (v'0
                  :: Vptr (todelblock, Int.zero)
                     :: x10
                        :: x9
                           :: Vint32 i12
                              :: Vint32 i11
                                 :: Vint32 i10
                                    :: Vint32 i9
                                       :: Vint32 i8
                                          :: Vint32 i7 :: Vint32 i :: nil)
                 :: l2') **
           G& OSPlaceHolder @ Int8u == vhold **
           AOBJ v'21 v'22 v'14 vhold v'7
             (nil ++
              (Vptr (v'1, Int.zero)
               :: Vnull
                  :: Vnull
                     :: x20
                        :: Vint32 i13
                           :: V$ OS_STAT_RDY
                              :: Vint32 v'40
                                 :: Vint32 (v'40&ᵢ$ 7)
                                    :: Vint32 (v'40 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
              :: (v'0
                  :: Vptr (todelblock, Int.zero)
                     :: x10
                        :: x9
                           :: Vint32 i12
                              :: Vint32 i11
                                 :: Vint32 i10
                                    :: Vint32 i9
                                       :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) :: l2')
             v'20 v'3 **
           (* A_isr_is_prop ** *)
           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
           (* LV self @ Int8u |-> (V$ 0) ** *)
           AOSEventFreeList v'20 v'3 **
           (* AOSQFreeList v'4 ** *)
           (* AOSQFreeBlk v'5 ** *)
           AOSMapTbl **
           AOSUnMapTbl **
           AOSIntNesting **
           sll v'18 v'19 OS_TCB_flag (fun vl : vallist => nth_val 0 vl) **
           sllfreeflag v'18 v'19 **
           AOSTime (Vint32 v'16) **
           AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'40 )).

      sep_lifts_trms (Aisr, Ais).
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.      

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'40, x) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in H22; simpl in H22.
        unfold get, sig, join in H22, H9; simpl in H22, H9.
        go.
      }

      destruct H68 as (tcbmap_left & tcbmapleft_join_hyp).
      rename H67 into not_cur_hyp.

      eapply seq_rule.
      eapply  derive_delother_rule.
      apply goodlinv.
       (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      (* unfold p_local. *)
      (* unfold CurTid; unfold LINV. *)
      (* unfold OSLInv. *)
      (* go. *)
      exact tcbmapleft_join_hyp.
      clear -H3.
      unfolds in H3.
      unfolds.
      simpljoin; eauto.

      {
        clear -not_cur_hyp.
        intro H; inverts H; apply not_cur_hyp; reflexivity.
      }
      
      intro; intros.
      split.
      sep_get_rv.
      unfold p_local in H67.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      (* ptcb ′ .. OSTCBflag =ₑ ′ 0;ₛ *)
      (* ... *)  
      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare_lifts_trms_pre OSLInv.
      (* hoare lift 4%nat pre. *)
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in H67.
      eauto.      

      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 14%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }      
      eapply eq_int; auto.
      linv_solver.

      (* ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ *)
      unfold AOBJ.
      unfold tcbllsegobjaux.
      remember ((v'13
            :: Vptr (todelblock, Int.zero)
               :: x10
                  :: x9
                     :: Vint32 i12
                        :: Vint32 i11
                           :: Vint32 i10
                              :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
           :: l2') as tl.
      unfold1 llsegobjaux.
      unfold objaux_node.
      hoare unfold.      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 25) ) in Hs.
      eauto.      
      
      unfold p_local at 2.
      unfold LINV, OSLInv.
      hoare normal pre.
      hoare_ex_intro.
      hoare_lifts_skp_pre (loc_off, _N_ 1).
      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 22%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }
      eapply eq_int; auto.      
      
      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.

      (* ptcb ′ .. __OSTskPtr =ₑ NULL;ₛ *)
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 26) ) in Hs.
      eauto.      
      
      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.
      instantiate (1:=Tnull).

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 21%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }
      eapply eq_tnull. left; eexists; eauto.
      
      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      hoare_split_pure_all.
      rename H67 into Hilg.
      rename H68 into Hgla.

      (* EXIT_CRITICAL;ₛ
           OS_Sched (­);ₛ        
           RETURN ′ OS_NO_ERR *)
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *)
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      eapply poi_OSINV_imply_OSInv.

      get_hsat Hs.
      unfold poi_OSINV.      
      sep pauto.
      sep cancel AOSEventFreeList.
      instantiate (14 := v'5).
      instantiate (13 := v'4).
      unfold AECBList.
      unfold AECBList in Hs.
      sep pauto.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel 17%nat 1%nat.
      sep cancel OSPlaceHolder.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      instantiate (4 := (
                         (v'13
                            :: Vnull
                            :: x10
                            :: x9
                            :: Vint32 i12
                            :: Vint32 i11
                            :: Vint32 i10
                            :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) :: l2')).  

      sep_lifts_trms AOBJ.
      unfold AOBJ.
      sep normal.
      exists v'27. exists v'34.
      sep cancel (Aabsdata absobjsid).
      sep cancel AObjs.
      sep split.
      unfold tcbllsegobjaux.
      sep cancel llsegobjaux.
      
      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.      
      sep cancel 4%nat 1%nat.
      sep cancel dllsegflag.
      sep cancel dllseg.
      sep cancel 9%nat 1%nat.

      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.      

      instantiate (2 := (
                         v'18
                           :: Vnull
                           :: Vnull
                           :: x20
                           :: V$ 0
                           :: V$ OS_STAT_RDY
                           :: Vint32 v'40
                           :: Vint32 (v'40&ᵢ$ 7)
                           :: Vint32 (v'40 >>ᵢ $ 3)
                           :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                           :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil                         
                       ) :: v'19).
      unfold sll.
      unfold sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      unfold node.
      unfold sll in Hs.
      unfold sllfreeflag in Hs.
      sep pauto.
      sep cancel sllseg.
      sep cancel sllsegfreeflag.
      
      sep cancel 3%nat 1%nat.
      sep cancel Astruct.
      sep cancel 2%nat 1%nat.
      sep cancel 1%nat 1%nat.
      eauto.
      go.
      go.
      apply isptr_is_definitely_ptr.
      eapply sllseg_head_isptr.
      instantiate (5:=s).
      sep cancel sllseg.
      eauto.

      {
        go. 
      }
      intro; tryfalse.
      go.
      go.
      go.
      intro; tryfalse.
      
      {
        unfold objref_distinct in H93.
        introv Hg1 Hg2.
        eapply H93; eauto.
      }
      {
        eapply objdel_nodup_tskdel_preserve; eauto.        
      }
      {
        eapply objcre_nodup_tskdel_preserve; eauto.        
      }
      {
        assert (Hjol':
                 join (sig (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal)) v'27
                  (set v'6 (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in H87.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (todelblock, Int.zero) Vnull) v'34 (set v'8 (todelblock, Int.zero) Vnull)).  
        {
          unfolds in H88.
          eapply join_sig_set; eauto.          
        }
        clear H87 H88. 
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(todelblock, Int.zero)) in H90. 
        eapply obj_aux_p_tsk_del_preserve; eauto.        
      }

      { (* vhold_addr = vhold_addr *)
        reflexivity.
      }
      {
        introv Heq.
        apply not_cur_hyp.
        inverts Heq; auto.
      }
      { (* TCBList_P *) 
        rewrite app_nil_l in H19.
        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H19.
        2: exact tcbmapleft_join_hyp.
        unfolds in H6.
        simpljoin; assumption.        
      }
      {
        clear -H18 not_cur_hyp .
        eapply ptr_in_tcbdllseg_change_head.
        2: {
          eapply ptr_in_tcbdllseg_not_head.
          rewrite app_nil_l in H18.
          2: eauto.
          simpl; auto.
          intro; tryfalse.
        }
        unfold V_OSTCBNext.
        reflexivity.
      }      
      
      (* from tcblist_p, get they are all different? *)
      split.
      assumption.
      eapply (H62 _ H49).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.      

      {  (* r_priotbl_p hold for deleting a tcb *)
        eapply r_priotbl_p_hold_for_del_a_tcb.
        
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }
      { (* rl_rtbl_ptbl_p hold for deleting a tcb *)
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        lia.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.        
      }

      split.

      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.      

      {
        assert (~exists ecbid,  x = wait ecbid).
        {
          intros.
          intro.
          destruct H89.
          gen H89.

          eapply lowready_not_wait4ecb.
          lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
          subst x23.
          exact H24.
        }
        eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }      

      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
        intros.
        intro.
        destruct H68.
        gen H68.
        eapply lowready_not_wait4ecb.
        lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
        subst x23.
        exact H24.     
      }

      { (* GoodFrm *)
        go.
      }

      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      {
        get_hsat Hs.
        unfold p_local in Hs.
        unfold LINV, OSLInv in Hs.
        sep normal in Hs.
        sep destruct Hs.
        sep split in Hs.
        simpljoin.
        inverts H67.
        unfolds; auto.
      }
      go.
      linv_solver.
      linv_solver.
      
      (* RETURN ′ OS_NO_ERR *) 
      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      {
        inverts H68.
        unfold init_lg in H97.
        inverts H97.
        exact H67.
      }
      {
        inverts H68.
        reflexivity. 
      }
    }
  }

  (* delete some tcb in the middle of the tcblist *)
  {
    destruct H36.
    hoare_assert_pure False.
    subst v'9.

    eapply dllseg_tail_not_null.
    instantiate (10:=s0).
    sep pauto.
    get_hsat Hs.
    sep_lifts_skp_in Hs (dllseg, _N_ 1).
    sep cancel 1%nat 1%nat.
    eauto.
    hoare unfold.
    false.

    destruct H36 as (prev_tcb_ptr & eqprev); subst v'9.
    (* rename x11 into prev_tcb_ptr. *)

    eapply backward_rule1.
    intro; intros.
    get_hsat Hs.
    sep_lifts_skp_in Hs (dllseg, _N_ 1).
    (* sep lift 16%nat in Hs. *)
    rewrite dllseg_split_node_tail in Hs.
    
    eauto.
    unfold node.
    hoare unfold.
    rename v'12 into prev_tcb_block.
    rename v'1 into next_tcb_block.    

    hoare forward.
    go.
    hoare unfold.
    instantiate (1:= Afalse).
    false.

    hoare unfold.
    clear H36.
    hoare forward.
    go.
    hoare forward.
    go.
    hoare forward.
    go.
    hoare forward.
    go.
    
    hoare forward.
    hoare unfold.
    unfold AOSTCBFreeList.
    hoare normal pre.
    hoare forward.
    eapply isptr_match_eq_true.
    eapply sll_head_isptr.
    instantiate (5 := s).
    sep cancel sll.
    eauto.

    hoare forward.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H68.
    { (* delete current *) 
      subst todelblock.
      rewrite H17 in kitty.
      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'40 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
                           (* <|| sdel (Vint32 v'43 :: nil);; isched;; END Some (V$ NO_ERR) ||>  ** *)
                           A_dom_lenv
                           ((prio, Int8u)
                              :: (ptr, OS_EVENT ∗)
                              :: (ptcb, OS_TCB ∗)
                              :: (os_code_defs.x, OS_TCB ∗) :: nil) ** 
                           GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
                           LV ptcb @ OS_TCB ∗ |-> Vptr (cur_tcb_blk, Int.zero) **
                           Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag
                           (v'18
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: Vnull
                              :: x20
                              :: V$ 0
                              :: V$ OS_STAT_RDY
                              :: Vint32 v'40
                              :: Vint32 (v'40&ᵢ$ 7)
                              :: Vint32 (v'40 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) **
                           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
                           Astruct (next_tcb_block, Int.zero) OS_TCB_flag
                           (v'0
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: x10
                              :: x9
                              :: Vint32 i12
                              :: Vint32 i11
                              :: Vint32 i10
                              :: Vint32 i9
                              :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
                           Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
                           (Vptr (next_tcb_block, Int.zero)
                              :: v'6
                              :: x11
                              :: x8
                              :: Vint32 i20
                              :: Vint32 i19
                              :: Vint32 i18
                              :: Vint32 i17
                              :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) **
                           dllseg v'7 Vnull v'6 (Vptr (prev_tcb_block, Int.zero)) v'8 OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           dllseg v'0 (Vptr (next_tcb_block, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                           (update_nth_val (Z.to_nat (Int.unsigned v'40)) priotbl Vnull) **
                           PV vhold @ Int8u |-> v' **
                           HECBList v'14 **
                           (* HTCBList tcbmap ** *)
                           HTime v'16 **
                           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                           LV ptr @ OS_EVENT ∗ |-> Vnull **
                           GV OSRdyGrp @ Int8u |-> Vint32 v'37 **
                           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
                              (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))) **
                           GV OSTCBList @ OS_TCB ∗ |-> v'7 **
                           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                          (* Aie false ** *)
                          (* Ais nil ** *)
                          (* Acs (true :: nil) ** *)
                          (* Aisr empisr ** *)
                         AECBList v'5 v'4 v'14 tcbmap **
                         tcbdllflag v'7
                         ((v :: l1') ++
                            (Vptr (next_tcb_block, Int.zero)
                               :: Vptr (prev_tcb_block, Int.zero)
                               :: Vnull
                               :: x20
                               :: Vint32 i13
                               :: V$ OS_STAT_RDY
                               :: Vint32 v'40
                               :: Vint32 (v'40&ᵢ$ 7)
                               :: Vint32 (v'40 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                            :: (v'0
                                  :: Vptr (cur_tcb_blk, Int.zero)
                                  :: x10
                                  :: x9
                                  :: Vint32 i12
                                  :: Vint32 i11
                                  :: Vint32 i10
                                  :: Vint32 i9
                                  :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
                            :: l2') **
                         G& OSPlaceHolder @ Int8u == vhold **
                         AOBJ v'21 v'22 v'14 vhold v'7
                         ((v :: l1') ++
                            (Vptr (next_tcb_block, Int.zero)
                               :: Vptr (prev_tcb_block, Int.zero)
                               :: Vnull
                               :: x20
                               :: Vint32 i13
                               :: V$ OS_STAT_RDY
                               :: Vint32 v'40
                               :: Vint32 (v'40&ᵢ$ 7)
                               :: Vint32 (v'40 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                            :: (v'0
                                  :: Vptr (cur_tcb_blk, Int.zero)
                                  :: x10
                                  :: x9
                                  :: Vint32 i12
                                  :: Vint32 i11
                                  :: Vint32 i10
                                  :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
                            :: l2') v'20 v'3 **                         
                         (* A_isr_is_prop ** *)
                         p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
                         (* LV self @ Int8u |-> (V$ 0) ** *)
                         AOSEventFreeList v'20 v'3 **
                         (* AOSQFreeList v'4 ** *)
                         (* AOSQFreeBlk v'5 ** *)
                         AOSMapTbl **
                         AOSUnMapTbl **
                         AOSIntNesting **
                         sll v'18 v'19 OS_TCB_flag V_OSTCBNext **
                         sllfreeflag v'18 v'19 **
                         AOSTime (Vint32 v'16) **
                         AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'40 )).   
      
      clear.
      intro; introv Hs.
      sep_lifts_trms (Aisr, Ais).
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'40, x) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in *; simpl in *.
        unfold get, sig, join in *; simpl in *.
        go.
      }

      destruct H68 as (tcbmap_left & tcbmapleft_join_hyp).


      eapply seq_rule.
      eapply derive_delself_rule.
      apply goodlinv.      

      { (* GoodFrm *)
        go.
      }
      {
        exact tcbmapleft_join_hyp.
      }
      {
        intro; intros.
        split.
        sep_get_rv.
        get_hsat Hs.
        unfold p_local in Hs.
        unfold CurLINV.
        sep pauto.
        sep cancel LINV.
        simpl; auto 1.
      }

      hoare_lifts_trms_pre tcbdllflag.
      (* hoare lift 27%nat pre. *)
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag.
      hoare_split_pure_all.
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      inverts H94.
      inverts H68.
      inverts H96.
      rewrite H67.

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (cur_tcb_blk, Int.zero)
                                                                   :: v'6
                                                                   :: x11
                                                                   :: x8
                                                                   :: Vint32 i20
                                                                   :: Vint32 i19
                                                                   :: Vint32 i18
                                                                   :: Vint32 i17
                                                                   :: Vint32 i16
                                                                   :: Vint32 i15 :: Vint32 i14 :: nil) = Some (Vptr v'9)).
      {
        eapply dllsegflag_last_next_is_endstnl.
        instantiate (4 := s0).
        sep cancel 4%nat 1%nat.
        eauto.
      }

      hoare_split_pure_all. 
      inverts H68.

      unfold p_local at 2. 
      unfold OSLInv at 3. 
      unfold LINV. 
      hoare_split_pure_all. 
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24) ) in Hs.
      eauto.

      hoare_lifts_trms_pre Aop.
      (* hoare lift 5%nat pre. *)
      eapply seq_rule.
      eapply assign_rule'.

      2: { 
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          sep cancel 15%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      } 
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      get_hsat Hs.
      sep_lifts_skp_in Hs (flag_off, _N_ 1).
      sep cancel 1%nat 1%nat.
      (* sep cancel 43%nat 1%nat. *)
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      simpl; auto.
      splits; eauto.
      unfolds; auto.

      (* ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ *)
      unfold AOBJ. 
      unfold tcbllsegobjaux.
      hoare unfold.
      eapply backward_rule1.
      introv Hs.
      sep_lifts_trms_in Hs llsegobjaux.
      eapply tcbllsegobjaux_split3_join2_frm in Hs; eauto.      
      hoare unfold.
      
      hoare_assert_pure (v'43 = (cur_tcb_blk, Int.zero)).
      {
        get_hsat Hs.
        apply llsegobjaux_tn_eq in Hs.
        simpl in Hs. inverts Hs.
        auto.
      }
      hoare_split_pure_all.
      subst v'43.
      unfold objaux_node.
      hoare unfold.      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 25) ) in Hs.
      eauto.

      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

      2: { 
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          simpl fst. simpl snd.
          sep cancel 20%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      } 
      eapply eq_int; auto.

      introv Hs.
      sep normal in Hs.
      unfold p_local.
      unfold LINV, OSLInv.
      sep pauto.
      sep_lifts_skp_in Hs (flag_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep_lifts_skp_in Hs (loc_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep_lifts_skp_in Hs (ptr_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep cancel CurTid.
      sep auto.
      go.
      unfolds. right; auto.
      unfolds. left; auto.
      
      (* ptcb ′ .. __OSTskPtr =ₑ NULL;ₛ *)
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 26) ) in Hs.
      eauto.

      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

      2: { 
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          simpl fst. simpl snd.
          sep cancel 19%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      } 
      eapply eq_tnull; auto.
      left.
      eexists; eauto.
      
      introv Hs.
      sep normal in Hs.
      unfold p_local.
      unfold LINV, OSLInv.
      sep pauto.
      sep_lifts_skp_in Hs (flag_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep_lifts_skp_in Hs (loc_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep_lifts_skp_in Hs (ptr_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep cancel CurTid.
      sep auto.
      go.
      unfolds. right; auto.
      unfolds. left; auto.
      unfolds. left; auto.

      (* EXIT_CRITICAL;ₛ *)
      (* OS_Sched (­);ₛ *)
      assert (Hdjl: disjoint v'35 v'27).
      {
        apply join_comm in H105.
        eapply join_join_disj_r; eauto.
      }
      assert (Hdjp: disjoint v'36 v'34).
      {
        apply join_comm in H106.
        eapply join_join_disj_r; eauto.
      }
      assert (Hjoml: TcbJoin (cur_tcb_blk, Int.zero) (Vint32 i21) (merge v'27 v'35) v'12).
      {
        apply join_comm in H105.
        unfold TcbJoin.
        asserts_rewrite (merge v'27 v'35 = merge v'35 v'27).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }
      assert (Hjomp: TcbJoin (cur_tcb_blk, Int.zero) v'24 (merge v'34 v'36) v'13).
      {
        apply join_comm in H106.
        unfold TcbJoin.
        asserts_rewrite (merge v'34 v'36 = merge v'36 v'34).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }
      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      (* sep lifts (8::10::nil)%nat in H100. *)
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *)
      eapply seq_rule.      

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local, OSLInv.
      unfold LINV.
      sep pauto.
      get_hsat Hs.
      sep_lifts_skp_in Hs (flag_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep_lifts_skp_in Hs (loc_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep_lifts_skp_in Hs (ptr_off, _N_ 0).
      sep cancel 1%nat 1%nat.
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      (* sep cancel AOSQFreeList. *)
      (* sep cancel AOSQFreeBlk. *)
      instantiate (17 := v'5).
      instantiate (16 := v'4).
      unfold AECBList.      
      
      unfold AECBList in Hs.
      sep pauto.      

      unfold AOSTCBPrioTbl.
      sep pauto.      
      sep cancel OSPlaceHolder.
      sep cancel (Aptrmapsto vhold_addr).
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold AOSTCBList'.
      sep_lifts_trms Adisj.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.      

      instantiate (5 := v'8 ++
                          ((Vptr (next_tcb_block, Int.zero)
                              :: v'6
                              :: x11
                              :: x8
                              :: Vint32 i20
                              :: Vint32 i19
                              :: Vint32 i18
                              :: Vint32 i17
                              :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) :: nil)).
      instantiate (3 := l2').
      instantiate (3 := 
                     v'15
                       :: Vptr (prev_tcb_block, Int.zero)
                       :: x10
                       :: x9
                       :: Vint32 i12
                       :: Vint32 i11
                       :: Vint32 i10
                       :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil). 
      unfold TCB_Not_In.
      sep pauto.

      sep_lifts_trms AOBJ.
      unfold AOBJ.
      sep normal.
      exists (merge v'27 v'35).
      exists (merge v'34 v'36).
      sep cancel (Aabsdata absobjsid).
      sep cancel AObjs.
      sep split.

      unfold tcbllsegobjaux.
      eapply llsegobjaux_merge2_frm; eauto.
      sep_lifts_skp_in Hs (llsegobjaux, _N_ 0).
      eapply llsegobjaux_update_tn; eauto.
      sep cancel llsegobjaux.
      2: {
        simpl. eauto.
      }
      sep_lifts_skp_in Hs (llsegobjaux, _N_ 0).
      eapply llsegobjaux_update_prev; eauto.
      sep cancel llsegobjaux.
      2: {
        simpl. eauto.
      }


      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 12%nat 1%nat.
      sep_lifts_skp_in Hs (dllseg, _N_ 1).
      sep cancel 1%nat 1%nat.
      
      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      instantiate (3 := (Vptr (prev_tcb_block, Int.zero))).
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep_lifts_skp_in Hs (Astruct, _N_ 1).
      sep cancel 1%nat 1%nat.
      sep cancel dllseg.
      
      unfold tcbdllflag.
      sep_lifts_skp_in Hs (dllsegflag, _N_ 1).
      rewrite dllsegflag_is_poi in Hs.
      apply split_poillseg in Hs.

      apply dllsegflag_is_poi.
      sep pauto.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep normal.
      sep normal in Hs.
      sep destruct Hs.
      sep eexists.
      instantiate ( 3 := Vptr (next_tcb_block, Int.zero)).
      sep pauto.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      (* instantiate (x1 := x14). *)
      sep cancel 1%nat 2%nat.
      sep cancel 4%nat 1%nat.

      (* freelist *)
      {
        unfold AOSTCBFreeList'.
        sep pauto.
        eapply intro_or_r. 
        unfold TCBFree_Eq.
        sep pauto.
        sep cancel sll.
        sep cancel sllfreeflag.
        eauto.
        go.
        eapply isptr_is_definitely_ptr.
        eapply sll_head_isptr.
        instantiate (5:=s).
        sep cancel sll.
        go.
        {
          unfolds.
          do 6 eexists.
          splits.
          go.
          go.
          go.
          go.
          go.
          go.
          go.
          splits.
          go.
          go.
          go.
          go.
          left; auto.
          repeat tri_exists_and_solver1.
          go.
          rewrite (H58 (eq_refl ($ OS_STAT_RDY))).
          reflexivity.
        }
        eexists; go.
        {
          unfolds in H6.
          simpljoin.
          mttac R_Prio_No_Dup
            ltac: (fun H => clear - tcbmapleft_join_hyp H; rename H into Hnd).
          (* clear -tcbmapleft_join_hyp H104. *)
          unfolds.
          unfolds in tcbmapleft_join_hyp.
          intro.
          simpljoin.

          unfolds in Hnd.
          assert (x0 <> (cur_tcb_blk, Int.zero)).
          {
            intro.
            subst.
            (* ** ac:         SearchAbout join. *)
            (* ** ac:         SearchAbout TcbMod.join. *)
            eapply TcbMod.map_join_get_some .
            
            auto.
            eauto.
            2: exact H.
            instantiate (1:=(v'40, x)).
            unfold get in *; simpl in *.
            unfold sig in *; simpl in *.
            eapply TcbMod.get_a_sig_a.
            go.
          }
          unfold join, sig, get in *; simpl in *.
          assert (TcbMod.get tcbmap x0 = Some (v'40, x1) ) by go.
          assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some (v'40, x) ) by go.
          lets bb: Hnd H0 H1 H2.
          apply bb.
          reflexivity.        
        }
        go.
      }
      
      2: go.
      go.
      go.
      go.
      go.
      go.
      go.

      {
        eapply join_merge_disj; eauto.
        apply disj_sym; auto.
      }
      {
        eapply join_merge_disj; eauto.
        apply disj_sym; auto.        
      }
      { (* objref_distinct *) 
        auto.
      }
      { 
        eapply objdel_nodup_tskdel_preserve; eauto.
      }
      {
        eapply objcre_nodup_tskdel_preserve; eauto.
      }
      {
        assert (Hjol':
                 join (sig (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal)) (merge v'27 v'35)
                  (set v'12 (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in Hjoml.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (cur_tcb_blk, Int.zero) Vnull) (merge v'34 v'36)
                   (set v'13 (cur_tcb_blk, Int.zero) Vnull)).  
        {
          unfolds in Hjomp.
          eapply join_sig_set; eauto.          
        }
        clear Hjoml Hjomp.
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(cur_tcb_blk, Int.zero)) in H95. 
        eapply obj_aux_p_tsk_del_preserve; eauto.         
      }

      { reflexivity. }

      {
        splits.
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None)
                  (v'8 ++
                     (Vptr (cur_tcb_blk, Int.zero)
                        :: v'6
                        :: x11
                        :: x8
                        :: Vint32 i20
                        :: Vint32 i19
                        :: Vint32 i18
                        :: Vint32 i17
                        :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil)
                     :: nil) ) as hell.
        {
          change ((fun x => list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) x)
                    (v'8 ++
                       (Vptr (cur_tcb_blk, Int.zero)
                          :: v'6
                          :: x11
                          :: x8
                          :: Vint32 i20
                          :: Vint32 i19
                          :: Vint32 i18
                          :: Vint32 i17
                          :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil)
                       :: nil)).
          
          rewrite <- H67. 
          
          eapply TCBLP_imply_nextnotnull_list.
          exact H23.
          
          rewrite H67.
          
          rewrite get_last_tcb_ptr_appsig.
          reflexivity.
        }

        (* here *)
        rewrite ptr_in_tcblist_app.
        (* 2: simpl; auto. *)
        intro.
        destruct H109.
        eapply ptr_in_tcblist_last_ir in H109.
        gen H109.
        eapply distinct_is_unique_first.
        exact hell.
        
        eapply  TCBLP_imply_dictinct_list .
        rewrite <- H67.
        exact H19.
        
        rewrite get_last_tcb_ptr_appsig.
        reflexivity.
        
        (* simpl in H131. *)
        (* exact H131. *)
        rewrite get_last_tcb_ptr_appsig in H109.
        simpl (val_inj (Some (Vptr (next_tcb_block, Int.zero)))) in H109. 

        eapply ptr_in_tcblist_change_first in H109.
        gen H109.
        
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        3: { exact H19. }
        2: go.
        rewrite H67.
        exact hell.
        rewrite H67.
        rewrite get_last_tcb_ptr_appsig.
        reflexivity.
        rewrite list_all_P_app.
        rewrite list_all_P_app in hell.
        simpljoin.
        splits; auto.
        simpl.
        split; auto.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        eauto.        
      }

      {
         eapply TCBList_merge_prop.
         instantiate (2 := v'10).
         instantiate (1 := x12).

         eapply some_join_lemma0; eauto.
         exact H11.
         exact tcbmapleft_join_hyp.
         rewrite app_last.
         simpl.
         go.

         2: {

           eapply  tcblist_p_hold_for_del_a_tcb_at_head .
           lia.

           2:go.
           2:go.
           2: exact H11.
           2: exact backup.
           unfolds in H6.
           simpljoin.
           clear -H110 H22.
           eapply R_Prio_No_Dup_hold_for_subset.
           apply TcbMod.join_comm; eauto.
           eauto.
         }

         Require Import task_pure.
         eapply update_rtbl_tcblist_hold.

         lia.
         unfold nat_of_Z; eapply nv'2nv.
         exact H54.
         intro; tryfalse.
         intros.
        
         unfolds in H6.
         simpljoin.
         clear -H22 H11 H111 H109.
         eapply H111.
         instantiate (2 := tid).
         instantiate (1 := (cur_tcb_blk, Int.zero)).
         intro; subst tid.
         eapply TcbMod.map_join_get_some.
         auto.
         exact H22.
         unfold TcbJoin in H11.
         unfold join,sig,get in H11; simpl in H11.
         go.
        
         unfold TcbJoin in H11.
         unfold join,sig,get in H11; simpl in H11.
         go.
        
         unfold TcbJoin in H11.
         unfold join,sig,get in H11; simpl in H11.
         unfold get; simpl.
         go.
         unfold TcbJoin in H11.
         unfold join,sig,get in H11; simpl in H11.
         unfold get; simpl.
         go.

         eapply TCBList_P_hold_for_last_change.
         rewrite H67 in H23.
         exact H23.
      }

      split.
      assumption.
      eapply (H62 _ H49).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      { (* r_priotbl_p hold for deleting a tcb *)
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }      

      { (* rl_rtbl_ptbl_p hold for deleting a tcb *)
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        lia.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.        
      }

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.

      {
        assert (~ exists ecbid, x = wait ecbid).
        {
          intros.
          intro.
          simpljoin.
          
          eapply lowready_not_wait4ecb.
          lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
          subst x23.
          eauto.
          eauto.
        }
        eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }

      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
        intros.
        intro.
        simpljoin.
        
        eapply lowready_not_wait4ecb.
        lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
        subst x23.
        eauto.
        eauto.
      }

      splits; go.
      unfolds; auto.
      go.
      unfolds. left; auto.
      unfolds. left; auto.
      go.
      
      (* OS_Sched (­);ₛ *)
      (* RETURN ′ OS_NO_ERR *) 
      hoare forward.
      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      linv_solver.
      linv_solver.

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      {
        inverts H108.
        eauto.
      }
      inverts H108.
      reflexivity.
    }

    (* delete not current *)
    {
      eapply backward_rule1. 
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'40 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [empisr, false, nil, (true::nil)] **
                           A_dom_lenv
                           ((prio, Int8u)
                              :: (ptr, OS_EVENT ∗)
                              :: (ptcb, OS_TCB ∗)
                              :: (os_code_defs.x, OS_TCB ∗) :: nil) **
                           GV OSTCBFreeList @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
                           LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
                           Astruct (todelblock, Int.zero) OS_TCB_flag
                           (v'18
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: Vnull
                              :: x20
                              :: V$ 0
                              :: V$ OS_STAT_RDY
                              :: Vint32 v'40
                              :: Vint32 (v'40&ᵢ$ 7)
                              :: Vint32 (v'40 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil) **
                           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
                           Astruct (next_tcb_block, Int.zero) OS_TCB_flag
                           (v'0
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: x10
                              :: x9
                              :: Vint32 i12
                              :: Vint32 i11
                              :: Vint32 i10
                              :: Vint32 i9
                              :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil) **
                           Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
                           (Vptr (next_tcb_block, Int.zero)
                              :: v'6
                              :: x11
                              :: x8
                              :: Vint32 i20
                              :: Vint32 i19
                              :: Vint32 i18
                              :: Vint32 i17
                              :: Vint32 i16 :: Vint32 i15 :: Vint32 i14 :: nil) **
                           dllseg v'7 Vnull v'6 (Vptr (prev_tcb_block, Int.zero)) v'8 OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           dllseg v'0 (Vptr (next_tcb_block, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                           (update_nth_val (Z.to_nat (Int.unsigned v'40)) priotbl Vnull) **
                           PV vhold @ Int8u |-> v' **
                           HECBList v'14 **
                           (* HTCBList tcbmap ** *)
                           HTime v'16 **
                           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                           LV ptr @ OS_EVENT ∗ |-> Vnull **
                           GV OSRdyGrp @ Int8u |-> Vint32 v'37 **
                           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'40 >>ᵢ $ 3))) v'26
                              (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'40&ᵢ$ 7))))))) **
                           GV OSTCBList @ OS_TCB ∗ |-> v'7 **
                           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                           (* Aie false ** *)
                           (* Ais nil ** *)
                           (* Acs (true :: nil) ** *)
                           (* Aisr empisr ** *)
                           AECBList v'5 v'4 v'14 tcbmap **
                           tcbdllflag v'7
                           ((v :: l1') ++
                              (Vptr (next_tcb_block, Int.zero)
                                 :: Vptr (prev_tcb_block, Int.zero)
                                 :: Vnull
                                 :: x20
                                 :: Vint32 i13
                                 :: V$ OS_STAT_RDY
                                 :: Vint32 v'40
                                 :: Vint32 (v'40&ᵢ$ 7)
                                 :: Vint32 (v'40 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                              :: (v'0
                                    :: Vptr (todelblock, Int.zero)
                                    :: x10
                                    :: x9
                                    :: Vint32 i12
                                    :: Vint32 i11
                                    :: Vint32 i10
                                    :: Vint32 i9
                                    :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
                              :: l2') **
                           G& OSPlaceHolder @ Int8u == vhold **
                           AOBJ v'21 v'22 v'14 vhold v'7
                           ((v :: l1') ++
                              (Vptr (next_tcb_block, Int.zero)
                                 :: Vptr (prev_tcb_block, Int.zero)
                                 :: Vnull
                                 :: x20
                                 :: Vint32 i13
                                 :: V$ OS_STAT_RDY
                                 :: Vint32 v'40
                                 :: Vint32 (v'40&ᵢ$ 7)
                                 :: Vint32 (v'40 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3)) :: nil)
                              :: (v'0
                                    :: Vptr (todelblock, Int.zero)
                                    :: x10
                                    :: x9
                                    :: Vint32 i12
                                    :: Vint32 i11
                                    :: Vint32 i10
                                    :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: Vint32 i :: nil)
                              :: l2') v'20 v'3 **
                           (* A_isr_is_prop ** *)
                           p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
                           (* LV self @ Int8u |-> (V$ 0) ** *)
                           AOSEventFreeList v'20 v'3 **
                           (* AOSQFreeList v'4 ** *)
                           (* AOSQFreeBlk v'5 ** *)
                           AOSMapTbl **
                           AOSUnMapTbl **
                           AOSIntNesting **
                           sll v'18 v'19 OS_TCB_flag V_OSTCBNext **
                           sllfreeflag v'18 v'19 **
                           AOSTime (Vint32 v'16) **
                           AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'40)).
      clear.
      intro; intros.
      sep_lifts_trms (Aisr, Ais).
      (* sep lifts (4:: 6::nil)%nat.  *)
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.

      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'40, x) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in *; simpl in *.
        unfold get, sig, join in *; simpl in *.
        go.
      }

      destruct H69 as (tcbmap_left & tcbmapleft_join_hyp).

      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.

      (* goodlinv *)
      go.
      (* unfold AEventData. *)
      (* destruct x22; go. *)
      (* unfold p_local. *)
      (* unfold CurTid; unfold LINV. *)
      (* unfold OSLInv. *)
      (* go. *)
      exact tcbmapleft_join_hyp.
      clear -H3; unfolds in H3.
      unfolds.
      simpljoin.
      eauto.
      intro; tryfalse.
      intro; intros.
      split.
      sep_get_rv.
      get_hsat Hs.
      unfold p_local in Hs.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      hoare_lifts_trms_pre tcbdllflag.
      (* hoare lift 28%nat pre. *)
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      subst v'1. 
      inverts H97.
      rewrite H67.      

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (todelblock, Int.zero)
                                                                :: v'6
                                                                :: x11
                                                                :: x8
                                                                :: Vint32 i20
                                                                :: Vint32 i19
                                                                :: Vint32 i18
                                                                :: Vint32 i17
                                                                :: Vint32 i16
                                                                :: Vint32 i15 :: Vint32 i14 :: nil) = Some (Vptr v'12) ).
      {
        eapply dllsegflag_last_next_is_endstnl.
        instantiate (4 := s0).
        sep cancel 5%nat 1%nat.
        eauto.
      }
      
      hoare_split_pure_all.
      inverts H69.

      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24) ) in Hs.
      eauto.

      hoare_lifts_trms_pre Aop.
      (* hoare lift 5%nat pre. *)
      eapply seq_rule.
      eapply assign_rule'.

      2: {
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {        
          sep cancel 15%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      }
      eapply eq_int; auto.

      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.
      get_hsat Hs.
      sep_lifts_trms_in Hs OSLInv.
      (* sep lift 30%nat in Hs.  *)
      unfold OSLInv in Hs.
      sep normal in Hs.
      sep destruct Hs.
      sep split in Hs.
      unfold init_lg in H69; destruct H69.
      inverts H69.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.      
      sep auto.

      simpl; auto.
      splits; eauto.
      unfolds; auto.
      unfolds. left; auto.
      unfolds. left; auto.

      (* ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ *)
      unfold AOBJ. 
      unfold tcbllsegobjaux.
      hoare unfold.
      eapply backward_rule1.
      introv Hs.
      sep_lifts_trms_in Hs llsegobjaux.
      eapply tcbllsegobjaux_split3_join2_frm in Hs; eauto.      
      hoare unfold.
      
      hoare_assert_pure (v'43 = (todelblock, Int.zero)).
      {
        get_hsat Hs.
        apply llsegobjaux_tn_eq in Hs.
        simpl in Hs. inverts Hs.
        auto.
      }
      hoare_split_pure_all.
      subst v'43.
      unfold objaux_node.
      hoare unfold.      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 25) ) in Hs.
      eauto.

      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

      2: { 
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          simpl fst. simpl snd.
          sep cancel 20%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      } 
      eapply eq_int; auto.

      introv Hs.
      sep normal in Hs.
      unfold p_local.
      unfold LINV, OSLInv.
      sep_lifts_trms_in Hs OSLInv.
      unfold OSLInv in Hs.
      sep pauto.

      (* ptcb ′ .. __OSTskPtr =ₑ NULL;ₛ *)
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.      
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 26) ) in Hs.
      eauto.

      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

      2: { 
        intro; intros.
        split.
        eapply field_asrt_impl.
        3: {
          simpl fst. simpl snd.
          sep cancel 19%nat 1%nat.
          eauto.
        }
        reflexivity.
        reflexivity.
        sep get rv.
      } 
      eapply eq_tnull; auto.
      left; eexists; eauto.

      introv Hs.
      sep normal in Hs.
      unfold p_local.
      unfold LINV, OSLInv.
      sep_lifts_trms_in Hs OSLInv.
      unfold OSLInv in Hs.
      sep pauto.

      (* EXIT_CRITICAL;ₛ *)
      (* OS_Sched (­);ₛ       *)
      assert (Hdjl: disjoint v'35 v'27).
      {
        apply join_comm in H105.
        eapply join_join_disj_r; eauto.
      }
      assert (Hdjp: disjoint v'36 v'34).
      {
        apply join_comm in H106.
        eapply join_join_disj_r; eauto.
      }
      assert (Hjoml: TcbJoin (todelblock, Int.zero) (Vint32 i21) (merge v'27 v'35) v'13).
      {
        apply join_comm in H105.
        unfold TcbJoin.
        asserts_rewrite (merge v'27 v'35 = merge v'35 v'27).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }
      assert (Hjomp: TcbJoin (todelblock, Int.zero) v'24 (merge v'34 v'36) v'15).
      {
        apply join_comm in H106.
        unfold TcbJoin.
        asserts_rewrite (merge v'34 v'36 = merge v'36 v'34).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }

      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      (* sep lifts (8::10::nil)%nat in H101. *)
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *)
      eapply seq_rule.

      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local.
      sep pauto.
      unfold LINV.
      sep pauto.
      sep cancel OSLInv.
      eapply poi_OSINV_imply_OSInv.
      unfold poi_OSINV.
      sep pauto.
      sep cancel AOSEventFreeList.
      (* sep cancel AOSQFreeList. *)
      (* sep cancel AOSQFreeBlk. *)
      get_hsat Hs.
      unfold AECBList in Hs.
      unfold AECBList. 
      instantiate (14 := v'5).
      instantiate (13 := v'4).      
      sep pauto.

      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel OSPlaceHolder.
      (* sep cancel 20%nat 2%nat. *)
      sep cancel (Aptrmapsto vhold_addr).
      (* sep cancel 14%nat 1%nat. *)
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.      
      instantiate (4 := (
                         (v'8 ++
                            (Vptr (next_tcb_block, Int.zero)
                               :: v'6
                               :: x11
                               :: x8
                               :: Vint32 i20
                               :: Vint32 i19
                               :: Vint32 i18
                               :: Vint32 i17
                               :: Vint32 i16
                               :: Vint32 i15 :: Vint32 i14 :: nil)
                            :: nil)  ++
                           (v'23
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: x10
                              :: x9
                              :: Vint32 i12
                              :: Vint32 i11
                              :: Vint32 i10
                              :: Vint32 i9
                              :: Vint32 i8
                              :: Vint32 i7 :: Vint32 i :: nil) 
                           
                           :: l2')).
      
      sep_lifts_trms AOBJ.
      unfold AOBJ.
      sep normal.
      exists (merge v'27 v'35).
      exists (merge v'34 v'36).
      sep cancel (Aabsdata absobjsid).
      sep cancel AObjs.
      sep split.

      unfold tcbllsegobjaux.
      eapply llsegobjaux_merge2_frm; eauto.
      sep_lifts_skp_in Hs (llsegobjaux, _N_ 0).
      eapply llsegobjaux_update_tn; eauto.
      sep cancel llsegobjaux.
      2: {
        simpl. eauto.
      }
      sep_lifts_skp_in Hs (llsegobjaux, _N_ 0).
      eapply llsegobjaux_update_prev; eauto.
      sep cancel llsegobjaux.
      2: {
        simpl. eauto.
      }

      unfold tcbdllseg.
      unfold tcbdllflag.
      unfold1 dllsegflag.
      unfold1 dllseg.
      unfold node.
      sep pauto.

      eapply dllseg_is_poi.
      eapply split_poillseg.
      sep eexists.
      eapply split_poillseg.
      sep eexists.
      rewrite <- dllseg_is_poi.
      sep lift 2%nat.
      rewrite <- dllseg_is_poi.
      sep lift 3%nat.
      rewrite <- dllseg_is_poi.
      unfold1 dllseg.
      unfold node.
      sep normal.
      sep eexists.
      instantiate (22 := prev_tcb_block).
      instantiate (4 := Vptr (prev_tcb_block, Int.zero)).
      instantiate (4 := v'6).
      instantiate (15 := Vptr (next_tcb_block, Int.zero)).
      instantiate (4 := Vptr (next_tcb_block, Int.zero)).
      instantiate (6 := Vptr (prev_tcb_block, Int.zero)).
      instantiate (7 := next_tcb_block).
      
      sep pauto.
      sep_lifts_skp_in Hs (dllseg, _N_ 1).
      sep cancel 1%nat 1%nat.
      sep cancel dllseg.

      sep_lifts_skp_in Hs (dllsegflag, _N_ 1).
      (* sep lift 4%nat in H101. *)
      rewrite dllsegflag_is_poi in Hs.
      apply split_poillseg in Hs.
      sep destruct Hs.
      apply dllsegflag_is_poi.
      apply split_poillseg.
      sep eexists.
      apply split_poillseg.
      sep eexists.
      sep pauto.
      sep cancel 1%nat 1%nat.
      unfold1 @poi_llseg in *.
      sep normal in Hs; sep destruct Hs.
      sep normal; sep eexists.
      instantiate (5 := Vptr (next_tcb_block, Int.zero)).
      sep pauto.
      2: go.
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      (* instantiate (x1 := x14). *)
      sep cancel 1%nat 2%nat.
      sep cancel 4%nat 1%nat.      

      {
        (* freelist *)
        unfold AOSTCBFreeList'.
        sep pauto.
        eapply intro_or_l. 
        unfold TCBFree_Not_Eq.
        sep pauto.
        instantiate ( 2 := (
                            (v'18
                               :: Vptr (prev_tcb_block, Int.zero)
                               :: Vnull
                               :: x20
                               :: V$ 0
                               :: V$ OS_STAT_RDY
                               :: Vint32 v'40
                               :: Vint32 (v'40&ᵢ$ 7)
                               :: Vint32 (v'40 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'40&ᵢ$ 7))
                               :: Vint32 ($ 1<<ᵢ(v'40 >>ᵢ $ 3))
                               :: nil) :: v'19
                    )).
        unfold1 sll.
        unfold1 sllfreeflag.
        unfold1 sllseg.
        unfold1 sllsegfreeflag.
        
        sep pauto.
        unfold node.
        unfold sll, sllfreeflag in Hs.
        sep pauto.
        sep cancel sllsegfreeflag.
        sep cancel sllseg.
        sep cancel Astruct.
        eauto.      
        go.
        eapply isptr_is_definitely_ptr.
        eapply sll_head_isptr.
        instantiate (5:=s).
        unfold sll.
        sep cancel sllseg.
        go.
        go.
        
        go.
        intro; tryfalse.
      }

      go.
      go.
      go.

      {
        eapply join_merge_disj; eauto.
        apply disj_sym; auto.
      }
      {
        eapply join_merge_disj; eauto.
        apply disj_sym; auto.        
      }
      { (* objref_distinct *) 
        auto.
      }
      { 
        eapply objdel_nodup_tskdel_preserve; eauto.
      }
      {
        eapply objcre_nodup_tskdel_preserve; eauto.
      }
      {
        assert (Hjol':
                 join (sig (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal)) (merge v'27 v'35)
                  (set v'13 (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in Hjoml.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (todelblock, Int.zero) Vnull) (merge v'34 v'36)
                   (set v'15 (todelblock, Int.zero) Vnull)).  
        {
          unfolds in Hjomp.
          eapply join_sig_set; eauto.          
        }
        clear Hjoml Hjomp.
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(todelblock, Int.zero)) in H96. 
        eapply obj_aux_p_tsk_del_preserve; eauto.         
      }

      {
        reflexivity.
      }
      intro; tryfalse.

      { (* tcblist_p hold for deleting a tcb *)
        eapply TCBList_merge_prop.
        instantiate (2 := v'10).
        instantiate (1 := x12).

        eapply some_join_lemma0; eauto.
        exact H11.
        exact tcbmapleft_join_hyp.
        
        rewrite app_last.
        simpl.
        go.

        2: {
          eapply  tcblist_p_hold_for_del_a_tcb_at_head.
          lia.
          
          2:go.
          2:go.
          2: exact H11.
          2: exact backup.
          unfolds in H6.
          simpljoin.
          clear -H110 H22.
          eapply R_Prio_No_Dup_hold_for_subset.
          apply TcbMod.join_comm; eauto.
          eauto.
        }
        
        eapply update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        exact H54.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H22 H11 H111 H109.
        eapply H111.
        instantiate (2 := tid).
        instantiate (1 := (todelblock, Int.zero)).
        intro; subst tid.
        eapply TcbMod.map_join_get_some.
        auto.
        exact H22.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        go.
        
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        unfold TcbJoin in H11.
        unfold join,sig,get in H11; simpl in H11.
        unfold get; simpl.
        go.
        eapply TCBList_P_hold_for_last_change.
        rewrite H67 in H23.
        exact H23.
      }      

      {
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None)
                  (v'8 ++
                     (Vptr (todelblock, Int.zero)
                        :: v'6
                        :: x11
                        :: x8
                        :: Vint32 i20
                        :: Vint32 i19
                        :: Vint32 i18
                        :: Vint32 i17
                        :: Vint32 i16
                        :: Vint32 i15 :: Vint32 i14 :: nil) :: nil
               )).
        {          
          eapply TCBLP_imply_nextnotnull_list.
          rewrite H67 in H23.
          exact H23.
          rewrite  get_last_tcb_ptr_appsig.
          eauto.
        }
 
        eapply  ptr_in_tcblist_app in H18.
        destruct H18.
        apply  ptr_in_tcblist_app.

        2: left; eapply ptr_in_tcblist_last_ir.
        apply  list_all_P_app.
        apply  list_all_P_app in H109.
        simpljoin.
        splits; auto.
        simpl; go.
        rewrite H67 in H18; exact H18.
        
        apply  ptr_in_tcblist_app.

        apply  list_all_P_app.
        apply  list_all_P_app in H109.
        simpljoin.
        splits; auto.
        simpl; go.

        right.
        
        rewrite          get_last_tcb_ptr_appsig.
        rewrite H67 in H18.
        rewrite          get_last_tcb_ptr_appsig in H18.
        eapply  ptr_in_tcbdllseg_change_head.
        2: { 
          eapply ptr_in_tcbdllseg_not_head. 
          2: exact H18.
          reflexivity.
          simpl; intro; tryfalse.
        }
        reflexivity.
        rewrite H67.
        exact H109.
      }     

      {
        split.
        assumption.
        eapply (H62 _ H49).
        clear -H0; unfold OS_IDLE_PRIO.
        csimpl OS_LOWEST_PRIO.
        int auto.        
      }
      
      { (* r_priotbl_p hold for deleting a tcb *)
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }
      
      { (* rl_rtbl_ptbl_p hold for deleting a tcb *)
        eapply  rtbl_remove_RL_RTbl_PrioTbl_P_hold'.
        lia.
        rewrite Int.repr_unsigned.
        reflexivity.

        rewrite Int.repr_unsigned.
        reflexivity.

        2: assumption.
        unfold nat_of_Z.
        apply nv'2nv.
        
        assumption.
        intro; tryfalse.        
      }

      {
        split.
        eapply array_type_vallist_match_hold.
        assumption.

        rewrite H7.
        clear -H; mauto.
        reflexivity.

        rewrite hoare_assign.update_nth_val_len_eq.
        assumption.        
      }

      {
        assert (~exists ecbid, x = wait ecbid).
        {
          intros.
          intro.
          simpljoin.
          
          eapply lowready_not_wait4ecb.
          lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
          subst x23.
          eauto.
          eauto.
        }

        eapply ECBLP_hold4del_a_tcb_rdy; eauto.
      }      
      
      {
        rewrite <- poi_is_rtep.
        rewrite <- poi_is_rtep in H2.

        eapply poi_RH_T_E_P_hold_for_tcbdel_rdy; eauto.
        intros.
        intro.
        simpljoin.
      
        eapply lowready_not_wait4ecb.
        lets bb: H58 (eq_refl ($ OS_STAT_RDY)).
        subst x23.
        eauto.
        eauto.
      }
      go.

      (* OS_Sched (­);ₛ *)
      (* RETURN ′ OS_NO_ERR       *)
      Ltac sep_semiauto_nosplit2 :=
        intros;
        match goal with
        | H:?s |= _
          |- ?s |= _ =>
            try (solve [ exact H | apply atrue_intro ]); sep normal in H; sep
                                                                            destruct H;  (try progress ssplit_apure_in H); subst;
            repeat match goal with
              | H0 : exists _ , _ |- _ => destruct H0
              | H0 : _ /\ _ |- _ => destruct H0
              end;
            (let Hp := type of H in
             let H' := fresh in
             assert Hp as H' by exact H; clear H; rename H' into H); sep normal;
            sep eexists; ssplit_apure(*;
        match goal with
          | |- _ |= _ => idtac 1;scancel
          | _ => idtac 2;sep_pure
        end*)
        | _ => idtac
        end.
      
      Ltac hoare_call2 :=
        match goal with
        | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
            match find_aop P with 
            | some ?n =>  
                hoare lifts (n::nil)%nat pre; 
                eapply call_rule';
                [intuition eauto | 
                  intros; 
                  do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                  first [apply rvl_nil | simpl;auto] |
                  intros;unfold_spec;sep_semiauto_nosplit2 |
                  idtac |
                  sep_unfold_funpost |
                  sep_unfold_funpre |
                  simpl;eauto
                ] 
            | none _ => idtac
            end
        end.
      
      hoare normal pre; hoare_ex_intro; eapply seq_rule.
      eapply forward_rule2.
      1: hoare_call2.
      7: try sep_unfold_funpost; sep pauto.

      sep cancel Aisr.
      sep cancel Acs.
      sep cancel Ais.
      sep cancel Aie.
      sep cancel Aop.
      sep cancel p_local.
      eauto.
      unfolds; auto.
      go.
      go.
      linv_solver.
      linv_solver.

      (* RETURN ′ OS_NO_ERR *)
      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      {
        inverts H108.
        eauto.
      }
      inverts H108.
      reflexivity.
    }
  }

  Unshelve.
  exact (Afalse).  
  exact cur_tcb_blk.        
  trivial.      
  trivial.    
  exact cur_tcb_blk.
  trivial.      
  trivial.      
  exact cur_tcb_blk.        
  trivial.  
  trivial.
  exact cur_tcb_blk.        
  trivial.
  trivial.

Qed. 

    

      
