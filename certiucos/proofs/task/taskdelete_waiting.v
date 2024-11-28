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

Lemma absimp_taskdel_cler_waitls_bit:
  forall P v3 sch tls els ct els' eid ehb wl tid t,
    can_change_aop P ->
    TcbMod.get tls tid = Some (v3, wait eid) ->
    EcbMod.get els eid = Some (ehb, wl) ->
    els' = set els eid (ehb, (remove_tid tid wl)) ->
    (* Int.lt ($ 63) v3 = false ->
     * (* OSAbstMod.get O abtcblsid = Some (abstcblist tls) -> *)
     * ~ (exists t' st msg, TcbMod.get tls t' = Some (v3, st, msg)) ->
     * (exists t', TcbMod.join tls (TcbMod.sig t' (v3, rdy, Vnull)) tls' )-> *)
    absinfer sch 
      ( <|| taskdel_clear_waitls_bit (|((Vint32 v3) :: nil)|) ;; spec_del (Vint32 v3)  ;;
        isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||>
                    **  HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P)
      ( <|| spec_del (Vint32 v3);;  isched ;; END (Some (Vint32 (Int.repr NO_ERR))) ||> 
                    **  HECBList els' ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
Proof.
  intros.
  infer_part1 0%nat.
  infer_part2.
Qed.

Lemma derive_delself_rule:
  forall pa P prio st tls' tls t e tp  aop r ri sd Spec I isr ie is cs,
    GoodLInvAsrt pa ->
    GoodFrm P ->
    joinsig t (prio, st) tls' tls  ->
    P ==>  Rv e @ tp == Vptr t //\\  CurLINV pa t ->
    InfRules Spec sd pa I r ri 
             (
               <|| spec_del  (Vint32 prio);; aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls) **
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ie, is, cs] ** P
             ) 
             (sprim (stkfree e))
             (
               <|| aop ||>  **
                   Aabsdata abstcblsid (abstcblist tls') ** 
                   Aabsdata curtid (oscurt t) **
                   OS[isr, ie, is, cs]  
                   ** P
             ) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
                    <|| spec_del (Vint32 prio);; aop ||> ** P**
                        HTCBList tls ** HCurTCB t ** OS [isr, ie, is, cs]                         
                  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply delself_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.

Set Printing Depth 999. 

Lemma task_deletewaiting: 
  forall
    (v'26 : vallist)
    (* (v'8 : block) *)
    (v'17 : int32)
    (* (v'27 : addrval) *)
    (v'50 : int32)
    (v'13 : block)
    (v'15 : int32)
    (v'34 : vallist)
    (v'35 : addrval)
    (H1 : Int.unsigned v'50 <= 255)
    (* (v'0 v'1 v'2 v' : val) *)
    (v'2: val)
    (v'3 : list vallist)
    (priotbl : vallist)
    (v'7 : val)
    (l1 l2 : list vallist)
    (ecbmap : EcbMod.map)
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
    (H2 : forall (p : priority) (tid0 : tid) (eid : ecbid),
       get tcbmap tid0 = Some (p, wait eid) ->
       exists n wls, get ecbmap eid = Some (abssem n, wls) /\ In tid0 wls)
    (H52 : poi_R_ET ecbmap tcbmap)
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
    (H0 : Int.unsigned v'50 <> 63)
    (H : Int.unsigned v'50 < 64)
    (hello : taskstatus)
    (kitty : ProtectWrapper (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) = Some (x5, hello)))
    (todelblock : block)
    (H14 : (todelblock, Int.zero) <> vhold)
    (H13 : nth_val' (Z.to_nat (Int.unsigned v'50)) priotbl = Vptr (todelblock, Int.zero))
    (H17 : TcbMod.get tcbmap (todelblock, Int.zero) = Some (v'50, wait (v'13, Int.zero)))
    (l1' l2' : list vallist)
    (x20 : val)
    (i13 : int32)
    (v'9 x33 x34 : val)
    (i i9 i10 i11 i12 i14 i15 : int32)
    (v'12 : val)
    (v'14 : block)
    (H98 : Vptr (v'14, Int.zero) <> Vnull)
    (Heqtcblst : ProtectWrapper
                (l1' ++
                 (Vptr (v'14, Int.zero)
                  :: v'9
                     :: Vptr (v'13, Int.zero)
                        :: x20
                           :: Vint32 i13
                              :: V$ OS_STAT_SEM
                                 :: Vint32 v'50
                                    :: Vint32 (v'50&ᵢ$ 7)
                                       :: Vint32 (v'50 >>ᵢ $ 3)
                                          :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                             :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                 :: (v'12
                     :: Vptr (todelblock, Int.zero)
                        :: x34
                           :: x33
                              :: Vint32 i15
                                 :: Vint32 i14
                                    :: Vint32 i12
                                       :: Vint32 i11
                                          :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
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
           (Vptr (v'14, Int.zero)
            :: v'9
               :: Vptr (v'13, Int.zero)
                  :: x20
                     :: Vint32 i13
                        :: V$ OS_STAT_SEM
                           :: Vint32 v'50
                              :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
           :: (v'12
               :: Vptr (todelblock, Int.zero)
                  :: x34
                     :: x33
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) :: l2'))
    (H19 : TCBList_P v'7
          (l1' ++
           (Vptr (v'14, Int.zero)
            :: v'9
               :: Vptr (v'13, Int.zero)
                  :: x20
                     :: Vint32 i13
                        :: V$ OS_STAT_SEM
                           :: Vint32 v'50
                              :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
           :: (v'12
               :: Vptr (todelblock, Int.zero)
                  :: x34
                     :: x33
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) :: l2')
          v'26 tcbmap)
    (H18 : ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'7
          (l1' ++
           (Vptr (v'14, Int.zero)
            :: v'9
               :: Vptr (v'13, Int.zero)
                  :: x20
                     :: Vint32 i13
                        :: V$ OS_STAT_SEM
                           :: Vint32 v'50
                              :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                    :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                       :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
           :: (v'12
               :: Vptr (todelblock, Int.zero)
                  :: x34
                     :: x33
                        :: Vint32 i15
                           :: Vint32 i14
                              :: Vint32 i12
                                 :: Vint32 i11
                                    :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) :: l2'))
    (v'10 v'11 : TcbMod.map)
    (H22 : TcbMod.join v'10 v'11 tcbmap)
    (H23 : TCBList_P v'7 l1' v'26 v'10)
    (x12 : TcbMod.map)
    (H24 : R_TCB_Status_P
          (Vptr (v'14, Int.zero)
           :: v'9
              :: Vptr (v'13, Int.zero)
                 :: x20
                    :: Vint32 i13
                       :: V$ OS_STAT_SEM
                          :: Vint32 v'50
                             :: Vint32 (v'50&ᵢ$ 7)
                                :: Vint32 (v'50 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                      :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) v'26
          (v'50, wait (v'13, Int.zero)))
    (H11 : TcbJoin (todelblock, Int.zero) (v'50, wait (v'13, Int.zero)) x12 v'11)
    (H51 : 0 <= Int.unsigned v'50)
    (H59 : Int.unsigned v'50 < 64)
    (H58 : $ OS_STAT_SEM = $ OS_STAT_RDY -> Vptr (v'13, Int.zero) = Vnull)
    (H46 : TCBList_P (Vptr (v'14, Int.zero))
          ((v'12
            :: Vptr (todelblock, Int.zero)
               :: x34
                  :: x33
                     :: Vint32 i15
                        :: Vint32 i14
                           :: Vint32 i12
                              :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
           :: l2') v'26 x12)
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
    (H35 : isptr (Vptr (v'14, Int.zero)))
    (H36 : isptr v'9)
    (H37 : isptr (Vptr (v'13, Int.zero)))
    (H38 : isptr x20)
    (H39 : Int.unsigned i13 <= 65535)
    (H40 : Int.unsigned ($ OS_STAT_SEM) <= 255)
    (H41 : Int.unsigned v'50 <= 255)
    (H42 : Int.unsigned (v'50&ᵢ$ 7) <= 255)
    (H43 : Int.unsigned (v'50 >>ᵢ $ 3) <= 255)
    (H44 : Int.unsigned ($ 1<<ᵢ(v'50&ᵢ$ 7)) <= 255)
    (backup : TCBList_P (Vptr (todelblock, Int.zero))
             ((Vptr (v'14, Int.zero)
               :: v'9
                  :: Vptr (v'13, Int.zero)
                     :: x20
                        :: Vint32 i13
                           :: V$ OS_STAT_SEM
                              :: Vint32 v'50
                                 :: Vint32 (v'50&ᵢ$ 7)
                                    :: Vint32 (v'50 >>ᵢ $ 3)
                                       :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                          :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
              :: (v'12
                  :: Vptr (todelblock, Int.zero)
                     :: x34
                        :: x33
                           :: Vint32 i15
                              :: Vint32 i14
                                 :: Vint32 i12
                                    :: Vint32 i11
                                       :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                 :: l2') v'26 v'11)
    (H45 : Int.unsigned ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) <= 255)
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
    (H54 : nth_val' (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26 = Vint32 v'38)
    (H65 : Int.unsigned v'38 <= Byte.max_unsigned)
    (H57 : length
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) =
        ∘ OS_RDY_TBL_SIZE)
    (H60 : rule_type_val_match char_t (Vint32 v'37) = true)
    (H64 : array_type_vallist_match char_t
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))))
    (H63 : prio_not_in_tbl v'50
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))))
    (H62 : forall x : int32,
        prio_in_tbl x v'26 ->
        Int.eq x v'50 = false ->
        prio_in_tbl x
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))))
    (H61 : RL_Tbl_Grp_P
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
             (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7)))))))
          (Vint32 v'37))
    (bbackup : RH_TCBList_ECBList_P ecbmap tcbmap (cur_tcb_blk, Int.zero))
    (x : int32)
    (x11 : list tid)
    (H55 : get ecbmap (v'13, Int.zero) = Some (abssem x, x11))
    (H56 : In (todelblock, Int.zero) x11)
    (v'6 : val)
    (x13 x14 : list os_inv.EventCtr)
    (x21 : EventData)
    (x22 x23 : list EventData) 
    (x28 x29 : val)
    (i7 i8 : int32)
    (v'4 : val)
    (H66 : ECBList_P v'6 Vnull
          (x13 ++
           (Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil, v'34) :: x14)
          (x22 ++ x21 :: x23) ecbmap tcbmap)
    (H67 : isptr v'6)
    (x24 x25 : EcbMod.map)
    (H68 : join x24 x25 ecbmap)
    (H70 : isptr (Vptr (v'13, Int.zero)))
    (H72 : ECBList_P (Vptr (v'13, Int.zero)) Vnull
          ((Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil, v'34) :: x14)
          (x21 :: x23) x25 tcbmap)
    (H71 : ECBList_P v'6 (Vptr (v'13, Int.zero)) x13 x22 x24 tcbmap)
    (H73 : isptr v'4)
    (H75 : array_type_vallist_match char_t v'34)
    (H76 : id_addrval' (Vptr (v'13, Int.zero)) OSEventTbl OS_EVENT = Some v'35)
    (H79 : length v'34 = ∘ OS_EVENT_TBL_SIZE)
    (H78 : RL_Tbl_Grp_P v'34 (Vint32 v'15))
    (H80 : Int.unsigned i7 <= 255)
    (H81 : Int.unsigned v'15 <= 255)
    (H82 : Int.unsigned i8 <= 65535)
    (H83 : isptr x28)
    (H84 : isptr v'4)
    (v'36 v'39 v'41 v'42 v'43 : expr)
    (v'47 v'48 : int32)
    (H74 : ptr ′ .. OSEventGrp
        :: ptr ′ .. OSEventTbl
           :: ptcb ′ .. OSTCBBitX :: ptcb ′ .. OSTCBBitY :: ptcb ′ .. OSTCBY :: nil =
        v'39 :: v'36 :: v'41 :: v'42 :: v'43 :: nil)
    (H77 : nth_val' (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34 = Vint32 v'48)
    (H95 : Int.unsigned v'48 <= Byte.max_unsigned)
    (H86 : length
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
             (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) =
        ∘ OS_RDY_TBL_SIZE)
    (H87 : rule_type_val_match char_t (Vint32 v'47) = true)
    (H88 : RL_Tbl_Grp_P
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
             (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7)))))))
          (Vint32 v'47))
    (H89 : forall x : int32,
        prio_in_tbl x v'34 ->
        Int.eq x v'50 = false ->
        prio_in_tbl x
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
             (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))))
    (H90 : prio_not_in_tbl v'50
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
             (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))))
    (H91 : array_type_vallist_match char_t
          (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
             (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))))
    (v'5 : val)
    (H69 : array_type_vallist_match OS_TCB ∗ priotbl)
    (H97 : length priotbl = 64%nat)
    (H85 : RL_RTbl_PrioTbl_P v'26 priotbl vhold)
    (H96 : R_PrioTbl_P priotbl tcbmap vhold)
    (H99 : isptr v'12)
    (H100 : isptr (Vptr (todelblock, Int.zero)))
    (H101 : isptr x34)
    (H102 : isptr x33)
    (H103 : Int.unsigned i15 <= 65535)
    (H104 : Int.unsigned i14 <= 255)
    (H105 : Int.unsigned i12 <= 255)
    (H106 : Int.unsigned i11 <= 255)
    (H107 : Int.unsigned i10 <= 255)
    (H108 : Int.unsigned i9 <= 255)
    (H109 : Int.unsigned i <= 255), 
  (* ============================ *)
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
  {{Astruct (v'14, Int.zero) OS_TCB_flag
      (v'12
       :: Vptr (todelblock, Int.zero)
          :: x34
             :: x33
                :: Vint32 i15
                   :: Vint32 i14
                      :: Vint32 i12
                         :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
    dllseg v'12 (Vptr (v'14, Int.zero)) v'25 Vnull l2' OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
     <||
    taskdel_clear_waitls_bit (|Vint32 v'50 :: nil|);;
    spec_del (Vint32 v'50);; isched;; END Some (V$ NO_ERR) ||>  **
    A_dom_lenv
      ((prio, char_t)
       :: (ptr, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (os_code_defs.x, OS_TCB ∗) :: nil) **
    GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
      (update_nth_val (Z.to_nat (Int.unsigned v'50)) priotbl Vnull) **
    PV vhold @ char_t |-> v'5 **
    LV ptcb @ OS_TCB ∗ |-> Vptr (todelblock, Int.zero) **
    Astruct (todelblock, Int.zero) OS_TCB_flag
      (Vptr (v'14, Int.zero)
       :: v'9
          :: Vptr (v'13, Int.zero)
             :: x20
                :: V$ 0
                   :: V$ OS_STAT_RDY
                      :: Vint32 v'50
                         :: Vint32 (v'50&ᵢ$ 7)
                            :: Vint32 (v'50 >>ᵢ $ 3)
                               :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                  :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) **
    Aarray v'35 (Tarray char_t ∘ OS_RDY_TBL_SIZE)
      (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
         (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
    PV (v'13, Int.zero +ᵢ  $ 1) @ char_t |-> Vint32 v'47 **
    PV (v'13, Int.zero) @ char_t |-> Vint32 i7 **
    PV (v'13, (Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) @
    Int16u |-> Vint32 i8 **
    PV (v'13,
       ((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ
       $ Z.of_nat (typelen Int16u)) @ (Void) ∗ |-> x28 **
    PV (v'13,
       ((((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ
         $ Z.of_nat (typelen Int16u)) +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
       $ Z.of_nat (typelen (Tarray char_t ∘ OS_EVENT_TBL_SIZE))) @ 
    STRUCT os_event ⋆ |-> v'4 **
    AEventData (Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil) x21 **
    evsllseg v'4 Vnull x14 x23 **
    evsllseg v'6 (Vptr (v'13, Int.zero)) x13 x22 **
    GV OSEventList @ OS_EVENT ∗ |-> v'6 **
    HECBList ecbmap **
    HTCBList tcbmap **
    HTime v'16 **
    HCurTCB (cur_tcb_blk, Int.zero) **
    LV ptr @ OS_EVENT ∗ |-> Vptr (v'13, Int.zero) **
    GV OSRdyGrp @ char_t |-> Vint32 v'37 **
    GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE)
      (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
         (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
    dllseg v'7 Vnull v'9 (Vptr (todelblock, Int.zero)) l1' OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
    GV OSTCBList @ OS_TCB ∗ |-> v'7 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
    Aie false **
    Ais nil **
    Acs (true :: nil) **
    Aisr empisr **
    tcbdllflag v'7
      (l1' ++
       (Vptr (v'14, Int.zero)
        :: v'9
           :: Vptr (v'13, Int.zero)
              :: x20
                 :: Vint32 i13
                    :: V$ OS_STAT_SEM
                       :: Vint32 v'50
                          :: Vint32 (v'50&ᵢ$ 7)
                             :: Vint32 (v'50 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
       :: (v'12
           :: Vptr (todelblock, Int.zero)
              :: x34
                 :: x33
                    :: Vint32 i15
                       :: Vint32 i14
                          :: Vint32 i12
                             :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
          :: l2') **
    G& OSPlaceHolder @ char_t == vhold **
    AOBJ v'21 v'22 ecbmap vhold v'7
      (l1' ++
       (Vptr (v'14, Int.zero)
        :: v'9
           :: Vptr (v'13, Int.zero)
              :: x20
                 :: Vint32 i13
                    :: V$ OS_STAT_SEM
                       :: Vint32 v'50
                          :: Vint32 (v'50&ᵢ$ 7)
                             :: Vint32 (v'50 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
       :: (v'12
           :: Vptr (todelblock, Int.zero)
              :: x34
                 :: x33
                    :: Vint32 i15
                       :: Vint32 i14
                          :: Vint32 i12
                             :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
          :: l2') v'20 v'3 **
    A_isr_is_prop **
    p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
    AOSEventFreeList v'20 v'3 **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSIntNesting **
    AOSTCBFreeList v'18 v'19 **
    AOSTime (Vint32 v'16) **
    AGVars **
    atoy_inv' ** LV os_code_defs.x @ OS_TCB ∗ |-> v'2 ** LV prio @ char_t |-> Vint32 v'50}} 
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
  Set Printing Depth 999.
  hoare forward.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskdel_cler_waitls_bit.
  go.
  exact H17.
  go.
  go.
  go.
  
  destruct l1'.
  hoare_assert_pure (v'9 = Vnull).
  {
    get_hsat Hs.
    unfold1 dllseg in Hs.
    sep normal in Hs.
    sep destruct Hs.
    sep split in Hs.
    
    rewrite H93; reflexivity.
  }

  (* v'9 is null, deleting first tcb node *)
  {
    hoare_split_pure_all.
    subst v'9.

    hoare forward.
    go.

    2:  { 
      hoare_split_pure_all; false.
      clear -H92; simpljoin.
      destruct H92; tryfalse.
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
      clear -H92; destruct H92; tryfalse.
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

    clear H92 H93 H94.

    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto.
    destruct H92.
    (* delete current *) 
    {
      subst todelblock.
      rewrite H17 in kitty.
      eapply backward_rule1.

      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'50 :: nil);;
                       (* taskdel_clear_waitls_bit (|Vint32 v'53 :: nil|);; *)
                           isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
                           (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
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
                              :: Vint32 v'50
                              :: Vint32 (v'50&ᵢ$ 7)
                              :: Vint32 (v'50 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) **
                           GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'14, Int.zero) **
                           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'14, Int.zero) **
                           Astruct (v'14, Int.zero) OS_TCB_flag
                           (v'12
                              :: Vnull
                              :: x34
                              :: x33
                              :: Vint32 i15
                              :: Vint32 i14
                              :: Vint32 i12
                              :: Vint32 i11
                              :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
                           dllseg v'12 (Vptr (v'14, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                           (update_nth_val (Z.to_nat (Int.unsigned v'50)) priotbl Vnull) **
                           PV vhold @ Int8u |-> v'5 **
                           Aarray v'35 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                              (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
                           PV (v'13, Int.zero +ᵢ  $ 1) @ Int8u |-> Vint32 v'47 **
                           PV (v'13, Int.zero) @ Int8u |-> Vint32 i7 ** 
                           PV (v'13,
                             (Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ $ Z.of_nat (typelen Int8u)) @ Int16u |-> Vint32 i8 **
                           PV (v'13,
                             ((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ $ Z.of_nat (typelen Int8u)) +ᵢ  
                             $ Z.of_nat (typelen Int16u)) @ (Void) ∗ |-> x28 ** 
                           PV (v'13,
                             ((((Int.zero +ᵢ  $ Z.of_nat (typelen Int8u)) +ᵢ $ Z.of_nat (typelen Int8u)) +ᵢ  
                           $ Z.of_nat (typelen Int16u)) +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                           $ Z.of_nat (typelen (Tarray Int8u ∘ OS_EVENT_TBL_SIZE))) @ STRUCT os_event ⋆ |-> v'4 ** 
                           AEventData
                           (Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil) x21 ** 
                           evsllseg v'4 Vnull x14 x23 **
                           evsllseg v'6 (Vptr (v'13, Int.zero)) x13 x22 **
                           GV OSEventList @ OS_EVENT ∗ |-> v'6 **
                           HECBList
                           (EcbMod.set ecbmap (v'13, Int.zero) (abssem x, remove_tid (cur_tcb_blk, Int.zero) x11))
                           (* ecbmap *) **
                           (* HTCBList tcbmap ** *)
                           HTime v'16 **
                           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                           LV ptr @ OS_EVENT ∗ |-> Vptr (v'13, Int.zero) **
                           GV OSRdyGrp @ Int8u |-> Vint32 v'37 **
                           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
                              (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
                           dllseg v'7 Vnull Vnull (Vptr (cur_tcb_blk, Int.zero)) nil OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                          (* Aie false ** *)
                          (* Ais nil ** *)
                          (* Acs (true :: nil) ** *)
                          (* Aisr empisr ** *)
                          tcbdllflag v'7
                          (nil ++
                             (Vptr (v'14, Int.zero)
                                :: Vnull
                                :: Vptr (v'13, Int.zero)
                                :: x20
                                :: Vint32 i13
                                :: V$ OS_STAT_SEM
                                :: Vint32 v'50
                                :: Vint32 (v'50&ᵢ$ 7)
                                :: Vint32 (v'50 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                             :: (v'12
                                   :: Vptr (cur_tcb_blk, Int.zero)
                                   :: x34
                                   :: x33
                                   :: Vint32 i15
                                   :: Vint32 i14
                                   :: Vint32 i12
                                   :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                             :: l2') **
                          G& OSPlaceHolder @ Int8u == vhold **
                          AOBJ v'21 v'22 ecbmap vhold v'7
                          (nil ++
                             (Vptr (v'14, Int.zero)
                                :: Vnull
                                :: Vptr (v'13, Int.zero)
                                :: x20
                                :: Vint32 i13
                                :: V$ OS_STAT_SEM
                                :: Vint32 v'50
                                :: Vint32 (v'50&ᵢ$ 7)
                                :: Vint32 (v'50 >>ᵢ $ 3)
                                :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                             :: (v'12
                                   :: Vptr (cur_tcb_blk, Int.zero)
                                   :: x34
                                   :: x33
                                   :: Vint32 i15
                                   :: Vint32 i14
                                   :: Vint32 i12
                                   :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
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
                          AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'50 
                           (* Aisr empisr **
                            * Aie false **
                            * Ais nil **
                            * Acs (true :: nil) ** *)
                  )).                     
                     
      clear.
      intro; intros.
      sep_lifts_trms (Aisr, Ais). 
      (* sep lifts (4:: 6::nil)%nat.  *)
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep cancel AOBJ.
      sep pauto.
      unfold os_task.STKFREE.

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'50, wait (v'13, Int.zero)) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in *; simpl in *.
        unfold get, sig, join in *; simpl in *.
        go.
      }

      destruct H92 as (tcbmap_left & tcbmapleft_join_hyp).
      
      eapply seq_rule.
      eapply  derive_delself_rule.
        
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x21; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.

      (* exact tcbmapleft_join_hyp. *)
      intro; intros.
      split.
      sep_get_rv.
      get_hsat Hs.
      unfold p_local in Hs.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      (* ptcb ′ .. OSTCBflag =ₑ ′ 0;ₛ *)
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
      (* Print Ltac sep_combine. *)
      get_hsat Hs.
      sep combine ( get_off_addr (cur_tcb_blk, Int.zero) ($ 24) ) in Hs.
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
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat. 
      simpl; auto.
      splits; eauto.
      unfolds; auto.      

      (* ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ *)
      unfold AOBJ.
      unfold tcbllsegobjaux.
      remember ((v'8
            :: Vptr (cur_tcb_blk, Int.zero)
               :: x34
                  :: x33
                     :: Vint32 i15
                        :: Vint32 i14
                           :: Vint32 i12
                              :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
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

      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais). 
      (* sep lifts (7::9::nil)%nat in H102. *)
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop. 
      (* hoare lift 4%nat pre. *) 
      eapply seq_rule.

      
      (* EXIT_CRITICAL *) 
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
      (* sep cancel 2%nat 1%nat. *) 
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList. 
      (* sep cancel AOSQFreeList. *)
      (* sep cancel AOSQFreeBlk. *)
      unfold AECBList.      
      
      instantiate (31 := (x13 ++ (Vint32 i7 :: Vint32 v'47 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                                                 (val_inj
                                                    (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7)))))))
                                ) :: x14)).
      instantiate (30 :=(x22 ++ x21 :: x23) ).      
      sep pauto.
      sep cancel (Aabsdata absecblsid).
      sep cancel (Aabsdata abstcblsid).
      sep cancel (Aabsdata ostmid).
      sep cancel (Aabsdata curtid).
      sep cancel AOSMapTbl.
      sep cancel AOSUnMapTbl.
      sep cancel AOSIntNesting.
      sep cancel AGVars.
      sep cancel A_isr_is_prop.
      sep cancel AOSTime.
      sep cancel OSEventList.
      
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H71).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H72).
      
      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.
      sep_lifts_trms AEventData. 
      (* sep lift 2%nat. *) 
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      get_hsat Hs.
      sep_lifts_skp_in Hs (v'47, _N_ 0).
      sep cancel 1%nat 2%nat.
      repeat sep cancel 19%nat 1%nat. 
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel OSPlaceHolder.
      sep cancel (Aptrmapsto vhold_addr). 
      (* sep cancel 16%nat 1%nat. *)
      sep cancel OSTCBPrioTbl.
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      sep_lifts_trms AOSTCBList'.
      unfold AOSTCBList'.
      eapply intro_or_r.
      sep pauto.
      unfold tcblist.
      sep cancel OSTCBList.
      sep cancel OSTCBCur.
      sep cancel OSRdyTbl.
      sep cancel OSRdyGrp.
      sep_lifts_trms AOBJ.
      instantiate ( 7 := nil).
      instantiate ( 5 := l2').
      instantiate ( 5 := (v'8
                            :: Vnull
                            :: x34
                            :: x33
                            :: Vint32 i15
                            :: Vint32 i14
                            :: Vint32 i12
                            :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)). 

      unfold AOBJ.
      sep normal.

      exists v'40. exists v'44.
      sep cancel (Aabsdata absobjsid).
      instantiate (6 := v'21).
      Require Import obj_common_ext.
      eapply AObjs_sem_set_wls'_preserve; eauto.
      sep cancel AObjs. 
      sep split.
      sep_lifts_skp (loc_off, _N_ 0).
      sep cancel 3%nat 1%nat.
      sep_lifts_skp (ptr_off, _N_ 0).
      sep cancel 3%nat 1%nat.
      unfold tcbllsegobjaux.
      sep cancel llsegobjaux.

      unfold TCB_Not_In.
      sep pauto.
      (* unfold tcbdllseg. *)
      eapply tcbdllseg_compose.
      unfold tcbdllseg.
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel 11%nat 1%nat.
      sep cancel 11%nat 1%nat.
      unfold1 tcbdllflag.
      get_hsat Hs.
      unfold tcbdllflag in Hs.
      rewrite app_nil_l.
      unfold1 dllsegflag.
      unfold1 dllsegflag in Hs.
      sep normal in Hs.
      sep pauto.
      (* inverts H126. *)
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
      unfolds.
      {
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
      }      
      eexists; go.
      {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H118.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H118.
        assert (x <> (cur_tcb_blk, Int.zero)).
        {
          intro.
          subst.
          eapply TcbMod.map_join_get_some .
          
          auto.
          eauto.
          2: exact H.
          (* instantiate (1:=(v'43, x, x0)). *)
          unfold get in *; simpl in *.
          unfold sig in *; simpl in *.
          eapply TcbMod.get_a_sig_a.
          go.
        }
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x =Some (v'50, x0) ) by go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some(v'50, wait (v'13, Int.zero))) by go.
        lets bb: H118 H0 H1 H2.
        apply bb.
        reflexivity.
      }

      go.
      go.
      intro;tryfalse.
      go.
      go.      

      {
        split.
        rewrite ptr_in_tcblist_app.
        2: simpl; auto.
        intro.
        destruct H94.
        simpl in H94.
        exact H94.
        simpl (val_inj (get_last_tcb_ptr nil (Vptr (v'14, Int.zero)))) in H94.
        gen H94.
        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        2: 
          instantiate ( 1 :=
                          (Vptr (v'14, Int.zero)
                             :: Vnull
                             :: Vptr (v'13, Int.zero)
                             :: x20
                             :: Vint32 i13
                             :: V$ OS_STAT_SEM
                             :: Vint32 v'50
                             :: Vint32 (v'50&ᵢ$ 7)
                             :: Vint32 (v'50 >>ᵢ $ 3)
                             :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                             :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)).
        2: go.
        instantiate (1 :=  nil).
        simpl; auto.
(* ** ac:         SearchAbout (nil ++ _). *)
        rewrite app_nil_l.

         exact backup.
         simpl.
         auto.
         eauto.
      }

      {
        rewrite app_nil_l.
        rewrite app_nil_l in H19.

        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H19.
        2: exact tcbmapleft_join_hyp.
        unfolds in H96.
        simpljoin; assumption.
      }      

      { (* objref_distinct *)
        auto.
      }

      { (* objdel_nodup *) 
        eapply objdel_nodup_tskdel_preserve; eauto.
      }

      { (* objcre_nodup *) 
        eapply objcre_nodup_tskdel_preserve; eauto. 
      }

      {
        eapply obj_aux_p_sem_set_wls'_preserve; eauto.
        assert (Hjol':
                 join (sig (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal)) v'40
                  (set v' (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in H116.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (cur_tcb_blk, Int.zero) Vnull) v'44 (set v'9 (cur_tcb_blk, Int.zero) Vnull)).
        {
          unfolds in H117.
          eapply join_sig_set; eauto.          
        }
        clear H116 H117.
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(cur_tcb_blk, Int.zero)) in H119. 
        eapply obj_aux_p_tsk_del_preserve; eauto.        
      }
      { (* vhold_addr = ... *)
        reflexivity.
      }

      go.

      split.
      assumption.
      eapply (H62 _ H49).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      go.
      go.

      {
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }      

      {  (* rl_rtbl_ptbl_p hold for deleting a tcb *)
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
      go.
      go.
      go.
      go.
      clear -H87 H94.
      unfolds in H87.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H87.
      lia.
      go.

      { (* ECBList_P *) 
        eapply ECBLP_hold4del_a_tcb; eauto.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.        
      }

      { (* RH_TCBList_ECBList_P *)
        eapply poi_is_rtep.
        {
          eapply poi_RHTEP_hold_for_del_a_tcb. 
          auto.
          go.
          eapply tcbmapleft_join_hyp.
          go.
          clear -H2 H52; unfolds; splits; auto.
        }        
      }

      splits; go.
      unfolds. right; auto.
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

      (* RETURN ′ OS_NO_ERR *)
      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      {
        inverts H94.
        eauto.
      }
      inverts H94.
      reflexivity.      
    }

    (* delete some tcb other than current, at head *)
    {
      eapply backward_rule1.
      intro; intros.
      instantiate ( 1 := (
                          <|| sdel (Vint32 v'50 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                              HTCBList tcbmap **
                              HCurTCB (cur_tcb_blk, Int.zero) **
                              OS [ empisr, false, nil, (true::nil) ] **
                           (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
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
                                 :: Vint32 v'50
                                 :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3))
                                 :: nil) **
                              GV OSTCBList @ OS_TCB ∗ |-> Vptr (v'14, Int.zero) **
                              LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (v'14, Int.zero) **
                              Astruct (v'14, Int.zero) OS_TCB_flag
                              (v'12
                                 :: Vnull
                                 :: x34
                                 :: x33
                                 :: Vint32 i15
                                 :: Vint32 i14
                                 :: Vint32 i12
                                 :: Vint32 i11
                                 :: Vint32 i10
                                 :: Vint32 i9 :: Vint32 i :: nil) **
                              dllseg v'12 (Vptr (v'14, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                              (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                              GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                              (update_nth_val (Z.to_nat (Int.unsigned v'50)) priotbl Vnull) **
                              PV vhold @ Int8u |-> v'5 **
                              Aarray v'35 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                              (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                                 (val_inj
                                    (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
                              PV (v'13, Int.zero +ᵢ  $ 1) @ char_t |-> Vint32 v'47 **
                              PV (v'13, Int.zero) @ char_t |-> Vint32 i7 **
                              PV (v'13,
                                (Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) @
                              Int16u |-> Vint32 i8 **
                              PV (v'13,
                                ((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t))
                                +ᵢ  $ Z.of_nat (typelen Int16u)) @ (Void) ∗ |-> x28 **
                              PV (v'13,
                                ((((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t))
                                  +ᵢ  $ Z.of_nat (typelen Int16u)) +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                                                                                         $ Z.of_nat (typelen (Tarray char_t ∘ OS_EVENT_TBL_SIZE))) @ 
                              STRUCT os_event ⋆ |-> v'4 **
                              AEventData (Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil) x21 **
                              evsllseg v'4 Vnull x14 x23 **
                              evsllseg v'6 (Vptr (v'13, Int.zero)) x13 x22 **
                              GV OSEventList @ OS_EVENT ∗ |-> v'6 ** 
                              HECBList (EcbMod.set ecbmap (v'13, Int.zero)
                                          (abssem x, remove_tid (todelblock, Int.zero) x11)) ** 
                              (* HTCBList tcbmap ** *)
                              HTime v'16 **
                              (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                              LV ptr @ OS_EVENT ∗ |-> Vptr (v'13, Int.zero) **
                              GV OSRdyGrp @ Int8u |-> Vint32 v'37 **
                              GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                              (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
                                 (val_inj
                                    (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
                              dllseg v'7 Vnull Vnull (Vptr (todelblock, Int.zero)) nil
                              OS_TCB_flag (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** 
                              GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                             (* Aie false ** *)
                             (* Ais nil ** *)
                             (* Acs (true :: nil) ** *)
                             (* Aisr empisr ** *) 
                             tcbdllflag v'7
                             (nil ++
                                (Vptr (v'14, Int.zero)
                                   :: Vnull
                                   :: Vptr (v'13, Int.zero)
                                   :: x20
                                   :: Vint32 i13
                                   :: V$ OS_STAT_SEM
                                   :: Vint32 v'50
                                   :: Vint32 (v'50&ᵢ$ 7)
                                   :: Vint32 (v'50 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                                :: (v'12
                                      :: Vptr (todelblock, Int.zero)
                                      :: x34
                                      :: x33
                                      :: Vint32 i15
                                      :: Vint32 i14
                                      :: Vint32 i12
                                      :: Vint32 i11
                                      :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                                :: l2') **
                             G& OSPlaceHolder @ Int8u == vhold **
                             AOBJ v'21 v'22 ecbmap vhold v'7
                             (nil ++
                                (Vptr (v'14, Int.zero)
                                   :: Vnull
                                   :: Vptr (v'13, Int.zero)
                                   :: x20
                                   :: Vint32 i13
                                   :: V$ OS_STAT_SEM
                                   :: Vint32 v'50
                                   :: Vint32 (v'50&ᵢ$ 7)
                                   :: Vint32 (v'50 >>ᵢ $ 3)
                                   :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                   :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                                :: (v'12
                                      :: Vptr (todelblock, Int.zero)
                                      :: x34
                                      :: x33
                                      :: Vint32 i15
                                      :: Vint32 i14
                                      :: Vint32 i12
                                      :: Vint32 i11
                                      :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                                :: l2') v'20 v'3 **
                             (* A_isr_is_prop *) 
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
                             AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'50
                  )).      

      sep_lifts_trms (Aisr, Ais). 
      (* sep lifts (4:: 6::nil)%nat.  *)
      eapply elim_a_isr_is_prop.
      sep cancel Aisr.
      sep cancel Ais.
      sep cancel Acs.
      sep cancel Aie.
      sep pauto.
      unfold os_task.STKFREE.      

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'50, wait (v'13, Int.zero)) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in H11; simpl in H11.
        unfold get, sig, join in H11, H22; simpl in H11, H22.
        go.
      }
      
      destruct H93 as (tcbmap_left & tcbmapleft_join_hyp). 
      rename H92 into not_cur_hyp.

      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.
       (* goodlinv *)
      go.
      unfold AEventData.
      destruct x21; go.
      (* unfold p_local. *)
      (* unfold CurTid; unfold LINV. *)
      (* unfold OSLInv. *)
      (* go. *)
      exact tcbmapleft_join_hyp.
      clear -H3.
      unfolds in H3.
      unfolds.
      simpljoin; eauto.

      clear -not_cur_hyp.
      intro H; inverts H; apply not_cur_hyp; reflexivity.

      
      intro; intros.
      split.
      sep_get_rv.
      get_hsat Hs.
      unfold p_local in Hs.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.

      rewrite app_nil_l.
      unfold1 tcbdllflag.
      unfold1 dllsegflag.
      hoare unfold.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *)
      unfold OSLInv at 3.
      unfold LINV.
      unfold1 dllseg.
      hoare unfold.
      eapply backward_rule1.
      intro; intros.
      (* Print Ltac sep_combine. *)
      get_hsat Hs.
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24) ) in Hs.
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
      
      linv_solver.

      (* ptcb ′ .. __OSTskLoc =ₑ ′ os_code_defs.__Loc_normal;ₛ *)
      unfold AOBJ.
      unfold tcbllsegobjaux.
      remember ((v'9
            :: Vptr (todelblock, Int.zero)
               :: x34
                  :: x33
                     :: Vint32 i15
                        :: Vint32 i14
                           :: Vint32 i12
                              :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
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

      hoare normal pre.
      hoare_ex_intro.
      hoare_lifts_trms_pre Aop.
      eapply seq_rule.
      eapply assign_rule'.

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
      eapply eq_tnull; auto.
      left; eexists; eauto.
      
      intro; intros.
      unfold p_local, OSLInv.
      sep pauto.
      unfold LINV.
      sep pauto.

      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      (* sep lifts (7::9::nil)%nat in H101. *) 
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop.
      (* hoare lift 4%nat pre. *) 
      hoare_split_pure_all.
      rename H92 into Hilg.
      rename H93 into Hgla.

      eapply seq_rule.

      (* EXIT_CRITICAL *) 
      eapply excrit1_rule'_ISnil_ISRemp''.
      intro.
      intros.
      sep cancel atoy_inv'.
      sep cancel Aisr.
      sep cancel Aie.
      sep cancel Ais.
      sep cancel Acs.
      unfold p_local.
      unfold LINV, OSLInv.
      eapply poi_OSINV_imply_OSInv. 
      
      unfold poi_OSINV.  
 
      sep pauto.
      sep cancel AOSEventFreeList.
      (* sep cancel AOSQFreeList. *)
      (* sep cancel AOSQFreeBlk. *) 
      unfold AECBList.
      instantiate (14 := (x13 ++ (Vint32 i7 :: Vint32 v'47 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil, 
                              (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                                 (val_inj
                                    (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7)))))))) :: x14)). 
      instantiate (13 :=(x22 ++ x21 :: x23)).
      (* instantiate (x3 := (x5 ++ (Vint32 i8 :: Vint32 v'53 :: Vint32 i9 :: x29 :: x30 :: v'6 :: nil,
       *                            (update_nth_val (Z.to_nat (Int.unsigned (v'56 >>ᵢ $ 3))) v'40
       *                                            (val_inj
       *                                               (and (Vint32 v'54) (Vint32 (Int.not ($ 1<<ᵢ(v'56&ᵢ$ 7)))))))
       *                           ) :: x15)).
       * instantiate (x2 :=(x23 ++ x22 :: x24) ). *)
      sep pauto. 
      eapply evsllseg_merge. 

      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H71).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H72).
      unfold1 evsllseg .
      sep pauto.
      (* ** ac:       Print AEventNode. *)
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep_lifts_trms AEventData.
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 19%nat 2%nat.
      repeat sep cancel 19%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel OSPlaceHolder.
      sep cancel (Aptrmapsto vhold_addr).
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto. 
      unfold poi_AOSTCBList. 
      
      sep pauto.
      instantiate (4 := (
                          (v'9
                             :: Vnull
                             :: x34
                             :: x33
                             :: Vint32 i15
                             :: Vint32 i14
                             :: Vint32 i12
                             :: Vint32 i11
                             :: Vint32 i10
                             :: Vint32 i9 :: Vint32 i :: nil)
                            :: l2')).

      sep_lifts_trms AOBJ.
      unfold AOBJ.
      sep normal.
      exists v'40. exists v'44. 
      sep cancel (Aabsdata absobjsid).
      instantiate (5 := v'21).
      eapply AObjs_sem_set_wls'_preserve; eauto.      
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
                           :: Vint32 v'50
                           :: Vint32 (v'50&ᵢ$ 7)
                           :: Vint32 (v'50 >>ᵢ $ 3)
                           :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                           :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) :: v'19). 
      unfold sll.
      unfold sllfreeflag.
      unfold1 sllseg.
      unfold1 sllsegfreeflag.
      unfold node.
      get_hsat Hs.
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

      go.
      intro; tryfalse.
      go.
      go.
      go.

      { (* objref_distinct *)
        eauto.
      }

      { (* objdel_nodup *)
        eapply objdel_nodup_tskdel_preserve; eauto.        
      }

      { (* objcre_distinct *)
        eapply objcre_nodup_tskdel_preserve; eauto.  
      }

      { (* OBJ_AUX_P *)
        eapply obj_aux_p_sem_set_wls'_preserve; eauto.
        assert (Hjol':
                 join (sig (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal)) v'40
                   (set v' (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in H114.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (todelblock, Int.zero) Vnull) v'44 (set v'0 (todelblock, Int.zero) Vnull)).  
        {
          unfolds in H115.
          eapply join_sig_set; eauto.          
        }
        clear H114 H115.
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(todelblock, Int.zero)) in H117. 
        eapply obj_aux_p_tsk_del_preserve; eauto.                
      }

      { (* vhold_addr = ... *)
        reflexivity. 
      }

      intro; tryfalse.

      { (* tcblist_p hold for deleting a tcb *)
        rewrite app_nil_l in H19.
        eapply tcblist_p_hold_for_del_a_tcb_at_head.
        lia.
        2:go.
        2:go.
        3: exact H19.
        2: exact tcbmapleft_join_hyp.
        unfolds in H96.
        simpljoin; assumption.
      }

      {
        clear -H18 not_cur_hyp.
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
      go.
      go.
      go.
      go.
      go.
      clear -H87 H116.
      unfolds in H87.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H87.
      lia.
      go.      

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }      

      {
        eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        auto. 
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H52; unfolds; splits; auto.
      }      

      go.
      
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
        inverts H92.
        auto.
      }
      go.
      linv_solver.
      linv_solver.

      (* RETURN  ′ OS_NO_ERR *) 
      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      {
        inverts H93.
        unfolds in H124.
        inverts H124.
        eauto.
      }
      inverts H93.
      reflexivity.
    }
  }

  {
    (* delete some tcb in the middle of the tcblist *)
    
    destruct H36.
    hoare_assert_pure False.
    subst v'9.

    eapply dllseg_tail_not_null.
    instantiate (10:=s0).
    sep pauto.
    get_hsat Hs.
    sep_lifts_skp_in Hs (dllseg, _N_ 1).
    (* sep cancel 26%nat 1%nat. *) 
    eauto.
    hoare unfold.
    tryfalse. 

    destruct H36 as (prev_tcb_ptr & eqprev); subst v'9.     
    
    eapply backward_rule1.
    intro; intros.
    get_hsat Hs.
    sep_lifts_skp_in Hs (dllseg, _N_ 1).
    (* sep lift 26%nat in H42. *)
    rewrite dllseg_split_node_tail in Hs.
    
    eauto.
    unfold node.
    hoare unfold.
    rename v'8 into prev_tcb_block.
    rename v'14 into next_tcb_block.

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
    unfold   AOSTCBFreeList.
    hoare normal pre.
    hoare forward.
    eapply isptr_match_eq_true.
    eapply sll_head_isptr.
    instantiate (5 := s).
    sep cancel sll.
    eauto.    

    hoare forward.
    assert (todelblock = cur_tcb_blk \/ todelblock <> cur_tcb_blk) by tauto. 
    destruct H93. 
    (* delete current *)
    {
      subst todelblock.
      (* unfold get in H16; simpl in H16. *)
      rewrite H17 in kitty.
  
      eapply backward_rule1.
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'50 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **

                           (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
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
                              :: Vint32 v'50
                              :: Vint32 (v'50&ᵢ$ 7)
                              :: Vint32 (v'50 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) ** 
                           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
                           Astruct (next_tcb_block, Int.zero) OS_TCB_flag
                           (v'12
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: x34
                              :: x33
                              :: Vint32 i15
                              :: Vint32 i14
                              :: Vint32 i12
                              :: Vint32 i11
                              :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) ** 
                           Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
                           (Vptr (next_tcb_block, Int.zero)
                              :: v'
                              :: x9
                              :: x8
                              :: Vint32 i22
                              :: Vint32 i21
                              :: Vint32 i20
                              :: Vint32 i19
                              :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) **                           
                           dllseg v'7 Vnull v' (Vptr (prev_tcb_block, Int.zero)) v'0 OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           dllseg v'12 (Vptr (next_tcb_block, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) ** 
                           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                           (update_nth_val (Z.to_nat (Int.unsigned v'50)) priotbl Vnull) **
                           PV vhold @ Int8u |-> v'5 **                           
                           Aarray v'35 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                              (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **

                           PV (v'13, Int.zero +ᵢ  $ 1) @ char_t |-> Vint32 v'47 **
                           PV (v'13, Int.zero) @ char_t |-> Vint32 i7 **
                           PV (v'13, (Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) @
                           Int16u |-> Vint32 i8 **
                           PV (v'13,
                             ((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ
                                 $ Z.of_nat (typelen Int16u)) @ (Void) ∗ |-> x28 **
                           PV (v'13,
                             ((((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ
                                  $ Z.of_nat (typelen Int16u)) +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                  $ Z.of_nat (typelen (Tarray char_t ∘ OS_EVENT_TBL_SIZE))) @ 
                           STRUCT os_event ⋆ |-> v'4 ** 
                           AEventData
                           (Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil) x21 ** 
                           evsllseg v'4 Vnull x14 x23 **
                           evsllseg v'6 (Vptr (v'13, Int.zero)) x13 x22 ** 
                           GV OSEventList @ OS_EVENT ∗ |-> v'6 **
                           (* HECBList ecbmap ** *)
                           HECBList (EcbMod.set ecbmap (v'13, Int.zero)
                                       (abssem x, remove_tid (cur_tcb_blk, Int.zero) x11)) ** 
                           (* HTCBList tcbmap ** *)
                           HTime v'16 **
                           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                           LV ptr @ OS_EVENT ∗ |-> Vptr (v'13, Int.zero) **
                           GV OSRdyGrp @ Int8u |-> Vint32 v'37 **                           
                           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
                              (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **                            
                           GV OSTCBList @ OS_TCB ∗ |-> v'7 **
                           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                           (* Aie false ** *)
                           (* Ais nil ** *)
                           (* Acs (true :: nil) ** *)
                           (* Aisr empisr ** *)
                           tcbdllflag v'7
                           ((v :: l1') ++
                              (Vptr (next_tcb_block, Int.zero)
                                 :: Vptr (prev_tcb_block, Int.zero)
                                 :: Vptr (v'13, Int.zero)
                                 :: x20
                                 :: Vint32 i13
                                 :: V$ OS_STAT_SEM
                                 :: Vint32 v'50
                                 :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                              :: (v'12
                                    :: Vptr (cur_tcb_blk, Int.zero)
                                    :: x34
                                    :: x33
                                    :: Vint32 i15
                                    :: Vint32 i14
                                    :: Vint32 i12
                                    :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                              :: l2') ** 
                           G& OSPlaceHolder @ Int8u == vhold **
                           AOBJ v'21 v'22 ecbmap vhold v'7
                           ((v :: l1') ++
                              (Vptr (next_tcb_block, Int.zero)
                                 :: Vptr (prev_tcb_block, Int.zero)
                                 :: Vptr (v'13, Int.zero)
                                 :: x20
                                 :: Vint32 i13
                                 :: V$ OS_STAT_SEM
                                 :: Vint32 v'50
                                 :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                              :: (v'12
                                    :: Vptr (cur_tcb_blk, Int.zero)
                                    :: x34
                                    :: x33
                                    :: Vint32 i15
                                    :: Vint32 i14
                                    :: Vint32 i12
                                    :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
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
                           AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'50)).

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

      assert (exists mmm, TcbJoin (cur_tcb_blk, Int.zero) (v'50, wait (v'13, Int.zero)) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in *; simpl in *.
        unfold get, sig, join in *; simpl in *.
        go.
      }

      destruct H93 as (tcbmap_left & tcbmapleft_join_hyp). 

      eapply seq_rule.
      eapply derive_delself_rule.
      apply goodlinv.

      (* goodlinv *)
      go.
      unfold AEventData.
      destruct x21; go.
      unfold p_local.
      unfold CurTid; unfold LINV.
      unfold OSLInv.
      go.
      (* exact tcbmapleft_join_hyp. *)
      intro; intros.
      split.
      sep_get_rv.
      get_hsat Hs.
      unfold p_local in Hs.
      unfold CurLINV.
      sep pauto.
      sep cancel LINV.
      simpl; auto 1.
      (* ** ac:       Check dllsegflag_split. *)
      hoare_lifts_trms_pre tcbdllflag. 
      (* hoare lift 36%nat pre. *)
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.
      inverts H121.
      Ltac mttac C tac :=
        match goal with H: context[C] |- _ => (tac H) end.
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      inverts H121.      
      rewrite H92.

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (
                              Vptr (cur_tcb_blk, Int.zero)
                                :: v'
                                :: x9
                                :: x8
                                :: Vint32 i22
                                :: Vint32 i21
                                :: Vint32 i20
                                :: Vint32 i19 :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) = Some (Vptr v'8) ). 
      eapply dllsegflag_last_next_is_endstnl.
      instantiate (4 := s0).
      sep cancel 4%nat 1%nat.
      eauto.

      hoare_split_pure_all.
      inverts H93.

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
      (* sep cancel 52%nat 1%nat. *)
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
      
      hoare_assert_pure (v'53 = (cur_tcb_blk, Int.zero)).
      {
        get_hsat Hs.
        apply llsegobjaux_tn_eq in Hs.
        simpl in Hs. inverts Hs.
        auto.
      }
      hoare_split_pure_all.
      subst v'53.
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
      
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      eapply add_a_isr_is_prop in Hs.
      eauto.
      hoare_lifts_trms_pre Aop. 
      eapply seq_rule.      

      
      (* EXIT_CRITICAL *) 
      assert (Hdjl: disjoint v'45 v'40).
      {
        apply join_comm in H132.
        eapply join_join_disj_r; eauto.
      }
      assert (Hdjp: disjoint v'46 v'44).
      {
        apply join_comm in H133.
        eapply join_join_disj_r; eauto.
      }
      assert (Hjoml: TcbJoin (cur_tcb_blk, Int.zero) (Vint32 i23) (merge v'40 v'45) v'12).
      {
        apply join_comm in H132.
        unfold TcbJoin.
        asserts_rewrite (merge v'40 v'45 = merge v'45 v'40).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }
      assert (Hjomp: TcbJoin (cur_tcb_blk, Int.zero) v'27 (merge v'44 v'46) v'14).
      {
        apply join_comm in H133.
        unfold TcbJoin.
        asserts_rewrite (merge v'44 v'46 = merge v'46 v'44).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }

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
      sep cancel CurTid.
      unfold OSInv.
      sep pauto.
      sep cancel AOSEventFreeList.
      (* sep cancel AOSQFreeList. *)
      (* sep cancel AOSQFreeBlk. *)
      unfold AECBList.
      instantiate (31 := (x13 ++ (Vint32 i7 :: Vint32 v'47 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil,
                              (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                                 (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7)))))))
                              ) :: x14)). 
      instantiate (30 :=(x22 ++ x21 :: x23) ).
      
      sep pauto.
      sep cancel OSEventList.
      sep cancel AOSMapTbl.
      sep cancel AOSUnMapTbl.
      sep cancel AOSIntNesting.
      sep cancel AOSTime.
      sep cancel (Aabsdata ostmid).
      sep cancel (Aabsdata absecblsid).
      sep cancel (Aabsdata abstcblsid).
      sep cancel (Aabsdata curtid).
      sep cancel AGVars.
      sep cancel A_isr_is_prop.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H71).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H72).

      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.

      sep pauto.
      sep_lifts_trms AEventData.
      (* sep lift 2%nat. *)
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 22%nat 2%nat.
      repeat sep cancel 22%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel OSTCBPrioTbl.
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

      sep_lifts_trms AOBJ.
      instantiate (10 := (v'0 ++ 
                            (Vptr (next_tcb_block, Int.zero)
                               :: v'
                               :: x9
                               :: x8
                               :: Vint32 i22
                               :: Vint32 i21
                               :: Vint32 i20
                               :: Vint32 i19
                               :: Vint32 i18
                               :: Vint32 i17 :: Vint32 i16 :: nil)
                            :: nil)). 
      instantiate (8 := l2').
      instantiate (8 := 
                      (v'23
                         :: Vptr (prev_tcb_block, Int.zero)
                         :: x34
                         :: x33
                         :: Vint32 i15
                         :: Vint32 i14
                         :: Vint32 i12
                         :: Vint32 i11
                         :: Vint32 i10
                         :: Vint32 i9 :: Vint32 i :: nil)).      
      
      unfold TCB_Not_In.
      sep pauto.
      sep cancel OSTCBList.
      sep cancel OSTCBCur.
      sep cancel OSRdyGrp.
      sep cancel OSRdyTbl. 
      
      unfold AOBJ.
      sep normal.
      exists (merge v'40 v'45).
      exists (merge v'44 v'46).
      sep cancel (Aabsdata absobjsid).
      eapply AObjs_sem_set_wls'_preserve; eauto.      
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
      unfold1 dllseg.
      unfold node.
      sep pauto.

      sep cancel 12%nat 1%nat.
      sep cancel dllseg.

      unfold tcbdllflag.
      sep_lifts_skp_in Hs (dllsegflag, _N_ 1).
      (* sep lift 4%nat in H130. *)
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

      (* Here sep_pure fails *)
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
    
      sep_semiauto_nosplit2.
      1: scancel.
      2: 
        sep normal in Hs;
        sep destruct Hs;
        sep split in Hs;
        subst.
      
      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      instantiate (5 := x2).
      sep cancel 1%nat 2%nat.
      sep cancel 4%nat 1%nat.
      sep cancel 3%nat 2%nat.
      sep cancel 3%nat 2%nat.

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
      unfolds.      

      {
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
      }      
      eexists; go.
      
      {
        unfolds in H6.
        simpljoin.
        clear -tcbmapleft_join_hyp H137.
        unfolds.
        unfolds in tcbmapleft_join_hyp.
        intro.
        simpljoin.

        unfolds in H137.
        assert (x <> (cur_tcb_blk, Int.zero)).
        {
          intro.
          subst.
          eapply TcbMod.map_join_get_some .
          
          auto.
          eauto.
          2: exact H.
          (* instantiate (1:=(v'43, x, x0)). *)
          unfold get in *; simpl in *.
          unfold sig in *; simpl in *.
          eapply TcbMod.get_a_sig_a.
          go.
        }
        unfold join, sig, get in *; simpl in *.
        assert (TcbMod.get tcbmap x =Some (v'50, x0) ) by go.
        assert (TcbMod.get tcbmap (cur_tcb_blk, Int.zero) =Some(v'50, wait (v'13, Int.zero))) by go.
        lets bb: H137 H0 H1 H2.
        apply bb.
        reflexivity.
      }

      go.
      2: go.
      go.
      go.
      intro; tryfalse.
      go.
      go.
      intro; tryfalse.
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
        eapply obj_aux_p_sem_set_wls'_preserve; eauto.
        assert (Hjol':
                 join (sig (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal)) (merge v'40 v'45)
                   (set v'12 (cur_tcb_blk, Int.zero) (V$ os_code_defs.__Loc_normal))).  
        {
          unfolds in Hjomp.
          eapply join_sig_set; eauto.          
        }
        assert (Hjop':
                 join (sig (cur_tcb_blk, Int.zero) (Vnull)) (merge v'44 v'46)
                  (set v'14 (cur_tcb_blk, Int.zero) (Vnull))).
        {
          unfolds in Hjoml.
          eapply join_sig_set; eauto.
        }
        clear Hjoml Hjomp.        
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(cur_tcb_blk, Int.zero)) in H122. 
        eapply obj_aux_p_tsk_del_preserve; eauto.         
      }

      { (* vhold_addr = ... *)
        reflexivity.
      }

      {
        splits.
        assert(list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) 
                 (v'0 ++
                    (Vptr (cur_tcb_blk, Int.zero)
                       :: v'
                       :: x9
                       :: x8
                       :: Vint32 i22
                       :: Vint32 i21
                       :: Vint32 i20
                       :: Vint32 i19
                       :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
                    :: nil) ) as hell.
        {
          change ((fun x => list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) x)
                    (v'0 ++
                       (Vptr (cur_tcb_blk, Int.zero)
                          :: v'
                          :: x9
                          :: x8
                          :: Vint32 i22
                          :: Vint32 i21
                          :: Vint32 i20
                          :: Vint32 i19
                          :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
                       :: nil)).
          
          rewrite <- H92.
          
          eapply TCBLP_imply_nextnotnull_list. 
          exact H23.
          
          rewrite H92.
          
          rewrite get_last_tcb_ptr_appsig.
          reflexivity.
        }        

        (* here *)
        rewrite ptr_in_tcblist_app.
        (* 2: simpl; auto. *)
        intro.
        destruct H135.
        eapply ptr_in_tcblist_last_ir in H135.
        gen H135.
        eapply distinct_is_unique_first.
        exact hell.
        (* ** ac: SearchAbout get_last_tcb_ptr. *)

         eapply  TCBLP_imply_dictinct_list .
         rewrite <- H92.
         exact H19.

         rewrite get_last_tcb_ptr_appsig.
         reflexivity.
       
        (* simpl in H131. *)
        (* exact H131. *)
         rewrite get_last_tcb_ptr_appsig in H135.
         simpl (val_inj (Some (Vptr (next_tcb_block, Int.zero)))) in H135. 
         (* ** ac:          SearchAbout ptr_in_tcblist. *)

         (* ** ac:         Show. *)
        eapply ptr_in_tcblist_change_first in H135.
        gen H135.

        eapply distinct_is_unique_second.
        3: eapply  TCBLP_imply_dictinct_list .
        3: exact H19.
        2: go.
        rewrite H92.
        exact hell.
        rewrite H92.
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

      {  (* tcblist_p hold for deleting a tcb *)

         eapply TCBList_merge_prop.
         instantiate (2 := v'10).
         instantiate (1 := x12).

         (* ** ac:          SearchAbout TcbMod.join. *)
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
           clear -H136 H22.
           eapply R_Prio_No_Dup_hold_for_subset.
           apply TcbMod.join_comm; eauto.
           eauto.
         }
         
         eapply update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        auto.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H22 H11 H135 H137.
(* ** ac:         Print R_Prio_No_Dup. *)
        eapply H137.
        instantiate (2 := tid).
        instantiate (1 := (cur_tcb_blk, Int.zero)).
        intro; subst tid.
(* ** ac:         SearchAbout TcbMod.join. *)
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

        (* ** ac:         SearchAbout TCBList_P. *)

        eapply TCBList_P_hold_for_last_change.
        rewrite H92 in H23.
        exact H23.     
      }

      {
        go. 
      }
      
      split.
      assumption.
      eapply (H62 _ H49).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      {
        go. 
      }
      {
        go. 
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

      split.
      eapply array_type_vallist_match_hold.
      assumption.

      rewrite H7.
      clear -H; mauto.
      reflexivity.

      rewrite hoare_assign.update_nth_val_len_eq.
      assumption.
      go.
      go.
      go.
      go.
      clear -H87 H135.
      unfolds in H87.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H87.
      lia.
      go.

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }      

      {
        eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        auto.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H52; unfolds; splits; auto.
      }

      splits; go.
      unfolds; auto.
      unfolds. left; auto.
      unfolds. left; auto.
      go.
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

      (* RETURN ′ OS_NO_ERR *) 
      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H135.
      eauto.
      inverts H135.
      reflexivity.      
    }

    { (* delete not current *) 
      eapply backward_rule1.
      
      instantiate (1:=
                     (
                       <|| sdel (Vint32 v'50 :: nil);; isched;; END Some (V$ NO_ERR) ||>  **
                           HTCBList tcbmap **
                           HCurTCB (cur_tcb_blk, Int.zero) **
                           OS [ empisr, false, nil, (true::nil)] **
   (* <|| spec_del (Vint32 v'53);; isched;; END Some (V$ NO_ERR) ||>  ** *)
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
                              :: Vint32 v'50
                              :: Vint32 (v'50&ᵢ$ 7)
                              :: Vint32 (v'50 >>ᵢ $ 3)
                              :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                              :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) ** 
                           LV os_code_defs.x @ OS_TCB ∗ |-> Vptr (next_tcb_block, Int.zero) **
                           Astruct (next_tcb_block, Int.zero) OS_TCB_flag
                           (v'12
                              :: Vptr (prev_tcb_block, Int.zero)
                              :: x34
                              :: x33
                              :: Vint32 i15
                              :: Vint32 i14
                              :: Vint32 i12
                              :: Vint32 i11
                              :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil) **
                           Astruct (prev_tcb_block, Int.zero) OS_TCB_flag
                           (Vptr (next_tcb_block, Int.zero)
                              :: v'
                              :: x9
                              :: x8
                              :: Vint32 i22
                              :: Vint32 i21
                              :: Vint32 i20
                              :: Vint32 i19
                              :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil) **
                           dllseg v'7 Vnull v' (Vptr (prev_tcb_block, Int.zero)) v'0 OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
                           dllseg v'12 (Vptr (next_tcb_block, Int.zero)) v'25 Vnull l2' OS_TCB_flag
                           (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **                           
                           GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64)
                           (update_nth_val (Z.to_nat (Int.unsigned v'50)) priotbl Vnull) **
                           PV vhold @ Int8u |-> v'5 **
                           Aarray v'35 (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                              (val_inj (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **

                           PV (v'13, Int.zero +ᵢ  $ 1) @ char_t |-> Vint32 v'47 **
                           PV (v'13, Int.zero) @ char_t |-> Vint32 i7 **
                           PV (v'13, (Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) @
                           Int16u |-> Vint32 i8 **
                           PV (v'13,
                             ((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ
                                  $ Z.of_nat (typelen Int16u)) @ (Void) ∗ |-> x28 **
                           PV (v'13,
                             ((((Int.zero +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ  $ Z.of_nat (typelen char_t)) +ᵢ
                                  $ Z.of_nat (typelen Int16u)) +ᵢ  $ Z.of_nat (typelen (Void) ∗)) +ᵢ
                                  $ Z.of_nat (typelen (Tarray char_t ∘ OS_EVENT_TBL_SIZE))) @  
                           STRUCT os_event ⋆ |-> v'4 **
                           AEventData (Vint32 i7 :: Vint32 v'15 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil) x21 ** 
                           evsllseg v'4 Vnull x14 x23 **
                           evsllseg v'6 (Vptr (v'13, Int.zero)) x13 x22 ** 
                           GV OSEventList @ OS_EVENT ∗ |-> v'6 **
                           (* HECBList ecbmap ** *)
                           HECBList
                           (EcbMod.set ecbmap (v'13, Int.zero)
                              (abssem x, remove_tid (todelblock, Int.zero) x11)) ** 
                           (* HTCBList tcbmap ** *)
                           HTime v'16 **
                           (* HCurTCB (cur_tcb_blk, Int.zero) ** *)
                           LV ptr @ OS_EVENT ∗ |-> Vptr (v'13, Int.zero) ** 
                           GV OSRdyGrp @ Int8u |-> Vint32 v'37 ** 
                           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE)
                           (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'26
                              (val_inj (and (Vint32 v'38) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7))))))) **
                           GV OSTCBList @ OS_TCB ∗ |-> v'7 **
                           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
                           (* Aie false ** *)
                           (* Ais nil ** *)
                           (* Acs (true :: nil) ** *)
                           (* Aisr empisr ** *) 
                           tcbdllflag v'7
                           ((v :: l1') ++
                              (Vptr (next_tcb_block, Int.zero)
                                 :: Vptr (prev_tcb_block, Int.zero)
                                 :: Vptr (v'13, Int.zero)
                                 :: x20
                                 :: Vint32 i13
                                 :: V$ OS_STAT_SEM
                                 :: Vint32 v'50
                                 :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                              :: (v'12
                                    :: Vptr (todelblock, Int.zero)
                                    :: x34
                                    :: x33
                                    :: Vint32 i15
                                    :: Vint32 i14
                                    :: Vint32 i12
                                    :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                              :: l2') **
                           G& OSPlaceHolder @ Int8u == vhold **
                           AOBJ v'21 v'22 ecbmap vhold v'7
                           ((v :: l1') ++
                              (Vptr (next_tcb_block, Int.zero)
                                 :: Vptr (prev_tcb_block, Int.zero)
                                 :: Vptr (v'13, Int.zero)
                                 :: x20
                                 :: Vint32 i13
                                 :: V$ OS_STAT_SEM
                                 :: Vint32 v'50
                                 :: Vint32 (v'50&ᵢ$ 7)
                                 :: Vint32 (v'50 >>ᵢ $ 3)
                                 :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                                 :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil)
                              :: (v'12
                                    :: Vptr (todelblock, Int.zero)
                                    :: x34
                                    :: x33
                                    :: Vint32 i15
                                    :: Vint32 i14
                                    :: Vint32 i12
                                    :: Vint32 i11 :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
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
                           AGVars ** atoy_inv' ** LV prio @ Int8u |-> Vint32 v'50 )). 

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

      assert (exists mmm, TcbJoin (todelblock, Int.zero) (v'50, wait (v'13, Int.zero)) mmm tcbmap).
      {
        apply tcb_get_join.
        unfold get, sig, join in *; simpl in *.
        unfold get, sig, join in *; simpl in *.
        go.
      }

      destruct H94 as (tcbmap_left & tcbmapleft_join_hyp).

      eapply seq_rule.
      eapply derive_delother_rule.
      apply goodlinv.

      (* goodlinv *)
      go.
      unfold AEventData.
      destruct x21; go.
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
      (* hoare lift 37%nat pre. *) 
      eapply backward_rule1.
      eapply dllsegflag_split.
      hoare_split_pure_all.
      unfold dllsegflag at 2.
      fold dllsegflag .
      hoare_split_pure_all.      

      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      mttac V_OSTCBNext ltac:(fun H=> inverts H).
      inverts H122.
      inverts H124.
      rewrite H92.

      hoare_assert_pure ( (fun vl : vallist => nth_val 0 vl) (Vptr (todelblock, Int.zero)
                                                                :: v'
                                                                :: x9
                                                                :: x8
                                                                :: Vint32 i22
                                                                :: Vint32 i21
                                                                :: Vint32 i20
                                                                :: Vint32 i19
                                                                :: Vint32 i18
                                                                :: Vint32 i17 :: Vint32 i16 :: nil) = Some (Vptr v'9) ).
      {
        eapply dllsegflag_last_next_is_endstnl.
        instantiate (4 := s0).
        sep cancel 5%nat 1%nat.
        eauto.
      }

      hoare_split_pure_all.
      inverts H121.
      
      unfold p_local at 2.
      unfold OSLInv at 3.
      unfold LINV.
      hoare_split_pure_all.
      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep combine ( get_off_addr (todelblock, Int.zero) ($ 24)  ) in Hs.
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
      (* sep lift 39%nat in H133. *) 
      unfold OSLInv in Hs.
      sep normal in Hs.
      sep destruct Hs.
      sep split in Hs.
      unfold init_lg in H121; destruct H121. 
      inverts H121.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep auto.

      simpl; auto.
      splits; eauto.
      unfolds. left; auto.
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
      
      hoare_assert_pure (v'53 = (todelblock, Int.zero)).
      {
        get_hsat Hs.
        apply llsegobjaux_tn_eq in Hs.
        simpl in Hs. inverts Hs.
        auto.
      }
      hoare_split_pure_all.
      subst v'53.
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

      eapply backward_rule1.
      intro; intros.
      get_hsat Hs.
      sep_lifts_trms_in Hs (Aisr, Ais).
      eapply add_a_isr_is_prop in Hs. 
      eauto.
      hoare_lifts_trms_pre Aop. 
      (* hoare lift 4%nat pre. *)
      eapply seq_rule.      

      (* EXIT_CRITICAL *)

      assert (Hdjl: disjoint v'45 v'40).
      {
        apply join_comm in H132.
        eapply join_join_disj_r; eauto.
      }
      assert (Hdjp: disjoint v'46 v'44).
      {
        apply join_comm in H133.
        eapply join_join_disj_r; eauto.
      }
      assert (Hjoml: TcbJoin (todelblock, Int.zero) (Vint32 i23) (merge v'40 v'45) v'14).
      {
        apply join_comm in H132.
        unfold TcbJoin.
        asserts_rewrite (merge v'40 v'45 = merge v'45 v'40).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }
      assert (Hjomp: TcbJoin (todelblock, Int.zero) v'27 (merge v'44 v'46) v'23).
      {
        apply join_comm in H133.
        unfold TcbJoin.
        asserts_rewrite (merge v'44 v'46 = merge v'46 v'44).
        {
          apply perm_map_lemmas_part3.disjoint_merge_comm.
          apply disj_sym; auto.
        }
        eapply join_join_merge23_join; eauto.
      }

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
      unfold AECBList.

      instantiate (14 := (x13 ++ (Vint32 i7 :: Vint32 v'47 :: Vint32 i8 :: x28 :: x29 :: v'4 :: nil,
                                 (update_nth_val (Z.to_nat (Int.unsigned (v'50 >>ᵢ $ 3))) v'34
                                                 (val_inj
                                                    (and (Vint32 v'48) (Vint32 (Int.not ($ 1<<ᵢ(v'50&ᵢ$ 7)))))))
                                ) :: x14)).
      instantiate (13 :=(x22 ++ x21 :: x23) ).

      sep pauto.
      eapply evsllseg_merge.
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H71).
      eapply (ecblistp_length_eq_1 _ _ _ _ _ _ H72). 

      unfold1 evsllseg .
      sep pauto.
      unfold AEventNode.
      sep cancel evsllseg.
      sep cancel evsllseg.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep pauto.
      sep cancel Aarray.      

      sep_lifts_trms AEventData. 
      (* sep lift 2%nat. *) 
      eapply AED_changegrp.
      sep cancel AEventData.
      unfold Astruct.
      unfold OS_EVENT.
      unfold Astruct'.
      sep normal.
      sep cancel 22%nat 2%nat.
      repeat sep cancel 22%nat 1%nat.
      unfold AOSTCBPrioTbl.
      sep pauto.
      sep cancel OSPlaceHolder.
      sep cancel (Aptrmapsto vhold_addr).
      unfold AOSRdyTblGrp.
      unfold AOSRdyTbl.
      unfold AOSRdyGrp.
      sep pauto.
      unfold poi_AOSTCBList.
      
      sep pauto.
      sep_lifts_trms AOBJ.
      instantiate (4 :=
                     (v'0 ++
                        (Vptr (next_tcb_block, Int.zero) 
                           :: v'
                           :: x9
                           :: x8
                           :: Vint32 i22
                           :: Vint32 i21
                           :: Vint32 i20
                           :: Vint32 i19
                           :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
                        :: nil) ++
                       (v'24
                          :: Vptr (prev_tcb_block, Int.zero)
                          :: x34
                          :: x33
                          :: Vint32 i15
                          :: Vint32 i14
                          :: Vint32 i12
                          :: Vint32 i11
                          :: Vint32 i10 :: Vint32 i9 :: Vint32 i :: nil)
                       :: l2'
                       ).

      sep_lifts_trms AOBJ.
      unfold AOBJ.
      sep normal.
      exists (merge v'40 v'45). 
      exists (merge v'44 v'46).
      sep cancel (Aabsdata absobjsid).
      eapply AObjs_sem_set_wls'_preserve; eauto.      
      sep cancel AObjs.
      sep split.

      get_hsat Hs.
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
      sep pauto.
      sep cancel 13%nat 1%nat.
      sep cancel 12%nat 1%nat.
      sep_lifts_skp_in Hs (dllseg, _N_ 1).
      sep cancel 1%nat 1%nat.
      sep cancel dllseg.

      sep_lifts_skp_in Hs (dllsegflag, _N_ 1).
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

      sep_semiauto_nosplit2.
      1: scancel.
      2: sep normal in Hs;
      sep destruct Hs;
      sep split in Hs;
      subst.

      sep lift 2%nat.
      rewrite <- dllsegflag_is_poi.
      sep cancel dllsegflag.
      instantiate (4 := x2).
      sep cancel 1%nat 2%nat.
      sep cancel 4%nat 1%nat.      
      
      (* freelist *)
      unfold AOSTCBFreeList'.
      sep pauto.
      eapply intro_or_l. 
      unfold TCBFree_Not_Eq.
      sep pauto.
      instantiate ( 2 := (
                          v'18
                            :: Vptr (prev_tcb_block, Int.zero)
                            :: Vnull
                            :: x20
                            :: V$ 0
                            :: V$ OS_STAT_RDY
                            :: Vint32 v'50
                            :: Vint32 (v'50&ᵢ$ 7)
                            :: Vint32 (v'50 >>ᵢ $ 3)
                            :: Vint32 ($ 1<<ᵢ(v'50&ᵢ$ 7))
                            :: Vint32 ($ 1<<ᵢ(v'50 >>ᵢ $ 3)) :: nil) :: v'19
                  ).
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
      2:go.
      go.
      go.
      intro; tryfalse.
      intro; tryfalse.
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
        eapply obj_aux_p_sem_set_wls'_preserve; eauto.
        assert (Hjol':
                 join (sig (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal)) (merge v'40 v'45)
                  (set v'14 (todelblock, Int.zero) (V$ os_code_defs.__Loc_normal))).
        {
          unfolds in Hjoml.
          eapply join_sig_set; eauto.
        }
        assert (Hjop':
                 join (sig (todelblock, Int.zero) Vnull) (merge v'44 v'46)
                   (set v'23 (todelblock, Int.zero) Vnull)).  
        {
          unfolds in Hjomp.
          eapply join_sig_set; eauto.          
        }
        clear Hjoml Hjomp.
        eapply obj_aux_p_set_nml_vnull_preserve with (t:=(todelblock, Int.zero)) in H124. 
        eapply obj_aux_p_tsk_del_preserve; eauto.         
      }

      { (* vhold_addr = ... *)
        reflexivity.
      }

      intro; tryfalse.
      {
        (* tcblist_p holds for deleting a tcb *)

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
          clear -H137 H22.
          eapply R_Prio_No_Dup_hold_for_subset.
          apply TcbMod.join_comm; eauto.
          eauto.
        }
        
        eapply update_rtbl_tcblist_hold.

        lia.
        unfold nat_of_Z; eapply nv'2nv.
        auto.
        intro; tryfalse.
        intros.

        unfolds in H6.
        simpljoin.
        clear -H22 H11 H138 H136.
        eapply H138. 
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
        rewrite H92 in H23.
        exact H23.
      }

      { 
        assert (list_all_P (fun x10 : vallist => V_OSTCBNext x10 <> None) (
                    v'0 ++
                      (Vptr (todelblock, Int.zero)
                         :: v'
                         :: x9
                         :: x8
                         :: Vint32 i22
                         :: Vint32 i21
                         :: Vint32 i20
                         :: Vint32 i19
                         :: Vint32 i18 :: Vint32 i17 :: Vint32 i16 :: nil)
                      :: nil
               )).

        eapply TCBLP_imply_nextnotnull_list.
        rewrite H92 in H23.
        exact H23.
        rewrite  get_last_tcb_ptr_appsig.
        eauto.
 
        eapply  ptr_in_tcblist_app in H18.
        destruct H18.
        apply  ptr_in_tcblist_app.

        2: left; eapply ptr_in_tcblist_last_ir.
        apply  list_all_P_app.
        apply  list_all_P_app in H136.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)
        rewrite H92 in H18; exact H18.

        
        apply  ptr_in_tcblist_app.

        apply  list_all_P_app.
        apply  list_all_P_app in H136.
        simpljoin.
        splits; auto.
        simpl; go.
        (* unfold V_OSTCBNext; simpl; intro; tryfalse. *)

        right.
        
        rewrite          get_last_tcb_ptr_appsig.
        rewrite H92 in H18.
        rewrite          get_last_tcb_ptr_appsig in H18.
        eapply  ptr_in_tcbdllseg_change_head.
        2: {
          eapply ptr_in_tcbdllseg_not_head. 
          2: exact H18.
          reflexivity.
          simpl; intro; tryfalse.
        }
        reflexivity.
        rewrite H92.
        exact H136.
      }      

      split.
      assumption.
      eapply (H62 _ H49).
      clear -H0; unfold OS_IDLE_PRIO.
      csimpl OS_LOWEST_PRIO.
      int auto.

      {  (* r_priotbl_p holds for deleting a tcb *)
        eapply  r_priotbl_p_hold_for_del_a_tcb.
        lia.
        assumption.
        eauto 1.

        exact   tcbmapleft_join_hyp .
      }

      {  (* rl_rtbl_ptbl_p holds for deleting a tcb *)
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
      go.
      go.
      go.
      go.
      clear -H87 H136.
      unfolds in H87.
      change Byte.max_unsigned with 255%Z in * .
      math simpl in H87.
      lia.
      go.      

      {
        eapply ECBLP_hold4del_a_tcb; eauto.
        clear -H6; unfolds in H6; tauto.
        clear -H6; unfolds in H6; tauto.
      }      

      {
        eapply poi_is_rtep.
        eapply poi_RHTEP_hold_for_del_a_tcb.
        auto.
        go.
        eapply tcbmapleft_join_hyp.
        go.
        clear -H2 H52; unfolds; splits; auto.
      }

      go.

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
                  intros;unfold_spec(*;sep pauto*) |
                  idtac |
                  sep_unfold_funpost |
                  sep_unfold_funpre |
                  simpl;eauto
                ] 
            | none _ => idtac
            end
        end.
      eapply seq_rule.
      1: hoare_call2.
      sep_semiauto_nosplit2.
      sep pauto.
      2: try sep_unfold_funpost; sep pauto.
      5: sep pauto.
      (*hoare forward.*)

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

      unfold OS_SchedPost.
      unfold OS_SchedPost'.
      unfold getasrt.
      hoare forward.
      inverts H135.
      eauto.
      inverts H135.
      reflexivity.
    }
  }
  
    Unshelve.
    exact (Afalse).

    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).
    exact (V$0).      
    all: exact (V$0).             
      
Qed. 

