Require Import os_code_defs.
Require Import os_ucos_h.

Local Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.


Definition STKINIT (a : expr * expr * expr ) := 
  let ( vt, v3 ) := a in let (v1, v2) := vt in  sprim (stkinit v1 v2 v3). 

Definition OSTaskCreate_impl :=
Int8u ·OSTaskCreate·(⌞task @ Void∗; pdata @ Void∗; prio @ Int8u⌟)··{
       ⌞ err @ Int8u⌟;

       If(prio′ >ₑ ′OS_LOWEST_PRIO) {
           RETURN ′OS_PRIO_INVALID
       };ₛ
           
       ENTER_CRITICAL;ₛ
       If (OSTCBPrioTbl′[prio′] ==ₑ NULL){
           (* OSTCBPrioTbl′[prio′] =ₑ 〈OS_TCB ∗〉PlaceHolder;ₛ  *)
           (* EXIT_CRITICAL;ₛ *)
         
           err′ =ᶠ OS_TCBInit(·prio′ (*, task′, pdata′*) ·);ₛ
           IF (err′ ==ₑ ′OS_NO_ERR) {
               (*ENTER_CRITICAL;ₛ*)
               STKINIT (task′, pdata′,  OSTCBPrioTbl′[prio′ ]);ₛ
               (* ++ OSTaskCtr′;ₛ *)
               EXIT_CRITICAL;ₛ
               (* If (OSRunning′ ==ₑ CTrue) { *)
                OS_Sched(­)
               (* } *)
           }ELSE{
               (* ENTER_CRITICAL;ₛ *)
               (* OSTCBPrioTbl′[prio′] =ₑ NULL;ₛ *)
               EXIT_CRITICAL
           };ₛ
           RETURN  err′ 
       };ₛ
       EXIT_CRITICAL;ₛ
       RETURN  ′OS_PRIO_EXIST
}·.

Definition STKFREE (a : expr ) :=
  sprim (stkfree a).
 
Require Import inline_definitions.
Require Import inline_bittblfunctions.

Definition OSTaskDel_impl := 
Int8u ·OSTaskDel·(⌞prio @ Int8u⌟)··{
      ⌞
        ptr @ OS_EVENT∗;
        ptcb @ OS_TCB∗;
        (* self @ Int8u; *)
        x @ OS_TCB∗
      ⌟;

      If (prio′ ==ₑ ′OS_IDLE_PRIO) {
          RETURN ′OS_TASK_DEL_IDLE
      };ₛ
      If (prio′ ≥ ′OS_LOWEST_PRIO (* &&ₑ prio′ !=ₑ ′OS_PRIO_SELF *)){
          RETURN ′OS_PRIO_INVALID
      };ₛ
      ENTER_CRITICAL;ₛ
      ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ

     If (ptcb′ ==ₑ NULL){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_ERR
      };ₛ
      If (ptcb′ ==ₑ PlaceHolder){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_ERR
      };ₛ
      (* self′ =ᶠ OS_IsSomeMutexOwner(·ptcb′·);ₛ *)
      (* If (self′==ₑ ′ 1){ *)
      (*   EXIT_CRITICAL;ₛ *)
      (*   RETURN ′OS_TASK_DEL_SOME_MUTEX_OWNER *)
      (* };ₛ *)
      If (ptcb′→OSTCBNext ==ₑ NULL){
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TASK_DEL_HAS_NO_NEXT
      };ₛ
 
      inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil);ₛ
      (* OSRdyTbl′[ptcb′→OSTCBY] &= ∼ptcb′→OSTCBBitX;ₛ
       * If(OSRdyTbl′[ptcb′→OSTCBY] ==ₑ ′0){
       *     OSRdyGrp′  &= ∼ptcb′→OSTCBBitY
       * };ₛ *)

      ptr′ =ₑ ptcb′→OSTCBEventPtr;ₛ
      If (ptr′ !=ₑ NULL){
        inline_call inline_bittbl_clearbit
          ((ptr′→OSEventGrp) :: (ptr′→OSEventTbl) ::
             (ptcb ′ → OSTCBBitX) :: (ptcb ′ → OSTCBBitY) :: (ptcb ′ → OSTCBY) :: nil)  
        (* pevent′→OSEventTbl[ptcb′→OSTCBY] =ₑ pevent′→OSEventTbl[ptcb′→OSTCBY] &ₑ (∼ptcb′→OSTCBBitX);ₛ
         * If(pevent′→OSEventTbl[ptcb′→OSTCBY] ==ₑ ′0){
         *     pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼ptcb′→OSTCBBitY)
         * } *)
      };ₛ
      ptcb′→OSTCBDly =ₑ ′0;ₛ
      ptcb′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
      (* −−OSTaskCtr′;ₛ *)
      OSTCBPrioTbl′[prio′] =ₑ NULL;ₛ
      ptcb′→OSTCBEventPtr =ₑ NULL;ₛ
      IF (ptcb′→OSTCBPrev ==ₑ NULL){
          x ′=ₑ ptcb′→OSTCBNext;ₛ
          x′→OSTCBPrev =ₑ NULL;ₛ
          OSTCBList′ =ₑ x′
      }ELSE{
          x′ =ₑ ptcb′→OSTCBPrev;ₛ
          x′→OSTCBNext =ₑ ptcb′→OSTCBNext;ₛ
          x′ =ₑ ptcb′→OSTCBNext;ₛ
          x′→OSTCBPrev =ₑ ptcb′→OSTCBPrev
      };ₛ
      ptcb′→OSTCBNext =ₑ OSTCBFreeList′;ₛ
      OSTCBFreeList′ =ₑ ptcb′;ₛ
      STKFREE (    ptcb′  );ₛ
      ptcb′→OSTCBflag =ₑ ′0;ₛ
      ptcb′→__OSTskLoc =ₑ ′__Loc_normal;ₛ
      ptcb′→__OSTskPtr =ₑ NULL;ₛ 
      EXIT_CRITICAL;ₛ
      OS_Sched(­);ₛ
      RETURN ′OS_NO_ERR
      (* };ₛ *)
      (* EXIT_CRITICAL;ₛ *)
      (* RETURN ′OS_TASK_DEL_ERR *)
}·. 


(* ** ac: Check (inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)) . *)
(* ** ac: Eval simpl in (inline_call inline_bittbl_clearbit ((OSRdyGrp ′):: (OSRdyTbl ′)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil)). *)

(* Eval simpl in (          inline_call inline_bittbl_clearbit ((pevent′→OSEventGrp):: (pevent′→OSEventTbl)::(ptcb ′ → OSTCBBitX)::(ptcb ′ → OSTCBBitY)::(ptcb ′ → OSTCBY)::nil) *)
(*               ). *)
