
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import os_core. 

Open Scope code_scope.

Definition OSSemPend_impl  :=
Int8u ·OSSemPend·(⌞ptr @ OS_EVENT∗⌟)··{
       ⌞⌟;

        ENTER_CRITICAL;ₛ
        If (ptr′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
             EXIT_CRITICAL;ₛ 
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ
        If (ptr′→OSEventCnt >ₑ ′0){
            −−ptr′→OSEventCnt;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        };ₛ

        OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_SEM;ₛ
        OSTCBCur′→OSTCBDly =ₑ ′0;ₛ
        OS_EventTaskWait(­ptr′­);ₛ 
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        (* If (OSTCBCur′→OSTCBStat &ₑ ′OS_STAT_SEM) { *)
        (*     OS_EventTO(­pevent′­);ₛ  *)
        (*     EXIT_CRITICAL;ₛ *)
        (*     RETURN ′OS_TIMEOUT *)
        (* };ₛ *)
        OSTCBCur′→OSTCBEventPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR
}· .

Definition OSSemPost_impl := 
Int8u ·OSSemPost·(⌞ptr @ OS_EVENT∗⌟)··{
       ⌞
         x  @ Int8u
       ⌟;

        ENTER_CRITICAL;ₛ
        If (ptr′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        If (ptr′→OSEventGrp !=ₑ ′0){
            x′ =ₑ ′OS_STAT_SEM;ₛ 
            OS_EventTaskRdy(­ptr′, ecast NULL (Tptr Tvoid), x′­);ₛ 
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        If (ptr′→OSEventCnt <ₑ ′65535){
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′OS_SEM_OVF

}·.
