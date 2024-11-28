
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_sema_oper. 

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

(* the function that performs the P operation on a service-level semahpore *)
Definition service_sema_P_impl :=
Tint8 ·service_sema_P·(⌞idx @ Int32⌟)··{   
        ⌞
         err @ Tint8;
         p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ 
        If (idx′ <ₑ ′0 ||ₑ idx′ ≥ ′MAX_OBJ_NUM){
           EXIT_CRITICAL;ₛ 
           RETURN  ′-1
        };ₛ
        p′ =ₑ efield (obj_arr′[idx′]) ptr;ₛ  
        If (p′ ==ₑ NULL ||ₑ p′ ==ₑ 〈OS_EVENT ∗〉PlaceHolder) { 
            EXIT_CRITICAL;ₛ
            RETURN ′-1
        };ₛ
        OSTCBCur′→__OSTskPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ

        err′ =ᶠ OSSemPend(· p′ ·);ₛ  
        
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskPtr =ₑ NULL;ₛ   
        EXIT_CRITICAL;ₛ

        RETURN  err′
}· .

(* the function that performs the V operation on a service-level semahpore *) 
Definition service_sema_V_impl :=
Tint8 ·service_sema_V·(⌞idx @ Int32⌟)··{   
        ⌞
         err @ Tint8;
         p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ 
        If (idx′ <ₑ ′0 ||ₑ idx′ ≥ ′MAX_OBJ_NUM){
           EXIT_CRITICAL;ₛ 
           RETURN  ′-1
        };ₛ
        p′ =ₑ efield (obj_arr′[idx′]) ptr;ₛ  
        If (p′ ==ₑ NULL ||ₑ p′ ==ₑ 〈OS_EVENT ∗〉PlaceHolder) { 
            EXIT_CRITICAL;ₛ
            RETURN ′-1
        };ₛ
        OSTCBCur′→__OSTskPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ

        err′ =ᶠ OSSemPost(· p′ ·);ₛ  
        
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskPtr =ₑ NULL;ₛ   
        EXIT_CRITICAL;ₛ

        RETURN  err′
}· .

Close Scope code_scope.         
