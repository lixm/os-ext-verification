Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition OS_EventWaitListInit_impl  :=
Void · OS_EventWaitListInit·(⌞ptr @ OS_EVENT∗ ⌟)··{
       ⌞ptbl @ Int8u∗⌟;

       ptr′→OSEventGrp =ₑ ′0;ₛ
       ptbl′ =ₑ &ₐ ptr′→OSEventTbl[′0];ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
                      
       RETURN
}·. 

Close Scope code_scope.
