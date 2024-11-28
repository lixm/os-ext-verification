Require Import os_code_defs.
Require Import code_notations.

Open Scope code_scope.

Definition OS_EVENT : type := 
  STRUCT os_event ­{ 
                    ⌞OSEventType @ Int8u;
                    OSEventGrp @ Int8u; 
                    OSEventCnt @ Int16u; 
                    OSEventPtr @ (Void ∗);
                    OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE);
                    OSEventListPtr @ STRUCT os_event ⋆ ⌟
                   }­.


Definition OS_TCB : type := 
  STRUCT os_tcb ­{
                  ⌞OSTCBNext @ STRUCT os_tcb ⋆;
                  OSTCBPrev @ STRUCT os_tcb ⋆ ;
                  OSTCBEventPtr @ OS_EVENT ∗ ; 
                  OSTCBMsg @ Void ∗ ;
                  OSTCBDly @ Int16u ;
                  OSTCBStat @ Int8u ;
                  OSTCBPrio @ Int8u ;
                  OSTCBX @ Int8u ;
                  OSTCBY @ Int8u ; 
                  OSTCBBitX @ Int8u ;
                  OSTCBBitY @ Int8u ;
                  OSTCBflag @ Int8u ;
                  __OSTskLoc @ Int8u ;
                  __OSTskPtr @ Tptr OS_EVENT⌟ 
                 }­.


Definition OS_STK : type := Int32.

Definition OS_STK_BLK : type := 
  STRUCT os_stk_blk ­{
                      ⌞nextblk @ Void ∗;
                      taskstk @ (Tarray OS_STK ∘TASK_STK_SIZE)⌟
                     }­.


Definition PlaceHolder:= &ₐ OSPlaceHolder′.


Definition gvarlist1 : decllist := 
             ⌞ 
              OSCtxSwCtr @ Int32u ;
              OSEventList @ OS_EVENT ∗ ;
              OSEventFreeList @ OS_EVENT ∗ ;
              OSEventTbl @ (Tarray OS_EVENT ∘OS_MAX_EVENTS);
              OSIntNesting @ Int8u;                                       
              OSIntExitY @ Int8u;
              OSPrioCur @ Int8u;
              OSPrioHighRdy @ Int8u;
              OSRdyGrp @ Int8u;
              OSRdyTbl @ (Tarray Int8u ∘OS_RDY_TBL_SIZE);
              OSRunning @ Int8u                                       
             ⌟.

Definition gvarlist2 :decllist := 
             ⌞ 
              OSTaskCtr @ Int8u;
              OSIdleCtr @ Int32u;
              OSTCBCur @ OS_TCB ∗;
              OSTCBFreeList @ OS_TCB ∗;
              OSTCBHighRdy @ OS_TCB ∗; 
              OSTCBList @ OS_TCB;                                       
              OSTCBPrioTbl @ (Tarray (OS_TCB ∗ ) ∘(OS_LOWEST_PRIO + 1)%Z );
              OSTCBTbl @ (Tarray OS_TCB ∘(OS_LOWEST_PRIO + 1)) 
            ⌟.

Definition gvarlist3 :decllist := 
             ⌞
              OSTime @ Int32u;
              OSMapTbl @ (Tarray Int8u 8); 
              OSUnMapTbl @ (Tarray Int8u 256)
             ⌟.


Fixpoint plus_decl  (d1 d2 : decllist) {struct d1} :=
    match d1 with
     | dnil => d2
     | dcons x t d1' => dcons x t (plus_decl d1' d2)
    end.


Definition GlobalVariables := 
  plus_decl (plus_decl gvarlist1 gvarlist2) gvarlist3.


(*********************** struct for service objects **********************) 

Definition service_obj_t : type := 
  STRUCT service_obj_ ­{ 
                        ⌞
                           attr @ Int32; 
                           ptr @ OS_EVENT ∗
                      ⌟
                        }­.

Definition gvarlist4 :decllist := 
             ⌞
              obj_arr @ (Tarray service_obj_t ∘(MAX_OBJ_NUM))
             ⌟.

Close Scope code_scope.
