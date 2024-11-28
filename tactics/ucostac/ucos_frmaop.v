
Require Import include_frm.
Require Export frmaop_sol.
Require Import os_inv.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import code_notations.

Open Scope code_scope.

Lemma good_frm_tcbdllseg : 
  forall vl head hp tail tn , 
    GoodFrm(tcbdllseg head hp tail tn vl).
Proof.
  intros.
  unfold tcbdllseg.
  apply good_frm_dllseg.
Qed.

Hint Resolve good_frm_tcbdllseg : good_frm_lemmas.

Lemma good_frm_AOSEventTbl : 
  forall x0 v0, GoodFrm (AOSEventTbl x0 v0).
Proof.
  intros.
  unfold AOSEventTbl.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSEventTbl : good_frm_lemmas.


Lemma good_frm_node : 
  forall v vl t , GoodFrm (node v vl t).
Proof. 
  introv.
  unfold node.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_node : good_frm_lemmas.


Lemma good_frm_AOSEvent : 
  forall a0 v x, GoodFrm  (AOSEvent a0 v x).
Proof.
  intros.
  unfold AOSEvent.
  good_frm_sovler.
Qed. 

Hint Resolve  good_frm_AOSEvent : good_frm_lemmas.


Lemma good_frm_mqsllseg :
  forall p n l msgqls, GoodFrm (evsllseg p n l msgqls).
Proof.
  introv.
  gen l n p msgqls.
  inductions l; intros; simpl; good_frm_sovler; auto.
  destruct msgqls.
  simpl;auto.
  destruct a.
  good_frm_sovler.
  unfold AEventNode.
  good_frm_sovler.
  unfold AEventData.
  destruct e; good_frm_sovler.
Qed.

Hint Resolve good_frm_mqsllseg  : good_frm_lemmas.


Lemma good_frm_ecbfslleg : 
  forall ls x y ,
    GoodFrm (ecbf_sllseg x  y ls OS_EVENT V_OSEventListPtr).
Proof.
   inductions ls; intros.  
   simpl.   auto. 
   unfold ecbf_sllseg; fold ecbf_sllseg.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_ecbfslleg  : good_frm_lemmas.


Lemma good_frm_ecbfsll: forall ls x ,
                               GoodFrm (ecbf_sll x ls OS_EVENT V_OSEventListPtr).
Proof.
   unfold ecbf_sll. 
    intros.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_ecbfsll  : good_frm_lemmas.

Lemma good_frm_AOSEventFreeList:
  forall fecbh fecbvl,
    GoodFrm (AOSEventFreeList fecbh fecbvl). 
Proof.
  unfold AOSEventFreeList.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSEventFreeList : good_frm_lemmas.


Lemma good_frm_EventList'  :
  forall  qptrl msgql,
    GoodFrm ((EX p : val, GV OSEventList @ OS_EVENT∗ |-> p ** evsllseg p Vnull qptrl msgql)).
Proof.
  intros.  
   good_frm_sovler.
Qed.

Hint Resolve good_frm_EventList' : good_frm_lemmas.

Lemma good_frm_AMsgQList : forall qptrl msgql mqls tcbls,
                             GoodFrm (AECBList qptrl msgql mqls tcbls ).
Proof.
  introv.
  unfold AECBList.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AMsgQList : good_frm_lemmas.  

Lemma good_frm_AOSMapTbl : GoodFrm AOSMapTbl.
Proof. 
  unfold AOSMapTbl.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSMapTbl : good_frm_lemmas. 


Lemma good_frm_AOSUnMapTbl : GoodFrm AOSUnMapTbl.
Proof. 
  unfold AOSUnMapTbl.
  good_frm_sovler.  
Qed.

Hint Resolve good_frm_AOSUnMapTbl : good_frm_lemmas. 

Lemma good_frm_AOSTCBPrioTbl:
  forall  ptbl rtbl tcbls (* ptls  *)vhold,
    GoodFrm (AOSTCBPrioTbl ptbl rtbl tcbls (* ptls  *)vhold).
Proof.
  unfold AOSTCBPrioTbl.
  intros.
  good_frm_sovler.
Qed.


Hint Resolve good_frm_AOSTCBPrioTbl : good_frm_lemmas. 


Lemma good_frm_AOSIntNesting : GoodFrm AOSIntNesting.
Proof.
  unfold AOSIntNesting.
   good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIntNesting : good_frm_lemmas. 

Lemma good_frm_AOSTime : forall t,GoodFrm (AOSTime t).
Proof.
  unfold AOSTime.
  intros;  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSTime : good_frm_lemmas. 

Lemma good_frm_AGVars : GoodFrm AGVars.
Proof.
  unfold AGVars.
  intros.
   good_frm_sovler.
Qed.


Hint Resolve good_frm_AGVars : good_frm_lemmas. 


Lemma good_frm_AOSTCBList: forall x1 x2 x3 x4 x5 x6 x7,
                             GoodFrm (AOSTCBList x1 x2 x3 x4 x5 x6 x7).
Proof.
  introv.
  unfold AOSTCBList.
  good_frm_sovler.  
Qed.

Hint Resolve  good_frm_AOSTCBList  : good_frm_lemmas.

Lemma good_frm_tcbdllflsg : forall x1 x2, 
   GoodFrm (tcbdllflag x1 x2).
Proof.
  intros.
  gen x1.
  inductions x2.
  simpl; split; auto.
  intros.
  unfold tcbdllflag in *.
  simpl.
  intros; splits; auto.
Qed.

Hint Resolve   good_frm_tcbdllflsg   : good_frm_lemmas.

Lemma good_frm_AOSTCBList':
  forall x1 x2 x3 x4 x5 x6 x7 x8,
    GoodFrm (AOSTCBList' x1 x2 x3 x4 x5 x6 x7 x8).
Proof.
  introv.
  unfold AOSTCBList'.
  unfold GoodFrm.
  fold GoodFrm.
  split; intros.
  splits;  good_frm_sovler; auto.
  simpl; intros; splits; auto.
  good_frm_sovler.
  splits; good_frm_sovler; auto.
  unfold tcblist.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBList'  : good_frm_lemmas.


Lemma good_frm_sllfreeflag :
  forall x1 x2,
    GoodFrm (sllfreeflag x1 x2).
Proof.
  introv.
  unfold sllfreeflag.
  gen x1.
  inductions x2. 
  intros.
  simpl; auto.
  intros.
  simpl.
  intros;splits; auto.
Qed.

Hint Resolve  good_frm_sllfreeflag  : good_frm_lemmas.

Lemma good_frm_AOSTCBFreeList: forall x1 x2,
                             GoodFrm (AOSTCBFreeList x1 x2).
Proof.
  introv.
  unfold AOSTCBFreeList.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBFreeList  : good_frm_lemmas. 

Lemma good_frm_AOSTCBFreeList': 
  forall x1 x2 x3 x4,
    GoodFrm (AOSTCBFreeList' x1 x2 x3 x4).
Proof.
  introv.
  unfold AOSTCBFreeList'.
  good_frm_sovler.
  unfold GoodFrm. fold GoodFrm.
  splits.
  unfold TCBFree_Not_Eq.
  good_frm_sovler.
  unfold TCBFree_Eq.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBFreeList'  : good_frm_lemmas. 

Lemma good_frm_AOSRdyTbl : forall vl,  
                               GoodFrm (AOSRdyTbl vl).
Proof.
  intros.
  unfold AOSRdyTbl .
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyTbl  : good_frm_lemmas. 


Lemma good_frm_AOSRdyGrp : forall vl,  
                               GoodFrm (AOSRdyGrp vl).
Proof.
  intros.
  unfold AOSRdyGrp .
 good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyGrp  : good_frm_lemmas. 

Lemma good_frm_AOSRdyTblGrp  : forall rtbl rgrp,  
                               GoodFrm (AOSRdyTblGrp rtbl rgrp).
Proof.
  intros.
  unfold   AOSRdyTblGrp .
 good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyTblGrp  : good_frm_lemmas.


(*add by wss*)
Lemma good_frm_OSLinv : forall t lg,
 GoodFrm (p_local OSLInv t lg).
Proof.
  intros. unfold p_local, LINV, OSLInv.
  unfold GoodFrm; fold GoodFrm.
  split; [cbn;auto | ].
  split;[ | auto].
  intros. 
  split;[ cbn;auto | ].
  split;[ cbn;auto | ].
  split;[ cbn;auto | ].
  auto.
Qed. 

Hint Resolve good_frm_OSLinv : good_frm_lemmas.
(*add end*)


(***********************add by CNU ******************************)

Lemma good_frm_Aarray_new' :
  forall n vll t l , GoodFrm (Aarray_new' l n t vll).
Proof.
  induction n; induction vll; intros;
    try good_frm_sovler.
  clear -IHn.
  destruct l.
  destruct t;
    simpl Aarray_new' in *;
    destruct a; 
    try good_frm_sovler;
    destruct a;
    try good_frm_sovler.
Qed.

Hint Resolve  good_frm_Aarray_new': good_frm_lemmas.  

Lemma good_frm_Aarray_new :
  forall vll t l , GoodFrm (Aarray_new l t vll).
Proof.
  intros.
  unfold Aarray_new.
  destruct t; try good_frm_sovler. 
Qed.

Hint Resolve  good_frm_Aarray_new: good_frm_lemmas.  

Lemma good_frm_AObjArr :
  forall objl, GoodFrm (AObjArr objl).
Proof.
  intros.
  unfold AObjArr.
  unfold GoodFrm.
  fold GoodFrm.
  split; good_frm_sovler.
  split; good_frm_sovler.
  auto.
Qed.

Hint Resolve  good_frm_AObjArr: good_frm_lemmas.


Lemma good_frm_AObjs :
  forall objl absobjs ecbls vhold,
    GoodFrm (AObjs objl absobjs ecbls vhold).  
Proof.
  intros.
  unfold AObjs.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AObjs: good_frm_lemmas. 


Lemma good_frm_objaux_node:
  forall a v1 v2, GoodFrm (objaux_node a v1 v2). 
Proof.
  intros. simpl. splits; auto.
Qed.

Hint Resolve good_frm_objaux_node: good_frm_lemmas. 

Lemma good_frm_llsegobjaux:
  forall l hd tn locmp ptrmp nextf, 
    GoodFrm (llsegobjaux hd tn l locmp ptrmp nextf).   
Proof.
  inductions l.
  intros. simpl. splits; auto.
  intros. simpl. intros. splits; auto. 
Qed.

Hint Resolve good_frm_llsegobjaux : good_frm_lemmas.

Lemma good_frm_tcbllsegobjaux:
  forall tcbvl tcbh locmp ptrmp, 
    GoodFrm (tcbllsegobjaux tcbh tcbvl locmp ptrmp).  
Proof.
  intros.
  unfold tcbllsegobjaux. apply good_frm_llsegobjaux.
Qed.

Hint Resolve good_frm_tcbllsegobjaux: good_frm_lemmas.


Lemma good_frm_AOBJ : 
  forall objl absobjs ecbls vhold tcblh tcbvl fecbh fecbvl, 
    GoodFrm (AOBJ objl absobjs ecbls vhold tcblh tcbvl fecbh fecbvl). 
Proof.
  intros.
  unfold AOBJ. 
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOBJ: good_frm_lemmas.  


(*********************** add by CNU end  ******************************) 


Theorem can_change_aop_aevtdata:
  forall vl d , can_change_aop (AEventData vl d).
Proof.
  intros.
  unfold AEventData.
  destruct d; can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aevtdata : can_change_aop.

Lemma can_change_aop_aoseventtbl:
  forall x d,
  can_change_aop (AOSEventTbl x d).
Proof.
  intros.
  unfold AOSEventTbl.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aoseventtbl : can_change_aop.


Lemma  can_change_aop_aosevent:
  forall l vl etbl,
   can_change_aop (AOSEvent l vl etbl).
Proof.
  intros.
  unfold AOSEvent.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aosevent : can_change_aop.

Theorem can_change_aop_msgqnode :
  forall l vl d c,
    can_change_aop (AEventNode l vl d c).
Proof.
  intros.
  unfold AEventNode.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgqnode : can_change_aop.

Theorem can_change_aop_msgqllseg :
  forall h tn l msgqls,
    can_change_aop (evsllseg h tn l msgqls).
Proof.
  intros.
  gen h tn msgqls.
  induction l; simpl in *; intuition auto.
  destruct msgqls.
  can_change_aop_solver.
  destruct a. 
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgqllseg : can_change_aop.

Theorem can_change_aop_tcbdllseg :
  forall h hp t tn l,
    can_change_aop (tcbdllseg h hp t tn l).
Proof.
  intros.
  unfold tcbdllseg.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_tcbdllseg : can_change_aop.


Theorem    can_change_aop_ecbfsllseg :
  forall ls x y,
    can_change_aop (ecbf_sllseg x y ls OS_EVENT V_OSEventListPtr).
Proof.
  inductions ls. 
  intros; simpl; intuition auto.
  unfold ecbf_sllseg; fold ecbf_sllseg.
  unfold dllseg; fold dllseg.
  intros.
  can_change_aop_solver.  
Qed.

Hint Resolve can_change_aop_ecbfsllseg: can_change_aop.

Theorem    can_change_aop_ecbfsll :
  forall ls x , can_change_aop (ecbf_sll x ls OS_EVENT V_OSEventListPtr).
Proof.

  intros; unfold ecbf_sll.
  can_change_aop_solver.  
Qed.


Hint Resolve can_change_aop_ecbfsll: can_change_aop.


Theorem  can_change_aop_sllfreeflag :
  forall x17 x18, can_change_aop (sllfreeflag x17 x18).
Proof.
  intros.
  unfold sllfreeflag.
  gen x17.
  inductions x18.
  intros.
  simpl; auto.
  intros.
  simpl.
  intros.
  splits; auto.
Qed.

Hint Resolve  can_change_aop_sllfreeflag: can_change_aop.

Theorem  can_change_aop_tcbdllflag:
  forall x6 x5, can_change_aop (tcbdllflag x5 x6).
Proof.
  inductions x6.
  simpl; auto.
  intros.
  simpl.
  intros.
  splits; auto.
  unfold tcbdllflag in IHx6.
  auto.
Qed.

Hint Resolve  can_change_aop_tcbdllflag: can_change_aop.

Theorem can_change_aop_tcbnotin:
  forall x6 x19 ls,
    can_change_aop (TCB_Not_In x6 x19 ls).
 Proof.
   intros.
   unfold TCB_Not_In.
   unfold can_change_aop.
   fold can_change_aop.
   auto.
Qed.

 Hint Resolve  can_change_aop_tcbnotin: can_change_aop.

 Theorem can_change_aop_tcblist:
  forall p1 p2 tcbl1 ls rtbl ct tcbls ,
   can_change_aop (AOSTCBList p1 p2 tcbl1 ls  rtbl ct tcbls). 
Proof.
  intros.
  unfold AOSTCBList.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_tcblist: can_change_aop.

Theorem can_change_aop_tcblist_new:
  forall p1 p2 tcbl1 ls rtbl ct tcbls ptfree,
   can_change_aop (AOSTCBList' p1 p2 tcbl1 ls  rtbl ct tcbls ptfree). 
Proof.
  intros.
  unfold AOSTCBList'.
  unfold can_change_aop.
  fold can_change_aop.
  split.
  intros.
  splits;  can_change_aop_solver; auto.
  simpl; auto.
  splits; can_change_aop_solver; auto.
  intros.
  splits; can_change_aop_solver; auto.
  simpl; auto.
  split; auto.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_tcblist_new: can_change_aop.

Lemma can_change_aop_noteq:
  forall ptfree ct lfree, 
   can_change_aop (TCBFree_Not_Eq ptfree ct lfree).
Proof.
  intros.
  unfold TCBFree_Not_Eq.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_noteq: can_change_aop.

Lemma can_change_aop_eq:
  forall ptfree ct lfree tcbls, 
   can_change_aop (TCBFree_Eq ptfree ct lfree tcbls).
Proof.
  intros.
  unfold TCBFree_Eq.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_eq: can_change_aop.

Theorem can_change_aop_tcbfreelist:
  forall ptfree lfree,
   can_change_aop (AOSTCBFreeList ptfree lfree).
Proof.
  intros.
  unfold AOSTCBFreeList.
  can_change_aop_solver.
Qed.
  
Hint Resolve  can_change_aop_tcbfreelist: can_change_aop.



Theorem can_change_aop_tcbfreelist_new:
  forall ptfree lfree ct tcbls,
   can_change_aop (AOSTCBFreeList' ptfree lfree ct tcbls).
Proof.
  intros.
  unfold AOSTCBFreeList'.
  unfold can_change_aop.
  fold can_change_aop.
  splits;  can_change_aop_solver.
Qed.
  
Hint Resolve  can_change_aop_tcbfreelist_new: can_change_aop.

Lemma can_change_aop_evtfls:
  forall fecbh fecbvl, can_change_aop (AOSEventFreeList fecbh fecbvl). 
Proof.
  intros.
  unfold AOSEventFreeList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_evtfls: can_change_aop.


Lemma can_change_aop_ecblist:
  forall x3 x2 x12 x13,
  can_change_aop (AECBList x3 x2 x12 x13).
Proof.
  intros.
  unfold AECBList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_ecblist: can_change_aop.

Lemma can_change_aop_mtbl:
  can_change_aop AOSMapTbl.
Proof.
  intros.
  unfold AOSMapTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_mtbl: can_change_aop.

Lemma can_change_aop_unmtbl:
  can_change_aop AOSUnMapTbl.
Proof.
  intros.
  unfold AOSUnMapTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_unmtbl: can_change_aop.

Lemma can_change_aop_prtbl:
  forall x4 x10 x13 x16 (* ptls *),
    can_change_aop  (AOSTCBPrioTbl x4 x10 x13 (* ptls  *)x16).
Proof.
  intros.
  unfold AOSTCBPrioTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_prtbl: can_change_aop.


Lemma can_change_aop_intnest:
  can_change_aop AOSIntNesting.
Proof.
  intros.
  unfold AOSIntNesting.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_intnest: can_change_aop.

Lemma can_change_aop_rdytbl:
  forall x10 ,
  can_change_aop  (AOSRdyTbl x10).
Proof.
  intros.
  unfold AOSRdyTbl.
  can_change_aop_solver.
Qed.


Hint Resolve  can_change_aop_rdytbl: can_change_aop.

Lemma can_change_aop_rdygrp:
  forall x10 ,
  can_change_aop  (AOSRdyGrp x10).
Proof.
  intros.
  unfold AOSRdyGrp.
  can_change_aop_solver.
Qed.


Hint Resolve  can_change_aop_rdygrp: can_change_aop.


Lemma can_change_aop_rdytbgrp:
  forall x10 x11,
  can_change_aop  (AOSRdyTblGrp x10 x11).
Proof.
  intros.
  unfold AOSRdyTblGrp.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_rdytbgrp: can_change_aop.

Lemma can_change_aop_time:
  forall x14, 
  can_change_aop  (AOSTime (Vint32 x14)).
Proof.
  intros.
  unfold AOSTime.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_time: can_change_aop.

Lemma can_change_aop_gvars:
  can_change_aop AGVars.
Proof.
  intros.
  unfold AGVars.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_gvars: can_change_aop.

Lemma can_change_aop_plocal:
  forall tid l, can_change_aop (p_local OSLInv tid l).
Proof.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_plocal : can_change_aop.

Lemma can_change_aop_isris:
  can_change_aop  A_isr_is_prop.
Proof.
  intros.
  unfold  A_isr_is_prop.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_isris: can_change_aop.


(***********************add by CNU ******************************)

Theorem can_change_aop_Aarray_new' :
forall n vll t l , can_change_aop (Aarray_new' l n t vll).
Proof.
induction n; induction vll; intros;
try can_change_aop_solver.
clear -IHn.
destruct l.
destruct t;
simpl Aarray_new' in *;
destruct a; 
try can_change_aop_solver;
destruct a;
try can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_Aarray_new': can_change_aop.  

Theorem can_change_aop_Aarray_new :
forall vll t l , can_change_aop (Aarray_new l t vll).
Proof.
intros.
unfold Aarray_new.
destruct t; try can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_Aarray_new: can_change_aop.  

Theorem can_change_aop_AObjArr :
  forall objl, can_change_aop (AObjArr objl). 
Proof.
  intros.
  unfold AObjArr.
  unfold can_change_aop.
  fold can_change_aop.
  split; can_change_aop_solver.
  split; can_change_aop_solver.
  auto.
Qed.

Hint Resolve  can_change_aop_AObjArr: can_change_aop.   

Theorem can_change_aop_AObjs : 
  forall (objl : list vallist) (absobjs : ObjMod.map) (ecbls : EcbMod.map) vhold, 
    can_change_aop (AObjs objl absobjs ecbls vhold). 
Proof.
  intros.
  unfold AObjs. 
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AObjs: can_change_aop. 


Lemma can_change_aop_objaux_node:
  forall a v1 v2, 
    can_change_aop (objaux_node a v1 v2).  
Proof.
  intros.
  simpl. splits; auto.
Qed.

Hint Resolve can_change_aop_objaux_node: can_change_aop.

Lemma can_change_aop_llsegobjaux :
  forall l hd tn locmp ptrmp nextf,  
    can_change_aop (llsegobjaux hd tn l locmp ptrmp nextf).  
Proof.
  inductions l.
  intros. simpl. splits; auto.
  intros. simpl. intros. splits; auto. 
Qed.   

Hint Resolve can_change_aop_llsegobjaux: can_change_aop.

Lemma can_change_aop_tcbllsegobjaux:
  forall tcbvl tcbh  locmp ptrmp, 
    can_change_aop (tcbllsegobjaux tcbh tcbvl locmp ptrmp).  
Proof.
  unfold tcbllsegobjaux.
  intros. apply can_change_aop_llsegobjaux.
Qed.

Hint Resolve can_change_aop_tcbllsegobjaux: can_change_aop. 

Theorem can_change_aop_AOBJ :
  forall objl absobjs ecbls vhold tcblh tcbvl fecbh fecbvl, 
    can_change_aop (AOBJ objl absobjs ecbls vhold tcblh tcbvl fecbh fecbvl). 
Proof.
  intros.
  unfold AOBJ.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_AOBJ: can_change_aop. 

(*********************** add by CNU end  ******************************) 

Theorem can_change_aop_OSQInv :
  can_change_aop OSInv.
Proof.
  unfold OSInv.
  can_change_aop_solver.
Qed.

Close Scope code_scope.
