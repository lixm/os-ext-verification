

(** this file contains the simulations used to proof our logic
soundness, we build three levels of simulations to support mudular
reasoning of function calls and interrupts **)

Require Import include_frm.

Definition enapi (C: code) (pl: lprog) : Prop :=
  match C with
    (c, (ke, ks)) =>
      match pl with
        (pc, (po, pi, ip)) =>
          (exists f vl tl,
              c = curs (sfexec f vl tl) /\ po f <> None /\ ke = kenil)
          \/
            (exists vl dl f s E ks',
                c = curs (salloc vl dl) /\ ks = kcall f s E ks' /\ po f <> None /\ ke = kenil) 
      end
  end.

Definition opt_htstep
  (ph: hprog) Ch (cst: clientst) OO Ch' (cst': clientst) OO' lb :=
  (exists pc A f r vl tl ks vl', 
      ph = (pc, A) /\
        Ch = (curs (sfexec f (rev vl) (rev tl)), (kenil, ks)) /\
        Ch' = (curs (hapi_code (r (vl++vl'))), (kenil, ks)) /\
        (exists tp tl, match A with (aspc, _, _) => aspc f = Some (r, (tp, tl)) end) /\ 
        lb = Some vl' /\ 
        hapistep A Ch OO Ch' OO')
  \/
    Ch = Ch' /\ cst = cst' /\ OO = OO' /\ lb = None.

Definition lb_equiv (lb1 lb2: option vallist) :=
  lb1 = None /\ lb2 = None \/
    exists vl1 vl2, lb1 = Some vl1 /\ lb2 = Some vl2. 

Definition enapi_t (T: tasks) t (pl: lprog) : Prop := 
  exists C, get T t = Some C /\ enapi C pl.  

(* added to take care of high level abortion due to assertion (actually assumption) failure *) 
Definition absabt (T: tasks) :=
  exists t ke ks, get T t = Some ((curs (hapi_code spec_abort)), (ke, ks)).

Definition opt_hpstep (ph: hprog) T cst O T' cst' O' lb t :=
  exists Ch Ch',
    get T t = Some Ch /\
      T' = set T t Ch' /\ 
      opt_htstep ph Ch cst O Ch' cst' O' lb.  

(* Inductive hpsteps: *)
(*   hprog -> tasks -> clientst -> osabst -> tasks -> clientst -> osabst -> Prop := *)
(* | hpsteps_O (p:hprog) (T:tasks) (cst:clientst) O:  *)
(*   hpsteps p T cst O  T cst O  *)
(* | hpsteps_S p T T' T'' cst cst' cst'' O O' O'': *)
(*   hpstep p T cst O T' cst' O' -> *)
(*   hpsteps p T' cst' O'  T'' cst'' O''->  *)
(*   hpsteps p T cst O T'' cst'' O''  *)
(* | hpsteps_S_ev p T T' T'' cst cst' cst'' O O' O'' ev: *)
(*   hpstepev p T cst O T'' cst'' O'' ev -> *)
(*   hpsteps p T'' cst'' O'' T' cst' O' -> *)
(*   hpsteps p T cst O T' cst' O'. *)

(* Definition prgabsabt (p: hprog) (T: tasks) (cst: clientst) (O: osabst) := *)
(*   exists T' cst' O', hpsteps p T cst O T' cst' O' /\ absabt T'. *)

Definition prgabsabt (p: hprog) (T: tasks) (cst: clientst) (O: osabst) :=
  (exists T' cst' O', hpstepstar p T cst O T' cst' O' /\ absabt T' ) \/
    (exists T' cst' O' ev, hpstepevstar p T cst O T' cst' O' ev /\ absabt T').

Definition int_ks T t := 
  exists c0 ke0 c ke ks E, get T t = Some (c0, (ke0, kint c ke E ks)). 

(* ProgSim is the definition of the simulation relation for systems. *)  
(* New conditions are introduced to express that the simulation of a concrete execution step
     is only necessary if the assumptions in the abstract system are satisfied. *)  
CoInductive ProgSim: lprog -> tasks -> osstate  -> hprog -> tasks -> osabst -> clientst -> tid -> Prop := 
| prog_sim:
  forall (pl:lprog) (ph:hprog) (Tl Th:tasks) (S:osstate) (O:osabst) (cst:clientst) t,
    get O curtid = Some (oscurt t) ->
    (
      forall Tl' S' cst' t',
        lpstep pl Tl cst S t Tl' cst' S' t'->
        (* newly introduced condition expressing that the assumptions in the abstract system 
               are satisfied *)          
        ((~enapi_t Tl t pl) \/ int_ks Tl' t') -> 
        ~prgabsabt ph Th cst O -> 
        exists Th' O',
          hpstepstar ph Th cst O Th' cst' O' /\
            (ProgSim pl Tl' S' ph Th' O' cst' t')
    ) ->
    (
      forall Tl' S' cst' t',
        lpstep pl Tl cst S t Tl' cst' S' t'->
        (enapi_t Tl t pl /\ ~ int_ks Tl' t') ->
        t' = t /\ 
          exists lb,  
            (lb = None \/ exists vl, lb = Some vl) /\ 
              forall Th' O' lb',
                lb_equiv lb lb' ->
                opt_hpstep ph Th cst O Th' cst' O' lb' t ->
                ProgSim pl Tl' S' ph Th' O' cst' t'
    ) -> 
    (
      forall Tl' S' cst' ev t',
        lpstepev pl Tl cst S t Tl' cst' S' t' ev ->
        (* newly introduced condition expressing that the assumptions in the abstract system 
               are satisfied *) 
        ~prgabsabt ph Th cst O -> 
        exists Th' O',
          hpstepevstar ph Th cst O Th' cst' O' ev /\
            (ProgSim pl Tl' S' ph Th' O' cst' t' )  
    )->
    (
      lpstepabt pl Tl cst S t -> 
      (* newly introduced condition expressing that the assumptions in the abstract system 
               are satisfied *) 
      ~prgabsabt ph Th cst O -> 
      hpstepabtstar ph Th cst O 
    )
    -> ProgSim pl Tl S ph Th O cst t.

(* the following is the original definition of ProgSim in the verification of uC/OS-II *)
(* CoInductive ProgSim :   lprog -> tasks -> osstate  -> hprog -> tasks -> osabst -> clientst -> tid -> Prop:= *)
(* | prog_sim: *)
(*     forall (pl:lprog) (ph:hprog) (Tl Th:tasks) (S:osstate) (O:osabst) (cst:clientst) t, *)
(*       get O curtid = Some (oscurt t) -> *)
(*       ( *)
(*         forall Tl' S' cst' t',  *)
(*           lpstep pl Tl cst S t Tl' cst' S' t'-> *)
(*           exists Th' O', hpstepstar ph Th cst O Th' cst' O' /\ *)
(*                          (ProgSim pl Tl' S' ph Th' O' cst' t') *)
(*       ) -> *)
(*       ( *)
(*         forall Tl' S' cst' ev t',  *)
(*           lpstepev pl Tl cst S t Tl' cst' S' t' ev -> *)
(*           exists Th' O', hpstepevstar ph Th cst O Th' cst' O' ev /\ *)
(*                          (ProgSim pl Tl' S' ph Th' O' cst' t' ) *)
(*       )-> *)
(*       ( *)
(*         lpstepabt pl Tl cst S t-> hpstepabtstar ph Th cst O  *)
(*       ) *)
(*       -> ProgSim pl Tl S ph Th O cst t. *)

Definition reltaskpred := prod taskst osabst -> Prop.


(*  (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t) ** p t lg ** [|GoodLInvAsrt p|].*)

Definition getmem (o:taskst) :=  get_mem (get_smem o).

Definition getapi (pl : lprog) := (fst (fst (snd pl))).

Definition getifun (pl : lprog) := (snd (fst (snd pl))).

Definition getsched (ph: hprog) := (snd (snd ph)).


Definition joinm2 o M1 M2  o' :=   exists o1,  joinmem o M1  o1 /\  joinmem o1 M2 o' .

(* Inductive htstepstar:  hprog  -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop:= *)
(* | ht_starO: forall (p:hprog)  (c:code) (cst:clientst) (O:osabst) t, *)
(*               htstepstar p t c cst O c cst O *)
(* | ht_starS: forall (p:hprog)  (c c' c'':code) (cst cst' cst'':clientst) (O O' O'':osabst) t, *)
(*               htstep p t c cst O c' cst' O' -> htstepstar p t c' cst' O' c'' cst'' O''-> *)
(*               htstepstar p t c cst O c'' cst'' O''. *)

(* Inductive htstepevstar: hprog -> tid -> code -> clientst -> osabst ->  *)
(*                         code -> clientst -> osabst -> val -> Prop:= *)
(* | htev_stepstar: forall (p:hprog)  (c c' c'' c''':code)  *)
(*                         (O O' O'':osabst) (ev:val) cst cst' cst'' t, *)
(*                    htstepstar p t c cst O c' cst' O' -> *)
(*                    htstepev p t c' cst' O' c'' cst' O' ev -> *)
(*                    htstepstar p t c'' cst' O' c''' cst'' O'' -> *)
(*                    htstepevstar p t c cst O c''' cst'' O'' ev. *)

(* Inductive htsteps: *)
(*   hprog -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop := *)
(* | htsteps_O p t c cst O: *)
(*   htsteps p t c cst O c cst O *)
(* | htsteps_S p t c c' c'' cst cst' cst'' O O' O'':   *)
(*   htstep p t c cst O c'' cst'' O'' -> *)
(*   htsteps p t c'' cst'' O'' c' cst' O' -> *)
(*   htsteps p t c cst O c' cst' O' *)
(* | htsteps_S_ev p t c c' c'' cst cst' cst'' O O' O'' ev: *)
(*   htstepev p t c cst O c'' cst'' O'' ev -> *)
(*   htsteps p t c'' cst'' O'' c' cst' O' -> *)
(*   htsteps p t c cst O c' cst' O'. *)
            
(* Definition tskabsabt (p: hprog) (c: code) (cst: clientst) (O: osabst) t := *)
(*   exists ke' ks' cst' O', *)
(*     htstepstar p t c cst O (curs (hapi_code spec_abort), (ke', ks')) cst' O'. *)

(* Definition tskabsabt (p: hprog) (c: code) (cst: clientst) (O: osabst) t := *)
(*   exists ke' ks' cst' O', *)
(*     htsteps p t c cst O (curs (hapi_code spec_abort), (ke', ks')) cst' O'.  *)

(* abstract-level task potentially aborts before hitting any "sfexec" *) 
Definition tskabsabt (p: hprog) (c: code) (cst: clientst) (O: osabst) t :=
  (exists ke' ks' cst' O', htstepstar p t c cst O (curs (hapi_code spec_abort), (ke', ks')) cst' O') \/
    (exists ke' ks' cst' O' ev, htstepevstar p t c cst O (curs (hapi_code spec_abort), (ke', ks')) cst' O' ev).

(* Fixpoint ksapi (ks: stmtcont) (po: progunit) :=  *)
(*   match ks with *)
(*     kstop => False *)
(*   | kseq _ ks | kint _ _ _ ks | kassignr _ _ ks | kassignl _ _ ks | kfuneval _ _ _ _ ks | *)
(*     kif _ _ ks | kwhile _ _ ks | kret ks | kevent _ _ ks => ksapi ks po *)
(*   | kcall f _ _ ks => po f <> None /\ ksapi ks po *)
(*   end. *)

(* TaskSim is the definition of the simulation relation for tasks. *)  
(* New conditions are introduced to express that the simulation of a concrete execution step
     is only necessary if the assumptions in the task executing the abstract program are satisfied. *)  
CoInductive TaskSim: 
  lprog -> code -> taskst -> hprog -> code -> osabst -> 
  LocalInv -> Inv -> reltaskpred -> tid -> Prop :=
| task_sim :
  forall (pl:lprog) (ph:hprog) (Cl Ch:code) (o:taskst) (O:osabst)
         (t:tid) lasrt (I:Inv) (P:reltaskpred),
    (
      forall Cl' Ms Mf cst cst' o'' Os  o2  OO, 
        satp (substaskst o  Ms) Os (INV I)->
        joinm2 o Ms Mf o2 ->
        join O Os OO ->
        ltstep pl t Cl cst o2 Cl' cst' o'' ->
        ~enapi Cl pl -> 
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        ~tskabsabt ph Ch cst OO t ->
        (
          exists Ch' OO'  o'  Ms'  O' Os', 
            htstepstar ph t Ch cst OO Ch' cst' OO' /\
              joinm2 o' Ms' Mf o'' /\ 
              join O' Os' OO' /\ 
              satp (substaskst o' Ms') Os' (INV I) /\
              satp  o' O' (CurLINV lasrt t)  /\
              TaskSim pl Cl' o' ph Ch' O'  lasrt I P t
        )
    )->
    (
      forall Cl' Ms Mf cst cst' o'' Os  o2  OO, 
        satp (substaskst o  Ms) Os (INV I)->
        joinm2 o Ms Mf o2 ->
        join O Os OO ->
        ltstep pl t Cl cst o2 Cl' cst' o'' ->
        enapi Cl pl ->
        (
          (exists f vl tl ke ks, Ch = (curs (sfexec f vl tl), (ke, ks))) /\
            exists lb,  
              (lb = None \/ exists vl, lb = Some vl) /\ 
                forall Ch' OO' lb',
                  lb_equiv lb lb' ->
                  opt_htstep ph Ch cst OO Ch' cst' OO' lb' -> 
                  exists o' Ms' O' Os', 
                    (joinm2 o' Ms' Mf o'' /\ 
                       join O' Os' OO' /\ 
                       satp (substaskst o' Ms') Os' (INV I) /\
                       satp  o' O' (CurLINV lasrt t) /\
                       TaskSim pl Cl' o' ph Ch' O' lasrt I P t)
        )
    ) -> 
    (
      forall Cl' Ms Mf cst cst' o'' Os  o2  OO ev, 
        satp (substaskst o  Ms) Os (INV I)->
        joinm2 o Ms Mf o2 ->
        join O Os OO ->
        ltstepev pl t Cl cst o2 Cl' cst' o'' ev ->
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        ~tskabsabt ph Ch cst OO t ->
        (
          exists Ch' OO'  o'  Ms'  O' Os', 
            htstepevstar ph t Ch cst OO Ch' cst' OO' ev /\
              joinm2 o' Ms' Mf o'' /\ 
              join O' Os' OO' /\ 
              satp (substaskst o' Ms') Os' (INV I) /\
              satp  o' O' (CurLINV lasrt t)  /\
              TaskSim pl Cl' o' ph Ch' O'  lasrt I P t
        )
    )->  
    (
      forall   Ms ks x Os OO, 
        Cl = (curs (sprim (switch x)), (kenil, ks)) ->
        (*InOS Cl (pumerge (getapi pl) (getifun pl))->*)
        satp (substaskst o Ms)  Os  (INV I) ->                                          
        disjoint (getmem o) Ms -> 
        join O Os OO ->
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        (exists cst, ~tskabsabt ph Ch cst OO t) ->
        (
          exists Ch' s k  OO'  Mc ol O' Os' Ol Oc , 
            Ch' = (curs (hapi_code (spec_seq sched s)),k) /\
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO')  /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc O' /\
              satp (substaskst o Ms) Os'  (INV I) /\
              satp  (substaskst o Mc) Oc (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              (
                (
                  satp (substaskst o Mc) Oc (SWPRE_NDEAD (getsched ph) x t) /\
                    (
                      forall Mc' Oc' o' O'', 
                        satp  (substaskst o Mc') Oc' (SWINVt I t) ->
                        joinmem ol Mc' o' ->
                        join Ol Oc' O'' ->
                        TaskSim pl  (SKIP, (kenil, ks))  o'  ph (curs (hapi_code s),k) O''  lasrt I P t
                    )
                )
                \/                
                  satp (substaskst o Mc) Oc (SWPRE_DEAD (getsched ph) x t)  
              )
        )
    )->
    (
      forall Ms Os OO,  
        IsEnd Cl -> 
        satp (substaskst o Ms) Os  (INV I) ->   
        disjoint (getmem o) Ms -> 
        join O Os OO ->
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        (exists cst, ~tskabsabt ph Ch cst OO t) ->
        (
          exists O' Os' Ch OO', 
            IsEnd Ch /\
              (forall cst, htstepstar ph t Ch cst OO Ch cst OO') /\
              join O' Os' OO'/\
              satp (substaskst o  Ms) Os' (INV I) /\
              satp o O (CurLINV lasrt t) /\
              P (o, O')
        )
    )->
    (
      forall cst o' Ms Os Mf OO Of OOO,
        ~(IsEnd Cl) ->
        ~(IsSwitch Cl) ->
        ~(IsStkInit Cl)->
        ~(IsStkFree Cl) ->
        satp (substaskst o Ms)  Os  (INV I) ->
        joinm2 o Ms  Mf o' ->
        join O Os OO ->
        join OO Of OOO ->
        ltstepabt pl t Cl cst o' ->
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        ~tskabsabt ph Ch cst OOO t ->
        htstepabtstar ph t Ch cst OOO
    )->
    (
      forall  Ms Os e1 e2 e3 ks OO, 
        Cl = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
        satp (substaskst o Ms) Os (INV I) ->
        disjoint (getmem o) Ms ->
        join O Os OO ->
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        (exists cst, ~tskabsabt ph Ch cst OO t) ->
        (
          exists Ch'  v1 v2  t' p s k   OO' OO''  ,
          exists ol Mcre O' Os' Ol Ocre ,
            Ch' = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 p)) s)), k) /\
              evalval e1 (get_smem o) = Some v1  /\
              evalval e2 (get_smem o) = Some v2 /\ 
              evalval e3 (get_smem o) = Some (Vptr t') /\
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO')  /\
              abs_crt_step OO' OO'' t t' p /\
              joinmem ol Mcre o /\
              join O' Os' OO'' /\
              join Ol Ocre O' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp ol Ol (CurLINV lasrt t) /\
              satp (substaskst o Mcre) Ocre (lasrt t' init_lg**[|GoodLInvAsrt lasrt|]) /\
              TaskSim pl  (SKIP,(kenil,ks))  ol ph  (curs (hapi_code s),k) Ol  lasrt I P t
        )
    )->       
    (
      forall Ms  Os e ks  OO, 
        Cl = (curs (sprim (stkfree e)),(kenil,ks))->
        satp (substaskst o Ms) Os  (INV I) ->
        disjoint (getmem o) Ms  ->
        join O Os  OO ->
        (* newly introduced condition expressing that the assumptions in the task 
               executing the abstract program are satisfied *)  
        (exists cst, ~tskabsabt ph Ch cst OO t) ->
        (
          exists Ch' p s k t' OO' OO''  O' Os' ,
            Ch' = (curs (hapi_code (spec_seq (spec_del (Vint32 p)) s)),k) /\
              evalval e (get_smem o) = Some (Vptr t')  /\ 
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO') /\
              (
                (
                  abs_delself_step OO' OO'' t t' p /\
                    join O' Os' OO'' /\ 
                    satp (substaskst o Ms) Os' (INV I) /\
                    satp o O' (CurLINV lasrt t) /\
                    TaskSim pl (SKIP ,(kenil,ks))  o ph  (curs (hapi_code s),k)   O' lasrt I P t
                )
                \/
                  (
                    abs_delother_step OO' OO'' t t' p /\
                      join O' Os' OO'' /\ 
                      satp (substaskst o Ms) Os' (INV I) /\
                      satp o O' (CurLINV lasrt t) /\
                      forall o' O'' Mdel Odel,
                        (
                          satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                          joinmem o Mdel o' ->
                          join O' Odel O'' ->
                          TaskSim pl  (SKIP, (kenil,ks))  o' ph  (curs (hapi_code s),k)  O''  lasrt I P t
                        )
                  )
              )
        )
    )->       
    TaskSim pl Cl o ph Ch O  lasrt I P t.


Definition TaskSimAsrt  
           (pl:lprog) (Cl:code) (ph:hprog) (Ch:code) 
           (t:tid) lasrt (I:Inv) (P:reltaskpred):Prop:=
  forall (o:taskst) (O:osabst), 
    P (o, O)  /\  satp o O (CurLINV lasrt t)  -> TaskSim pl Cl o ph Ch O lasrt I P t.


Definition notabort (C:code):=
  ~IsSwitch C /\ ~IsEnd C /\ 
  ~ IsRet C /\ ~IsRetE C /\ ~IsIRet C /\ 
  ~IsStkInit C /\
  ~IsStkFree C.

Definition notabortm (C:code):= ~IsFcall C /\ notabort C.

(* MethSimMod is the definition of the simulation relation for methods *) 
(* new conditions are introduced to express that the simulation of a concrete execution step
     is only necessary if the assumptions in the abstract statement are satisfied *) 
CoInductive MethSimMod : funspec -> ossched ->  code -> taskst -> absop -> osabst  -> LocalInv ->
                         Inv -> retasrt -> asrt -> retasrt -> tid -> Prop :=
| meth_sim_mod :
    forall (spec :funspec) sd (C:code)  
           (gamma:absop) (O:osabst) t lasrt (I:Inv)
           (r q : retasrt) (ri: asrt)  (o:taskst) ,
      (
        forall p C' Ms Mf Os OO o2 o2',
          ~IsFcall C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO'  o' Ms'  O' Os', 
              hmstepstar sd gamma OO gamma' OO' /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO' /\
              satp (substaskst o'  Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSimMod spec sd C' o' gamma' O' lasrt I r ri q t
          )
      )->
      (
        forall Ms Os ks f vl tl OO,
          C = (curs (sfexec f vl tl), (kenil,ks)) ->
          satp (substaskst o  Ms) Os (INV I)->
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          ( 
            exists gamma' OO' om M O' Os' Ot Of ,
              exists pre post tp logicl,
                hmstepstar sd gamma OO gamma' OO' /\
                joinmem om M o /\
                join O' Os' OO' /\
                join Ot Of O'/\
                tl_vl_match tl vl = true /\
                spec f = Some (pre, post,  (tp ,List.rev tl)) /\
                sat (om, Ot, gamma') (getasrt (pre (rev vl) logicl t)) /\ 
                satp om Ot (CurLINV lasrt t) /\ 
                satp (substaskst o Ms) Os' (INV I) /\
                (
                  forall o1 O1  v gamma'', 
                    sat (o1,O1,gamma'') (getasrt (post (rev vl) v logicl t)) ->
                    (
                      satp o1 O1 (CurLINV lasrt t) /\ 
                      (
                        forall o' O'',
                          (* satp o' O'' (CurLINV lasrt t) -> *)
                          joinmem o1 M o' ->
                          join O1 Of O'' ->
                          eqenv o o' ->
                          MethSimMod spec sd (curs (sskip v), (kenil,ks)) o' gamma'' O'' lasrt I r ri q t 
                      )
                    )
                )
          )
      )->
      (
        forall Ms ks x Os OO, 
          C = (curs (sprim (switch x)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' s OO' ol Mc O' Os' Ol Oc,  
              gamma' = spec_seq sched s /\
              hmstepstar sd gamma OO gamma' OO' /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc  O' /\
              satp (substaskst o Ms) Os'  (INV I) /\
              satp (substaskst o Mc) Oc  (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              (
                (
                  satp (substaskst o Mc) Oc (SWPRE_NDEAD sd x t)  /\
                  (
                    forall Mc' Oc' o' O'', 
                      satp (substaskst o  Mc') Oc' (SWINVt I t)->
                      joinmem ol Mc' o' ->
                      join Ol Oc' O'' ->
                      MethSimMod spec sd (SKIP, (kenil, ks))  o' s O'' lasrt I r ri q t 
                  ) 
                )

                \/

                satp (substaskst o Mc) Oc  (SWPRE_DEAD sd x t) 
              )
          )
      )->

      (
        forall v Ms Os OO, 
          C = (curs (sskip v), (kenil, kstop)) ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (q v) 
          )
      )->

      (
        forall ks Os Ms OO,
          C = (curs sret, (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (r None)
          )
      )->

      (
        forall ks Os Ms v OO,
          C = ([v], (kenil, (kret ks))) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'), gamma')  (r (Some v)) 
          )
      )->
      
      (
        forall ks Os Ms OO,
          C = (curs (sprim exint), (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists  gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') ri 
          )
      )->
      (
        forall p Os Ms Mf o2 OO,                    
          notabortm C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 ->
          disjoint O Os ->
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          ~ (loststepabt p C o2)
      )->
      (
        forall  Ms Os e1 e2 e3 ks  OO, 
          C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' v1 v2 t' p s  OO'  OO'' ol , 
              exists Mcre O' Os' Ol Ocre ,
                gamma' = (spec_seq (spec_crt v1 v2 (Vint32 p)) s) /\
                evalval e1 (get_smem o) = Some v1 /\
                evalval e2 (get_smem o) = Some v2 /\ 
                evalval e3 (get_smem o) = Some (Vptr t') /\
                hmstepstar sd gamma OO gamma' OO' /\
                abs_crt_step OO' OO'' t t' p /\
                joinmem ol Mcre o /\
                join O' Os' OO'' /\
                join Ol Ocre O' /\
                satp (substaskst o Ms) Os' (INV I) /\
                satp ol Ol (CurLINV lasrt t) /\
                satp (substaskst o Mcre) Ocre (lasrt t' init_lg**[|GoodLInvAsrt lasrt|]) /\
                MethSimMod spec sd  (SKIP, (kenil,ks))  ol s Ol lasrt I r ri q t
          )
      )->
      (
        forall  Ms Os e ks OO, 
          C = (curs (sprim (stkfree e)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os OO->
          (* newly introduced condition expressing that the assumptions in the abstract statement
               are satisfied *) 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' p s t'  OO' ,
              gamma' = (spec_seq (spec_del (Vint32 p)) s) /\
              evalval e (get_smem o) = Some (Vptr t')  /\ 
              hmstepstar sd gamma OO gamma' OO' /\
              (
                ( 
                  exists OO'' O' Os', 
                    abs_delself_step OO' OO'' t t' p /\
                    join O' Os' OO'' /\ 
                    satp (substaskst o Ms) Os'  (INV I) /\
                    satp o O' (CurLINV lasrt t) /\
                    MethSimMod spec sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
                ) 
                \/ 
                (
                  exists OO'' O' Os', 
                    abs_delother_step OO' OO'' t t' p /\
                    join O' Os' OO'' /\ 
                    satp (substaskst o Ms) Os' (INV I) /\
                    satp o O' (CurLINV lasrt t) /\
                    forall o' O'' Mdel Odel,
                      (
                        satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                        joinmem o Mdel o' ->
                        join O' Odel O'' ->
                        MethSimMod spec sd  (SKIP, (kenil,ks))  o' s O''  lasrt I r ri q t
                      )
                )
              )
          )
      )->

      MethSimMod spec sd C o gamma O lasrt I r ri q t. (* | *)
  

Notation "  '{[' p , sd , li , I , r , ri , q  ']}'  '||-' t '(' C , o ')'  '<_msim' '(' gamma ,  O  ')' "
  :=  (MethSimMod p sd  C o gamma O li I r ri q t) (at level 200).     


CoInductive MethSim : progunit -> ossched -> code -> taskst -> absop -> osabst -> LocalInv ->
                      Inv -> retasrt -> asrt -> retasrt -> tid -> Prop :=
| meth_sim :
    forall (p:progunit) sd (C:code)
           (gamma:absop) (O:osabst) (I:Inv)
           (r q: retasrt) (ri: asrt)  (o:taskst) t lasrt,
      (
        forall  C' Ms Mf Os OO o2 o2',
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO'  o' Ms'  O' Os', 
              hmstepstar sd gamma OO gamma' OO' /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO' /\
              satp (substaskst o'  Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSim p sd C' o' gamma' O' lasrt I r ri q t
          )
      )->
      (
        forall  Ms ks x Os OO, 
          C = (curs (sprim (switch x)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' s OO' ol Mc O' Os' Ol Oc, 
              gamma' = spec_seq sched s /\
              hmstepstar sd gamma OO gamma' OO' /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc O' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp (substaskst o Mc)  Oc (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              (
                (
                  satp (substaskst o Mc) Oc (SWPRE_NDEAD sd x t)  /\
                  (
                    forall Mc' Oc' o' O'', 
                      satp (substaskst o  Mc') Oc' (SWINVt I t)->
                      joinmem ol Mc' o' ->
                      join Ol Oc' O'' ->
                      MethSim p sd (SKIP, (kenil, ks))  o' s O'' lasrt I r ri q t 
                  )
                )
                \/
                
                satp (substaskst o Mc) Oc (SWPRE_DEAD sd x t)
              )
          )
      )->
      (
        forall v Ms Os OO, 
          C = (curs (sskip v), (kenil, kstop)) ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (q v) 
          )
      )->
      (
        forall ks Os Ms OO,
          C = (curs sret, (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (r None)
          )
      )->
      (
        forall ks Os Ms v OO,
          C = ([v], (kenil, (kret ks))) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'), gamma')  (r (Some v)) 
          )
      )->
      (
        forall ks Os Ms OO,
          C = (curs (sprim exint), (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists  gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') ri 
          )
      )->
      (
        forall  Os Ms Mf o2 OO,    
          notabort C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 ->
          disjoint O Os ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          ~ (loststepabt p C o2)
      )->
      (
        forall  Ms Os e1 e2 e3 ks  OO, 
          C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' v1 v2 t' pri s  OO'  OO'' ol , 
              exists Mcre O' Os' Ol Ocre ,
                gamma' = (spec_seq (spec_crt v1 v2 (Vint32 pri)) s) /\
                evalval e1 (get_smem o) = Some v1 /\
                evalval e2 (get_smem o) = Some v2  /\  
                evalval e3 (get_smem o) = Some (Vptr t')  /\
                hmstepstar sd gamma OO gamma' OO' /\
                abs_crt_step OO' OO'' t t' pri /\
                joinmem ol Mcre o /\
                join O' Os' OO'' /\
                join Ol Ocre O' /\
                satp (substaskst o Ms) Os' (INV I) /\
                satp ol Ol (CurLINV lasrt t) /\
                satp (substaskst o Mcre) Ocre (lasrt t' init_lg**[|GoodLInvAsrt lasrt|]) /\
                MethSim p sd  (SKIP, (kenil,ks))  ol s Ol lasrt I r ri q t
          )
      )->
      (
        forall  Ms Os e ks OO, 
          C = (curs (sprim (stkfree e)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os OO->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' pri s t'  OO' OO'' O' Os' ,
              gamma' = (spec_seq (spec_del (Vint32 pri)) s) /\
              evalval e (get_smem o) = Some (Vptr t')  /\ 
              hmstepstar sd gamma OO gamma' OO' /\
              (
                (
                  abs_delself_step OO' OO'' t t' pri /\
                  join O' Os' OO'' /\ 
                  satp (substaskst o Ms) Os'  (INV I) /\
                  satp o O' (CurLINV lasrt t) /\
                  MethSim  p  sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
                ) 
                \/ 
                (
                  abs_delother_step OO' OO'' t t' pri /\
                  join O' Os' OO'' /\ 
                  satp (substaskst o Ms) Os' (INV I) /\
                  satp o O' (CurLINV lasrt t) /\
                  forall o' O'' Mdel Odel,
                    (
                      satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                      joinmem o Mdel o' ->
                      join O' Odel O'' ->
                      MethSim  p  sd  (SKIP, (kenil,ks))  o' s O''  lasrt I r ri q t
                    )
                )
              )
          )
      )->
      MethSim p sd C o gamma O lasrt I r ri q t.



Lemma buldp_some_imp_gooddecl : forall dl vl p, buildp dl vl = Some p -> good_decllist dl = true .
Proof.
  introv Hbul.
  inductions dl.
  simpl; auto.
  simpl.
  simpl in Hbul.
  remember (negb (in_decllist i dl) && good_decllist dl) as H.
  apply sym_eq in HeqH.
  destruct H.
  auto.
  inverts Hbul.
Qed.


Definition RuleSem (spec : funspec) (sd : ossched) lasrt (I:Inv) (r:retasrt) (ri:asrt) 
  (p:asrt) (s:stmts)  (q:asrt) t :Prop :=
  forall o O aop,  (sat ((o, O),aop) p /\  satp o O  (CurLINV lasrt t))  ->
                   (* ~(exists O', spec_stepstar sd aop O spec_abort O') ->  *) 
                   (* problem: with the compositionality results for seq and while,
                       we have no access to the condition that abstract ABORT cannot be reached
                       from a new abstract state reached after a statement *)   
                   MethSimMod spec sd (nilcont s) o aop O lasrt I r ri (lift q) t.


Definition MethSimAsrt (P : progunit) (sd:ossched) lasrt (I:Inv) (r:retasrt) (ri:asrt) 
  (p:asrt) (s:stmts)  (q:asrt) t :Prop :=
  forall o O aop, (sat ((o, O),aop) p /\  satp o O  (CurLINV lasrt t))  ->
                  (* ~(exists O', spec_stepstar sd aop O spec_abort O') ->  *)
                  MethSim P sd (nilcont s) o aop O lasrt I r ri (lift q) t.


Definition WFFuncsSim (P:progunit) (FSpec:funspec) (sd:ossched) lasrt (I:Inv) :Prop :=
  EqDom P FSpec /\
  forall f pre post t tl,
    FSpec f = Some (pre, post, (t, tl)) -> 
    exists  d1 d2 s,
      P f = Some (t, d1, d2, s)/\   
      tlmatch tl d1 /\
      good_decllist (revlcons d1 d2) = true /\ 
      (
        forall vl p r logicl tid,
          Some p = BuildPreI P f vl logicl pre tid-> 
          Some r = BuildRetI P f vl logicl post tid ->
          RuleSem FSpec sd lasrt I r Afalse p s Afalse tid
      ).



Definition WFFuncsSim' (P:progunit) (FSpec:funspec) (sd:ossched) lasrt (I:Inv) :Prop := 
  EqDom P FSpec /\
  forall f pre post t tl,
    FSpec f = Some (pre, post, (t, tl)) -> 
    exists  d1 d2 s,
      P f = Some (t, d1, d2, s)/\   
      tlmatch tl d1 /\
      good_decllist (revlcons d1 d2) = true /\ 
      (
        forall vl p r logicl tid,
          Some p = BuildPreI P f vl logicl pre tid -> 
          Some r = BuildRetI P f vl logicl post tid ->
          (
            forall o O aop,
              (o, O, aop) |= p /\ satp o O (CurLINV lasrt tid) -> 
              MethSim P sd (nilcont s) o aop O lasrt I r Afalse (lift Afalse) tid
          ) 
      ).


Notation " '[' Spec , sd , lasrt , I , r , ri  , n ']'  '|=' t '{{' pre  '}}' s '{{' post '}}' "
  := (RuleSem Spec sd lasrt I r ri pre s post n t) (at level 200).


Notation "  '{[' p , sd , lasrt , I , r , ri , q   ']}'  '||-' t '(' C , o ')'  '<_msim' '(' gamma ,  O  ')' "
  :=  (MethSimMod p sd C o gamma O lasrt I r ri q t) (at level 200).     


Notation "  '{{[' p , sc , lasrt , I , r , ri , q ']}}'  '||-' t '(' C , o ')'  '<_msim' '(' gamma ,  O  ')' "
  :=  (MethSim p sc C o gamma O lasrt I r ri q t) (at level 201).    
