
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import include_frm.
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Require Import kernel_sema_oper.
Require Import kernel_sema_oper_spec.

Require Import abs_infer_abt.
Require Import sem_common.

Require Import objauxvar_lemmas.
Require Import objaux_pure. 

Require Import obj_common.
Require Import obj_common_ext.

Require Import freeevtlist_lemmas.

(* Require Import abs_op. *)
Require Import ifun_spec. 

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(*************************************** sem_pend ****************************************)

Lemma absinfer_sem_pend_null_return :
  forall P k sch, 
    can_change_aop P ->
    k = Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| sem_pend (Vnull :: k :: nil) ||> ** P) 
                               (<|| END Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) ||> **  P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_null_return' :
  forall P k sch s, 
    can_change_aop P ->
    k = Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| spec_code_cons (sem_pend (Vnull :: k :: nil)) s ||> ** P) 
     (<|| s ||> **  P).
Proof.
  simpl spec_code_cons.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_null_return_abt :
  forall P k sch, 
    can_change_aop P ->
    k <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| sem_pend (Vnull :: k :: nil ) ||> ** P) 
      (<|| ABORT ||> **  P).
Proof.
  intros.
  unfold sem_pend.
  simpl.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_null_return_abt' :
  forall P k sch s, 
    can_change_aop P ->
    k <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) ->
    absinfer sch (<|| spec_code_cons (sem_pend (Vnull :: k :: nil)) s ||> ** P) 
      (<|| ABORT ||> **  P).
Proof.
  intros.
  simpl spec_code_cons.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_trans.
  Focus 2.
  eapply absinfer_seq_abt; try eauto.
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_no_active_evt_err:
  forall a P els tcbls curtid sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k = V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a :: k :: nil)) s ||> **
         HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| s ||> **
         HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  introv Hcop Hnone Hk.
  subst.
  simpl spec_code_cons.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_pend_no_active_evt_err_abt: 
  forall a P els tcbls curtid sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k <> V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a :: k :: nil)) s ||> **
         HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> ** 
         HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  introv Hcop Hnone Hne.
  simpl spec_code_cons.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
  can_change_aop_solver.
  instantiate (1:=ABORT).
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt. 
  can_change_aop_solver.
  can_change_aop_solver.
  intros; auto. 
Qed.

Lemma absinfer_sem_pend_from_idle_abt :
  forall a P els tcbls curtid sch k, 
    can_change_aop P ->
    (exists st, TcbMod.get tcbls curtid = Some (Int.repr OS_IDLE_PRIO, st)) ->
       absinfer sch
      (<|| sem_pend (Vptr a :: k :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  destruct H0.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls  ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 2 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_from_idle_err (|Vptr a :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_from_idle_abt' :
  forall a P els tcbls curtid sch k s, 
    can_change_aop P ->
    (exists st, TcbMod.get tcbls curtid = Some (Int.repr OS_IDLE_PRIO, st)) ->
       absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a :: k :: nil)) s ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  destruct H0.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 2 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  2: {
    eapply absinfer_seq_abt; try eauto.
  }
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_from_idle_err (|Vptr a :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_not_ready_abt :
  forall P els tcbls curtid st x prio sch k,
    TcbMod.get tcbls curtid = Some (prio, st) ->
    ~ st = rdy ->
    can_change_aop P ->
    absinfer sch
      (<|| sem_pend (Vptr x :: k :: nil) ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 3 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_not_ready_err (|Vptr x :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_not_ready_abt' :
  forall P els tcbls curtid st a prio sch k s,
    TcbMod.get tcbls curtid = Some (prio, st) ->
    ~ st = rdy ->
    can_change_aop P ->
    absinfer sch
      (<|| spec_code_cons (sem_pend (Vptr a :: k :: nil)) s ||> **
         HECBList els ** HTCBList tcbls  ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
         HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 3 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  2: { 
    eapply absinfer_seq_abt; try eauto.
  }
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_not_ready_err (|Vptr a :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_inst_get_return:
  forall P wls sid n tcbls curtid sch k infol sobjs els vhold tcblh tcbvl fecbh fecbvl,   
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| sem_pend (Vptr sid :: k :: nil) ||> **
          HECBList els ** HTCBList tcbls ** HCurTCB curtid **
          AOBJ infol sobjs els vhold tcblh tcbvl fecbh fecbvl ** P)
      ( <|| END Some (Vint32 (Int.repr OS_NO_ERR)) ||> **
          HECBList (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) **
          HTCBList tcbls ** HCurTCB curtid **
          AOBJ infol sobjs (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) vhold
          tcblh tcbvl fecbh fecbvl ** P).
Proof. 
  infer_solver 4%nat.
  unfold AOBJ in *.
  sep pauto.
  unfold AObjs in *.
  sep pauto.
  eapply RH_OBJ_ECB_P_set_minus_one; eauto.
  auto.
  auto.
  eapply obj_aux_p_sem_minus_one_preserve; eauto. 
Qed.

Lemma absinfer_sem_pend_inst_get_return':
  forall P wls sid n tcbls curtid sch k infol sobjs els vhold tcblh tcbvl fecbh fecbvl s,  
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k = Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr sid :: k :: nil)) s ||> **
        HECBList els ** HTCBList tcbls ** HCurTCB curtid **
        AOBJ infol sobjs els vhold tcblh tcbvl fecbh fecbvl ** P) 
      ( <|| s ||> **
        HECBList (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) **
        HTCBList tcbls ** HCurTCB curtid ** 
        AOBJ infol sobjs (EcbMod.set els sid (abssem (Int.sub n Int.one), wls)) vhold
                               tcblh tcbvl fecbh fecbvl ** P).
Proof.
  infer_solver 4%nat.
  unfold AOBJ in *.
  sep pauto.
  unfold AObjs in *.
  sep pauto.
  eapply RH_OBJ_ECB_P_set_minus_one; eauto.
  auto.
  auto.
  eapply obj_aux_p_sem_minus_one_preserve; eauto.
Qed.   

Lemma absinfer_sem_pend_inst_get_return_abt:
  forall P wls els sid n tcbls curtid sch k,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| sem_pend (Vptr sid :: k :: nil) ||> **
          HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
          HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  unfold sem_pend.
  simpl.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 4 try (eapply absinfer_trans; try(eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try(eapply absinfer_choice1; try eauto).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma absinfer_sem_pend_inst_get_return_abt':
  forall P wls els sid n tcbls curtid sch k s,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    k <> Vint32 (Int.repr OS_NO_ERR) ->
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr sid :: k :: nil)) s ||> **
        HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      ( <|| ABORT ||> **
        HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  do 4 try(eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans.
  2: {
    eapply absinfer_seq_abt; try eauto.
  }
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_inst_get_succ (|Vptr sid :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_block :
  forall P qid wl p st curtid tcbls sch k infol sobjs els vhold tcblh tcbvl fecbh fecbvl,
    can_change_aop P ->
    EcbMod.get els qid = Some (abssem Int.zero, wl) ->
    TcbMod.get tcbls curtid = Some (p, st) ->
    absinfer sch
      ( <|| sem_pend (Vptr qid :: k :: nil) ||>  ** 
          HECBList els ** HTCBList tcbls ** HCurTCB curtid **
          AOBJ infol sobjs els vhold tcblh tcbvl fecbh fecbvl ** P) 
      (<|| isched;; sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|);;
       sem_pend_block_get_succ (|Vptr qid :: k :: nil|) ||> **  
         HECBList (EcbMod.set els qid (abssem Int.zero, curtid::wl)) ** 
         HTCBList (TcbMod.set tcbls curtid (p, wait qid)) **   
         HCurTCB curtid ** 
         AOBJ infol sobjs (EcbMod.set els qid (abssem Int.zero, curtid::wl)) vhold 
         tcblh tcbvl fecbh fecbvl ** P). 
Proof.
  infer_solver 5%nat.
  unfold AOBJ in *.
  sep pauto.
  unfold AObjs in *.
  sep pauto.
  eapply RH_OBJ_ECB_P_set_wls'; eauto.
  auto.
  auto.
  eapply obj_aux_p_sem_set_wls'_preserve; eauto.
Qed.

Lemma absinfer_sem_pend_block' :
  forall P qid wl p st curtid tcbls sch k infol sobjs els vhold tcblh tcbvl fecbh fecbvl s, 
    can_change_aop P ->
    EcbMod.get els qid = Some (abssem Int.zero, wl) ->
    TcbMod.get tcbls curtid = Some (p, st) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_pend (Vptr qid :: k :: nil)) s ||>  ** 
           HECBList els ** HTCBList tcbls ** HCurTCB curtid **
           AOBJ infol sobjs els vhold tcblh tcbvl fecbh fecbvl ** P) 
      (<|| isched;; sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|);;
       (sem_pend_block_get_succ (|Vptr qid :: k :: nil|) ;; s) ||> ** 
           HECBList (EcbMod.set els qid (abssem Int.zero, curtid::wl)) ** 
           HTCBList (TcbMod.set tcbls curtid (p,wait qid) ) **
           HCurTCB curtid **
           AOBJ infol sobjs (EcbMod.set els qid (abssem Int.zero ,curtid::wl)) vhold tcblh tcbvl fecbh fecbvl ** P).
Proof.
  infer_solver 5%nat.
  unfold AOBJ in *.
  sep pauto.
  unfold AObjs in *.
  sep pauto.
  eapply RH_OBJ_ECB_P_set_wls'; eauto.  
  auto.
  auto.
  eapply obj_aux_p_sem_set_wls'_preserve; eauto.  
Qed.

(*---------------------------------------------------------------------*)

Lemma absinfer_sem_pend_p_aftersch :
  forall qid P els tcbls curtid sch k p st, 
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st) ->
     st = rdy ->  
    absinfer sch
      (<|| sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|) ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| END None ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_p_aftersch' :
  forall qid P els tcbls curtid sch k p st s, 
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st) ->
     st = rdy -> 
    absinfer sch
      (<|| sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|) ;; s ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| s ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_p_aftersch_abt :
  forall qid P els tcbls curtid sch k p st,  
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st) ->
     ~(st = rdy) ->
    absinfer sch
      (<|| sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|) ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s); 
         instantiate (2 := sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_p_aftersch_abt' :
  forall qid P els tcbls curtid sch k p st s,  
    can_change_aop P ->
    TcbMod.get tcbls curtid = Some (p, st) -> 
    ~(st = rdy) -> 
    absinfer sch
      (<|| sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|) ;; s ||> **
                                                                  HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
         HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans;
    try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver;
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|));
         sep pauto).
Qed.

Lemma absinfer_sem_pend_block_get_succ :
  forall qid P tcbls curtid sch k p s, 
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, rdy) ->
     k = V$ OS_NO_ERR -> 
    absinfer sch
      (<|| sem_pend_block_get_succ (|Vptr qid :: k :: nil|);; s ||> **
           HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| s ||> **
           HTCBList tcbls ** HCurTCB curtid ** P).
Proof.  
  infer_solver 0%nat.
Qed.

Lemma absinfer_sem_pend_block_get_succ_abt :
  forall qid P tcbls curtid sch k p s, 
    can_change_aop P ->
    TcbMod.get tcbls curtid = Some (p, rdy) ->
    k <> V$ OS_NO_ERR ->     
    absinfer sch
      (<|| sem_pend_block_get_succ (|Vptr qid :: k :: nil|) ;; s ||> **
               HTCBList tcbls ** HCurTCB curtid ** P)
      (<|| ABORT ||> **
               HTCBList tcbls ** HCurTCB curtid ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans;
    try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver. 
    try (instantiate (3 := s0); 
         instantiate (2 := sem_pend_rdy_after_sched (|Vptr qid :: k :: nil|));
         sep pauto).
Qed.

Require Import sempend_pure.
Require Import sempend_pure_ext.

Require Import os_program.


(* use this old hoare_if to avoid large modification *)
Ltac lzh_find_ret_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete _ => constr:(some 1%nat)
        | _ => lzh_find_ret_stmt rs
      end
    | srete _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac lzh_hoare_if2 :=
  hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                            ?v <> Vnull /\
                                            ?v <> Vundef|]}} ?stmts {{_}} =>
      (* idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve CltEnvMod.beq_refl: brel .
Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Require Import seplog_pattern_tacs.
Require Import tcblist_setnode_lemmas. 

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 

Lemma ele_lst_cons: 
  forall {A: Type} (e: A) (l: list A), (e :: nil) ++ l = e :: l. 
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma semacc_new_fundation: 
  forall s P a msgq mq a' msgq' mq' n wls i x2 x3 x4 qid b tcbls, 
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    R_ECB_ETbl_P qid (a, b) tcbls ->
    a = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 n :: x2 :: x3 :: x4 :: nil) ->
    msgq = DSem n ->
    mq = (abssem n, wls) ->
    Int.ltu Int.zero n = true ->
    a' = (V$OS_EVENT_TYPE_SEM :: Vint32 i :: Vint32 (n-ᵢ$ 1)  :: x2 :: x3 :: x4 :: nil) -> 
    msgq' = DSem (n-ᵢ$ 1) ->
    mq' = (abssem (n-ᵢ$ 1), wls) ->
    s |= AEventData a' msgq' **
      [| RLH_ECBData_P msgq' mq' |] ** 
      [| R_ECB_ETbl_P qid (a',b) tcbls |] ** P.
Proof.   
  intros.
  sep pauto.
  unfold AEventData in *.
  sep pauto.
  apply semacc_ltu_trans; auto.
  unfold RLH_ECBData_P in *.
  destruct H0.
  split.
  auto.  
  unfold RH_ECB_P in *.
  destruct H2.
  split.
  intros.
  apply H2; auto.
  intros.
  apply H2 in H5.
  tryfalse.
Qed.

Lemma semacc_RH_TCBList_ECBList_P_hold:
  forall mqls tcbls ct a n wl,
    RH_TCBList_ECBList_P mqls tcbls ct ->
    get mqls a = Some (abssem n, wl) ->
    Int.ltu Int.zero n = true ->
    RH_TCBList_ECBList_P 
      (set mqls a (abssem (Int.sub n Int.one), wl)) tcbls ct.
Proof.   
  intros.
  unfold RH_TCBList_ECBList_P in *.
  rename H into Hsem.
  intuition.

  unfold RH_TCBList_ECBList_SEM_P in *.
  destruct Hsem as [F1 F2].
  intuition.
  destruct (dec a eid) eqn:Feq.
  subst.
  rewrite set_a_get_a in H2; eauto.
  inverts H2.
  eapply F1.
  split; eauto.

  eapply F1.
  split;
    [ rewrite set_a_get_a' in H2; eauto
    | eauto].

  destruct (dec a eid) eqn:Feq.
  subst.
  apply F2 in H; mytac.
  Ltac gel H :=
    match type of H with
      | ?A = ?B =>
        change ((fun y => y = B) A) in H
    end.
  gel H0.
  rewrite H in H0.
  inverts H0.
  rewrite set_a_get_a.
  do 2 eexists.
  eauto.

  rewrite set_a_get_a'.
  apply F2 in H; mytac.
  do 2 eexists.
  eauto.
  auto.
Qed.

Lemma TcbMod_set_R_PrioTbl_P_hold :
  forall ptbl tcbls ptcb pr st st' av,
    R_PrioTbl_P ptbl tcbls av ->
    TcbMod.get tcbls ptcb = Some (pr, st) ->
    R_PrioTbl_P ptbl (TcbMod.set tcbls ptcb (pr,st')) av.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  mytac.
  splits.
  {
    intros.
    lets H100 : H H3 H4 H5.
    mytac.
    rewrite TcbMod.set_sem.
    unfold get in *; simpl in *.
    rewrite H7.
    remember (tidspec.beq ptcb tcbid) as bool; destruct bool.
    symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
    subst.
    rewrite H0 in H7.  
    inverts H7.
    eauto.
    eauto.
  }
  {
    intros.
    rewrite TcbMod.set_sem in H3.
    remember (tidspec.beq ptcb tcbid) as bool; destruct bool.
    inverts H3.
    symmetry in Heqbool; apply tidspec.beq_true_eq in Heqbool.
    subst.
    eapply H1; eauto.
    eapply H1; eauto.
  }
  eapply  R_Prio_NoChange_Prio_hold; eauto.
Qed.

Lemma rtbl_remove_RL_RTbl_PrioTbl_P_hold :
  forall prio y bitx rtbl ry ptbl vhold,
    0 <= Int.unsigned prio < 64 ->
    y = Int.shru (prio) ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and (prio) ($ 7)) ->
    nth_val ∘(Int.unsigned y) rtbl = Some (Vint32 ry) ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold->
    RL_RTbl_PrioTbl_P
     (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (ry&ᵢInt.not bitx))) ptbl vhold.
Proof.
  introv Hpr Hy Hbit Hnth Hrl.
  subst.
  unfolds. 
  unfolds in Hrl.
  intros.
  assert (p = prio \/ p <> prio) by tauto.
  destruct H1.
  subst.
  unfolds in H0.
  assert ( prio&ᵢ$ 7  =  prio&ᵢ$ 7 ) by auto.
  assert (Int.shru prio ($ 3)  =  Int.shru prio ($ 3)) by auto.
  lets Hf : H0  (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7))) H1 H2.
  assert ( (ry&ᵢInt.not ($ 1<<ᵢ(prio&ᵢ$ 7)))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 1<<ᵢ(prio&ᵢ$ 7)).
  apply Hf.
  eapply update_nth; eauto.
  rewrite Int.and_assoc in H3.
  assert (Int.not ($ 1<<ᵢ(prio&ᵢ$ 7))&ᵢ($ 1<<ᵢ(prio&ᵢ$ 7)) = $ 0).
  rewrite Int.and_commut. 
  rewrite Int.and_not_self; auto.
  rewrite H4 in H3.
  rewrite Int.and_zero in H3.
  assert ($ 1<<ᵢ(prio&ᵢ$ 7) <> $ 0) by (apply math_prop_neq_zero2; eauto).
  unfold Int.zero in H3.
  tryfalse.
  eapply Hrl; auto.
  eapply prio_neq_in_tbl with (prio0 :=p)(prio:=prio); eauto.
Qed.  

Lemma TCBList_P_tcb_dly_hold' :
  forall v ptcb rtbl vl y bitx tcbls prio ry x1 tcs tcs' t,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.join (TcbMod.sig ptcb (prio, t)) x1 tcs ->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  intros.
  subst.
  eapply update_rtbl_tcblist_hold;eauto.
  unfolds in H5.
  intros.
  eapply H5;eauto.
  eapply tcbjoin_join_get_neq; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold'' :
  forall v ptcb rtbl vl y bitx tcbls prio ry x1 tcs tcs' t,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.join (TcbMod.sig ptcb (prio, t)) x1 tcs ->
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  introv Hran Htc Hy Hb Hpro Hnth.
  eapply TCBList_P_tcb_dly_hold'; eauto.
Qed.

Lemma TCBList_P_tcb_block_hold':
  forall v ptcb rtbl vl y bitx tcbls prio ry tcs tcs' t,
    0 <= Int.unsigned prio < 64 ->
    TcbMod.get  tcs ptcb = Some (prio, t) -> 
    TcbMod.join tcbls tcs tcs' -> 
    TCBList_P v vl rtbl tcbls ->
    y = Int.shru prio ($ 3) ->
    bitx = ($ 1) <<ᵢ (Int.and prio ($ 7)) ->
    prio_neq_cur tcbls ptcb  prio ->
    nth_val (nat_of_Z (Int.unsigned y)) rtbl = Some (Vint32 ry) ->
    TCBList_P v vl (update_nth_val ∘(Int.unsigned y) rtbl (Vint32 (Int.and ry (Int.not bitx)))) tcbls.
Proof.
  intros.
  lets Hx:tcb_get_join H0.
  mytac.
  eapply TCBList_P_tcb_block_hold'';eauto.
Qed.

Lemma kernel_sema_pend_proof: 
  forall vl p r logicl ct, 
    Some p =
      BuildPreI os_internal OSSemPend vl logicl OSSemPendPre ct->
    Some r =
      BuildRetI os_internal OSSemPend vl logicl OSSemPendPost ct->
    exists t d1 d2 s,
      os_internal OSSemPend = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  (* rename v'1 into etype. *)
  change ((x :: nil) ++ v'1 :: nil) with (x :: v'1 :: nil).
  subst.
  rename v'1 into errcode.

  hoare forward prim.
  hoare unfold.
  
  lzh_hoare_if2.
  subst.

  assert (Het: errcode = Vint32 (Int.repr OS_ERR_PEVENT_NULL) 
               \/ errcode <> Vint32 (Int.repr OS_ERR_PEVENT_NULL)) by tauto.
  destruct Het.
  subst.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_null_return'; pure_auto.
  hoare forward prim.
  pure_auto.
  (* return OS_ERR_PEVENT_NULL *) 
  hoare forward.  
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_null_return_abt';
  try can_change_aop_solver; try eauto.
  eapply absabort_rule.  

  (* ptr <> NULL *)
  rename x into p.

  hoare unfold.
  unfold AOBJ.
  hoare normal pre.
  hoare_ex_intro.  
  hoare_split_pure_all.
  subst. (* addr of placeholder is now vhold_addr *)

  hoare_lifts_trms_pre tcbllsegobjaux.
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegobjaux_split3_join2_frm in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assert_pure (Vptr v'30 = v'6).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (llsegobjaux, AOSTCBList).
    eapply tcblist_llsegaux_match_tn_frm in Hsat; eauto.
  }
  hoare_split_pure_all.
  subst v'6.

  hoare_assert_pure (ct = v'30).
  {
    get_hsat Hsat.
    unfold AOSTCBList in Hsat.
    sep normal in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    simpljoin1.
    congruence. 
  }
  hoare_split_pure_all.
  rename H0 into Hcteq. (* ct = ... *)

  unfold p_local at 2. 
  unfold OSLInv at 3.
  
  unfold LINV.
  hoare_split_pure_all.
  inverts H0. inverts H13. (* logiv_val ... :: ... = logic_val ... :: ... *)  
  
  hoare_assert_pure (Vptr p = v'22). { gen_eq_ptr. } 
  hoare_split_pure_all. subst v'22.
  rename v'21 into ptrmp. 
  assert (Hevptr: get ptrmp ct = Some (Vptr p)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    subst ct. join auto.
  }
  hoare_assert_pure (v'15 = V$ os_code_defs.__Loc_normal).
  { gen_eq_loc. }
  hoare_split_pure_all. 
  subst v'15.
  subst v'30. (* current task id is ct *)
  rename v'0 into locmp.
  assert (Hevloc: get locmp ct = Some (V$ os_code_defs.__Loc_normal)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  rename v'12 into els.
  rename v'18 into fecbh.
  rename v'1 into fecbvl.
  rename v'20 into eibs.
  
  assert (Hevt: is_kobj els p \/ ptr_in_ecblist (Vptr p) fecbh fecbvl).  
  { eapply obj_aux_nml; eauto. }  

  destruct Hevt as [Hevt | Hfree].
  Focus 2.
  (* pevent points into list of free ECBs *)
  hoare_assert_pure (exists p, fecbh = Vptr p).
  {
    unfold ptr_in_ecblist in Hfree.
    lets Hptr: ptr_in_ecbsllseg_ptr Hfree.
    eauto.
  }
  hoare_split_pure_all.
  subst. 
  eapply backward_rule1.
  introv Hsat.
  unfold AOSEventFreeList in Hsat.
  unfold ecbf_sll in Hsat.
  sep normal in Hsat.
  sep_lifts_trms_in Hsat ecbf_sllseg.
  eapply ecbf_sllseg_split3_frm; eauto.
  hoare unfold.
  Set Printing Depth 99.
  lzh_hoare_if. 
  2: {
    change (Int.eq ($ OS_EVENT_TYPE_UNUSED) ($ OS_EVENT_TYPE_SEM)) with false in Hif_false. 
    inverts Hif_false.
  }
  unfold AECBList.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Astruct, evsllseg).

  hoare_assert_pure (get els (v'21, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: semcre_ecblist_star_not_inh H0 Hsat. 
    auto.
  }
  hoare_split_pure_all.
  rename H13 into Hnone.   

  casetac errcode (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_pend_no_active_evt_err_abt; try pure_auto.
    go. unfold CurTid. go.
    eapply absinfer_eq. 
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_no_active_evt_err; eauto. 
  go. unfold CurTid. go.
  eapply absinfer_eq.  

  (* EXIT_CRITICAL *) 
  hoare forward prim. 
  unfold AECBList.
  sep normal.
  eexists.
  sep cancel OSEventList.
  sep cancel evsllseg.
  sep split; eauto.
  sep cancel tcbdllflag.
  unfold p_local. sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto. 
  instantiate (2:=v'1++((V$ OS_EVENT_TYPE_UNUSED
              :: Vint32 i :: Vint32 i1 :: x2 :: x3 :: v'20 :: nil) :: v'12)).
  instantiate (2:=Vptr v'0).
  unfold AOSEventFreeList.
  sep normal.
  sep cancel OSEventFreeList.
  unfold ecbf_sll.
  sep_lifts_trms ecbf_sllseg. 
  eapply ecbf_sllseg_compose3_frm; eauto. 
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel ecbf_sllseg.
  sep cancel ecbf_sllseg.

  2: { go. }
  2: { go. }
  unfold AOBJ.
  sep pauto; eauto.
  sep cancel AObjs.
  unfold tcbllsegobjaux.
  eapply llsegobjaux_merge2_frm; eauto.
  sep cancel llsegobjaux.
  eapply llsegobjaux_merge_hd; eauto.
  go. 

  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.
  
 (* pevent points to an active ECB *) 
  Set Printing Depth 99.
  unfold AECBList.
  hoare unfold.
  rename H0 into H_elp.
  assert (Hecb: exists ecb, get els p = Some ecb). 
  {
    unfold is_kobj in Hevt.
    simpljoin1; eexists; eauto.
  }
  destruct Hecb as (ecb & Hgetecb).
  destruct ecb. 
  lets Hctr: ECBList_P_get_ectr_some Hgetecb H_elp.
  destruct Hctr as (evl & etbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  hoare_assert_pure (length v'6 = length v'15).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg. 
    eapply evsllseg_aux in Hsat. 
    destruct Hsat.
    eauto. 
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H00: ecblist_p_decompose H_elp; eauto. 
  destruct H00 as (x' & els1 & els2 & H''). 
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).
  destruct Hjo as (Hjo & Hptror).
  hoare_assert_pure (x' = Vptr (v'29, Int.zero)). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.
  
  assert (Hecbl' := Hecbl2).
  do 2 (rewrite ele_lst_cons in Hecbl'). 
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hex). (* add Hecbpetbl *)
  inverts Hqid. 
  destruct Hex as (absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.
  
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (v'29, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.

  assert (Hnone: get els (v'29, Int.zero) = None).
  {
    destruct (get els (v'29, Int.zero)) eqn: E.
    false. destruct p. destruct e0. apply H0. do 2 eexists; eauto.
    auto. 
  }

  casetac errcode (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid). 
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_pend_no_active_evt_err_abt; eauto. 
    go. unfold CurTid. go.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_no_active_evt_err; eauto.
  go. unfold CurTid. go.
  eapply absinfer_eq.  

  fold_AEventNode_r. 
  (* EXIT_CRITICAL *)
  hoare forward prim.
  sep cancel tcbdllflag. 
  unfold p_local. sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto. 
  get_hsat Hsat.
  eapply lzh_evsllseg_compose in Hsat; eauto.
  eapply AECBList_fold in Hsat; eauto. 
  sep cancel AECBList.
  unfold AOBJ.
  sep pauto; eauto.
  sep cancel AObjs.
  unfold tcbllsegobjaux.
  eapply llsegobjaux_merge2_frm; eauto.
  sep cancel llsegobjaux.
  eapply llsegobjaux_merge_hd; eauto.
  go. (* GoodFrm *) 
  
  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.
  
 (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists wls, v'20 = DSem i1 /\ absmq = (abssem i1, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: { go. }
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H0 as (Hdsem & Habssem). 
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (v'29, Int.zero) = Some (e, w)) 
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  subst.
  
  (*******************************  type = sem ********************************)
  lzh_simpl_int_eq. 
  hoare_unfold. 
  
  assert (Fget: exists p st, TcbMod.get v'13 ct = Some (p, st)). 
  {
    mttac RH_CurTCB ltac:(fun H=> clear -H; rename H into H_).
    unfold RH_CurTCB in H_. 
    auto.
  }
  destruct Fget as [cur_p]. 
  assert (Hcur_p: cur_p = $ OS_IDLE_PRIO \/ cur_p <> $ OS_IDLE_PRIO) by tauto.
  destruct Hcur_p as [Hcur_p | Hcur_p].

  (*****************************  Curtid == OS_IDLE_PRIO *********************)
  subst cur_p.
  fold_AEventNode_r.
  compose_evsllseg.
  fold_AECBList.

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).
  eapply abscsq_rule; eauto.  
  eapply absinfer_sem_pend_from_idle_abt';
    try can_change_aop_solver; try eauto.
  unfold CurTid. go.
  eapply absinfer_eq.
  eapply absabort_rule.
  (******************** Curtid == idle finished *********************)
  (******************** Curtid <> idle begin: ***********************)  

  (******************** OSTCBCur is not rdy : a weird situation !*************************)
  destruct H0 as [cur_st]. 
  assert (Hcur_st: cur_st <> rdy \/ cur_st = rdy) by tauto.
  destruct Hcur_st as [Hcur_st | Hcur_st].

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).
  eapply abscsq_rule; eauto.    
  eapply absinfer_sem_pend_not_ready_abt';
    try can_change_aop_solver; try eauto.
  unfold CurTid. go.
  eapply absinfer_eq. 
  eapply absabort_rule. 

  (********* OSTCBCur is not rdy finished ****************)
  subst cur_st.

  (****************** cnt > 0, succ return ******************)
  hoare_unfold. 
  lzh_hoare_if2. 
  
  hoare forward.
  (* pure_auto. *)
  struct_type_match_solver.
  unfold p_local.
  sep normal. sep cancel CurTid.
  unfold LINV, OSLInv. sep pauto. 

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_skp_in Hsat (objaux_node, (llsegobjaux, _N_ 1)). 
  eapply llsegobjaux_merge_hd in Hsat; eauto. 
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_skp_in Hsat ((llsegobjaux, _N_ 1), (llsegobjaux, _N_ 0)).  
  eapply llsegobjaux_merge2_frm with (locmp:=set locmp ct (V$ __Loc_normal)); eauto.
  rewrite get_set_same; eauto.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (absobjsid, AObjs, llsegobjaux).
      
  match type of Hsat with
    _ |= HObjs ?objs ** AObjs ?objl ?objs ?ecbls ?vhold ** llsegobjaux ?tcblh _ ?vl _ _ _ ** ?Q =>
      instantiate (1 := AOBJ objl objs ecbls vhold_addr tcblh vl fecbh fecbvl  ** Q)
  end.
  sep pauto.
  sep cancel Aisr. sep cancel Aie. sep cancel Ais. sep cancel Acs. sep cancel Aop.
  sep cancel A_dom_lenv.
  unfold AOBJ.
  rewrite get_set_same in Hsat; eauto.
  sep pauto.
  
  hoare_lifts_trms_pre AOBJ.   
  
  assert (Het: errcode = Vint32 (Int.repr OS_NO_ERR) 
                \/ errcode <> Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Het. 
  subst.
  (* etype = OS_NO_ERR  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).
  eapply abscsq_rule; eauto.    
  eapply absinfer_sem_pend_inst_get_return'; pure_auto.
  unfold CurTid. go. 
  eapply absinfer_eq.
  
  
  (******* fold AECBList  *****)
  transform_pre semacc_new_fundation ltac:(sep cancel AEventData).
  hoare_split_pure_all.
  fold_AEventNode_r.
  compose_evsllseg.
  assert (Hjo_: EcbMod.join (sig (v'29, Int.zero) (abssem i1, v'1)) mqls' els2).
  { join auto. }
  lets Hnewjoin: ecb_get_set_join_join Hsem Hjo_ Hjo. 
  mytac.

  assert (
      ECBList_P v'0 Vnull
        (v'6 ++
           ((V$ OS_EVENT_TYPE_SEM
               :: Vint32 i :: Vint32 (i1 -ᵢ $ 1) :: x2 :: x3 :: v'' :: nil, etbl) :: nil) ++ 
           v'12)
        (v'15 ++ (DSem (i1-ᵢ$ 1) :: nil) ++ v'18) 
        (EcbMod.set els (v'29, Int.zero) (abssem (i1 -ᵢ Int.one), v'1)) 
        v'13).
  {
    eapply semacc_compose_EcbList_P; eauto.
  }
  clear H_elp. 
  fold_AECBList.
  hoare forward prim.
  sep cancel AOBJ. 
  sep cancel tcbdllflag.
  unfold p_local.
  sep normal. sep cancel CurTid. unfold LINV, OSLInv. sep pauto.
  eapply semacc_RH_TCBList_ECBList_P_hold; eauto.
  pure_auto.
  (* RETURN ′ OS_NO_ERR *) 
  hoare forward.
  simpl. introv Hf. inverts Hf. 

  (* errcode <> OS_NO_ERR  *)
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).
  eapply abscsq_rule; eauto.    
  eapply absinfer_sem_pend_inst_get_return_abt';
    try can_change_aop_solver; try eauto.
  unfold CurTid. go.
  eapply absinfer_eq. 
  eapply absabort_rule.

  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_skp_in Hsat (objaux_node, (llsegobjaux, _N_ 1)).    
  eapply llsegobjaux_merge_hd in Hsat; eauto. 
  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_skp_in Hsat ((llsegobjaux, _N_ 1), (llsegobjaux, _N_ 0)).  
  eapply llsegobjaux_merge2_frm; eauto.  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (absobjsid, AObjs, llsegobjaux). 
      
  match type of Hsat with
    _ |= HObjs ?objs ** AObjs ?objl ?objs ?ecbls ?vhold ** llsegobjaux ?tcblh _ ?vl _ _ _ ** ?Q =>
      instantiate (1 := AOBJ objl objs ecbls vhold tcblh vl fecbh fecbvl  ** Q)
  end.
  sep auto.
  unfold AOBJ. exists locmp. exists ptrmp.  
  sep auto.
  
  (********************** cnt > 0 finished ***************************)
  
  unfold AOSTCBList.
  hoare_assert_pure (get_last_tcb_ptr v'7 v'5 = Some (Vptr ct)). 
  {
    get_hsat Hsat. 
    sep normal in Hsat.  sep destruct Hsat.
    sep_lifts_trms_in Hsat (tcbdllseg v'5). 
    eapply tcbdllseg_get_last_tcb_ptr; eauto. 
  }
  hoare_split_pure_all.
  rename H36 into Hlast.
  hoare unfold. 

  assert (Fget: exists st, TcbMod.get v'22 (v'32, Int.zero) = Some (i5, st)). 
  {
    lets Ftmp: TCBListP_head_in_tcb H35; eauto. 
  }
  destruct Fget as [st]. rename H7 into Fget. 
  lets Fget': TcbMod.join_get_r H33 Fget. 
  rewrite Fget' in H0. inverts H0.
  assert (Hveq: x9 = Vnull /\ i6 = $ OS_STAT_RDY).
  {
    lets Hget_r: get_tcb_stat_rdy H35 Fget. 
    unfold V_OSTCBStat,V_OSTCBEventPtr in Hget_r.
    simpl in Hget_r.
    clear -Hget_r.
    destruct Hget_r; pauto.
  }
  destruct Hveq as (Hvptr & Hvst).
  subst x9. subst i6.

  hoare forward. 
  struct_type_match_solver.
  unfold p_local.
  sep normal. sep cancel CurTid.
  unfold LINV, OSLInv. sep pauto. 
  assert (Hor: Int.or ($ OS_STAT_RDY) ($ OS_STAT_SEM) = ($ OS_STAT_SEM)). 
  {
    change ($ OS_STAT_RDY) with (Int.zero).
    rewrite Int.or_commut.
    apply Int.or_zero.
  }
  rewrite Hor.  
  hoare forward.
  unfold p_local.
  sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto. 

  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop).  
  transform_pre a_isr_is_prop_split ltac:(idtac).
(*   unfold AOSRdyTblGrp. *)
(*   unfold AOSRdyTbl. *)
(*   unfold AOSRdyGrp. *)
  hoare_split_pure_all.

  hoare_unfold.
  hoare forward.
  
  unfold node.
  sep pauto.
  sep cancel Astruct.
  instantiate  (3:=DSem i1).
  unfold AEventNode.
  sep cancel AEventData. (* new add *)
  unfold AOSEvent.
(*   unfold AEventData. *)
  unfold node.
  sep cancel AOSRdyTblGrp.
(*   unfold AEventData. *)
  (* unfold AOSRdyTblGrp. *)
(*   unfold AOSRdyTbl. *)
(*   unfold AOSRdyGrp. *)
  unfold AOSEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel Astruct.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop.
  unfold p_local. sep normal. sep cancel CurTid.
  unfold LINV, OSLInv. sep pauto. 

  eauto. 
  eauto. 
  eauto. 
  eauto. 
  
  split; auto.
  struct_type_match_solver.
  split; auto.
  struct_type_match_solver.

  split; simpl ; eauto.
  eexists. split. unfolds; simpl ; eauto.
  apply Int.eq_false; eauto.

  eapply tcblist_p_node_rl_sem; eauto.
  pure_auto.

  intros.
  sep auto.
  intros.
  sep auto.

  hoare_ex_intro.
  unfold OS_EventTaskWaitPost.
  unfold OS_EventTaskWaitPost'.
  unfold getasrt.

  hoare_split_pure_all. 
  lzh_inverts_logic.
  inverts H36.
  unfold V_OSTCBY,V_OSTCBBitX,V_OSTCBBitY,V_OSEventGrp in H37. 
  simpl in H37. 
  mytac_H.
  inverts H36.
  inverts H37.
  inverts H38.
  inverts H55.
 
  (******************  function call finished **************)  

 assert (Hcnt:i1 = $ 0).
  {
    clear -H17. 
    apply semacc_ltu_zero_false.
    auto.
  }
  
  subst i1.

  assert (Heg: EcbMod.get els (v'29,Int.zero) = Some (abssem Int.zero, v'1)). 
  {
    eapply EcbMod.join_get_r; eauto.
    eapply EcbMod.join_sig_get; eauto.
    clear -Hjo'.
    unfold TcbJoin in Hjo'.
    join auto.  
  }

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid, AOBJ).   
  eapply abscsq_rule. 
  go. 
  eapply absinfer_sem_pend_block'; eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 

  unfold AOSTCBPrioTbl.
  hoare_split_pure_all.
  lets cp : H35. 
  destruct cp as (td & vv & tcblss & asbs & Hveq & Hnes & Htcj & Htp & Htlis).
  destruct asbs.
  unfolds in Htp.
  destruct Htp as (_ & Hrsl & _).
  
  funfold Hrsl. 
  assert (0<= Int.unsigned x < 64).
  {
    clear -H58 H66.
    Require Import Lia. 
    lia.
  }
  assert (prio_neq_cur v'13 (v'32, Int.zero) x). 
  {
    eapply R_PrioTbl_P_impl_prio_neq_cur; eauto.
  }
  inverts Hveq.

  hoare_lifts_trms_pre (Aisr, Ais). 
  transform_pre add_a_isr_is_prop ltac:(idtac).
  simpl update_nth_val. 

  assert (Htcblsp0: 
      TCBList_P v'5
                    (v'7++(vv :: v'2 :: Vnull :: x8 :: Vint32 i7 :: V$ OS_STAT_RDY :: Vint32 x :: 
                              Vint32 (x&ᵢ$ 7) :: Vint32 (x >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(x&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(x >>ᵢ $ 3)) :: nil)
                        :: v'9) v'33 v'13).
  {
    eapply TCBList_P_Combine; eauto. 
  }
  
  hoare forward prim.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold dllseg at 2.
  fold dllseg.
  sep pauto.
  repeat (sep cancel dllseg).
  sep cancel node.
  unfold AOSTCBPrioTbl.
  sep pauto.
  
  (* AECBList *)
  unfold AECBList.
  instantiate (1:= A_dom_lenv ((ptr, OS_EVENT ∗) :: nil) ** LV ptr @ OS_EVENT ∗ |-> Vptr (v'29, Int.zero)). 
  sep pauto.
  eapply evsllseg_compose; eauto. 
  2: {
    sep cancel AEventNode.
    sep cancel evsllseg.
    sep cancel evsllseg.
    sep cancel 1%nat 1%nat.
    sep cancel p_local.
    sep cancel A_dom_lenv.
    sep cancel OSPlaceHolder.
    get_hsat Hsat.
    sep_lifts_trms_in Hsat tcbdllflag.
    sep_lifts_trms tcbdllflag.
    eapply tcbdllflag_hold; [idtac | sep cancel tcbdllflag]. 
    eapply tcbdllflag_hold_middle.
    simpl; auto.
    apply astar_r_aemp_elim. 
    eapply aobj_set_tcbvl_mid_preserve; eauto.
    sep cancel AOBJ.
    auto.
  }
  go.
  (** sep assertions end here ~ **)

  rewrite list_prop1.
  rewrite list_prop1.

  eapply ecblist_p_compose.
  
  eapply EcbMod.join_set_r.
  eauto.
  eexists.
  eapply EcbMod.join_get_l.
  unfold TcbJoin in Hjo'. 
  eauto.
  apply EcbMod.get_a_sig_a.
  eapply CltEnvMod.beq_refl.  

 (**** ecblist_P ****)
  Focus 2.
  
  instantiate (1:=(Vptr (v'29, Int.zero))). 
  unfold ECBList_P; fold ECBList_P.
  eexists; split.
  eauto.
  splits.
  2: { 
    do 3 eexists; splits.
    unfolds; simpl; auto.

    unfold TcbJoin.
    unfold join.
    simpl.
    unfold sig; simpl.
    erewrite <- EcbMod.set_sig.
    eapply EcbMod.join_set_l.
    unfold TcbJoin in Hjo'.
    eauto.
    unfold EcbMod.indom; eexists.
    apply EcbMod.get_a_sig_a.
    auto with brel.
    unfold RLH_ECBData_P.
    splits; auto.
    unfolds; split; intros; auto.
    clear -H55; tryfalse.
    eapply  ECBList_P_high_tcb_block_hold_sem; eauto.
    (*   eapply TcbMod.join_get_r; eauto. *)
    
    eapply ejoin_get_none_r. 
    2: eauto. 
    apply EcbMod.get_a_sig_a.
    instantiate (1:=(v'29, Int.zero)). 
    auto with brel.
    unfold TcbJoin in Hjo'.
    eauto.
  }

  eapply sempend_pure.R_ECB_ETbl_P_high_tcb_block_hold; eauto.
  
  eapply  ECBList_P_high_tcb_block_hold_sem; eauto.

  eapply ejoin_get_none_l. 
  2:eauto.
  unfold TcbJoin in Hjo'.
  eapply EcbMod.join_get_l; eauto.  
  apply EcbMod.get_a_sig_a.
  auto with brel.
  (** ECBList_P ends here ~ **)  
  
  auto. (* new add *)
  eapply TcbMod_set_R_PrioTbl_P_hold ; eauto.  
  eapply rtbl_remove_RL_RTbl_PrioTbl_P_hold; eauto. 
  eapply TCBList_P_tcb_block_hold; eauto. 

  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.

  clear Fget'.
  eapply TCBList_P_tcb_block_hold' with (prio := x); eauto.  

  eapply TcbMod_join_impl_prio_neq_cur_r; eauto.
  eapply TcbMod.join_comm; eauto.
  unfold join; simpl.
  eapply TcbMod.join_set_r; eauto.
  unfolds; eexists; eauto.

  unfold V_OSTCBPrev; simpl nth_val; auto.
  unfold V_OSTCBNext; simpl nth_val; auto.

  eapply  RH_CurTCB_high_block_hold_sem; eauto. 

  eapply RH_TCBList_ECBList_P_high_block_hold_sem; eauto.

  pure_auto.

  (******************** ex_critical finished ***********************)
    
  (* schedule *) 
  hoare forward. 
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop.
  sep cancel p_local.
  sep pauto.
  unfold isflag.
  pure_auto.
  pure_auto.
  introv Hsat. 
  sep destruct Hsat. 
  sep eexists.
  sep cancel p_local.
  sep auto.
  introv Hsat. 
  sep destruct Hsat. 
  sep eexists.
  sep cancel p_local.
  sep auto.
  
  (* ** ac: Print OS_SchedPost. *)
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare_split_pure_all.
  lzh_inverts_logic.  


  (* enter critical *)
  hoare forward prim.
  hoare normal pre.
  hoare_ex_intro.
  clear Hlast.
  hoare_assert_pure (get_last_tcb_ptr v'40 v'38 = Some (Vptr (v'32, Int.zero))).  
  {
    get_hsat Hsat.
    unfold AOSTCBList in Hsat. 
    sep normal in Hsat. sep destruct Hsat.
    sep split in Hsat. simpljoin1.
    sep_lifts_trms_in Hsat (tcbdllseg v'38).
    eapply tcbdllseg_get_last_tcb_ptr; eauto. 
  }
  hoare_split_pure_all. rename H54 into Hlast.  

  clear Htcblsp0 Fget Fget'.
  hoare unfold.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  mytac.

(* new add about the absstract stat after sched *)
  assert (Fget: exists st, TcbMod.get v'61 (v'32,Int.zero) = Some (i3, st)). 
  {
    eapply TCBListP_head_in_tcb'; try eauto.
  }
  destruct Fget as [st]. rename H83 into Fget. 
  lets Fget': TcbMod.join_get_r H62 Fget.  
  assert (Hst_cond: st = rdy \/ st <> rdy) by tauto. 
  destruct Hst_cond.
  2: { 
    hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).
    eapply abscsq_rule.
    go.
    eapply absinfer_sem_pend_p_aftersch_abt'; eauto.
    can_change_aop_solver.
    eapply absinfer_eq. 
    eapply absabort_rule.
  }
  (* st = rdy *) 
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_pend_p_aftersch'; try eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 

  assert (Hvst: i4 = ($ OS_STAT_RDY) /\ x11 = Vnull). 
  {
    lets Hget_r: get_tcb_stat_rdy H68 Fget.
    (* lets Hget_s: get_tcb_stat_sem H69 Fget. *)
    unfold V_OSTCBStat,V_OSTCBEventPtr,V_OSTCBDly in Hget_r. 
    simpl in Hget_r.
    specializes Hget_r; eauto. 
    simpljoin1.
    split; pauto.
  }

  (*OS_TCBCurStat <> OS_STAT_SEM*)
  hoare forward.
  destruct Hvst as (Hvi & Hvptr). 
  inverts Hvi; inverts Hvptr.

  assert (Fget_st: ~(exists sid, st= wait sid)).
  {
    eapply low_stat_impl_high_stat_neq_sem';
    unfold V_OSTCBStat, V_OSTCBPrio,V_OSTCBMsg; try eauto; try (simpl; auto).
  }

  assert (Het: errcode = Vint32 (Int.repr OS_NO_ERR)
                  \/ errcode <> Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Het.
  subst.
  (* errcode = OS_NO_ERR  *)
  hoare_lifts_trms_pre (Aop, abstcblsid, curtid).
  eapply abscsq_rule.  
  apply noabs_oslinv.
  eapply absinfer_sem_pend_block_get_succ; try eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 


  fold V_OSTCBPrev.
  fold V_OSTCBNext.
  hoare forward prim.
  sep cancel AOBJ. 
  unfold AOSRdyTblGrp. 
  unfold AOSRdyTbl. 
  unfold AOSTCBList.
  unfold tcbdllseg. 
  sep pauto.
  sep cancel AOSRdyGrp.
  sep cancel (dllseg v'38). 
  unfold dllseg.
  fold dllseg.
  unfold node.
  sep pauto.
  sep cancel Astruct. 
  sep cancel dllseg.
  sep cancel p_local. 
  exact_s.

  simpl; auto.
  splits; try eauto.
  go.
  split; eauto.
  eauto.
  eauto.
  eauto.
  pure_auto.
 
  hoare forward.
  introv Hf. simpl in Hf. inverts Hf.   

  (* errcode <> OS_NO_ERR  *)
  rewrite H83 in Fget'.
  hoare_lifts_trms_pre (Aop, abstcblsid, curtid).  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply absinfer_sem_pend_block_get_succ_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.  

Qed.
