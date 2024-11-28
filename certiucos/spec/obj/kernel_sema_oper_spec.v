
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import abs_op.
Require Import os_inv. 
Require Import kernel_sema_oper.

(********************************* OSSemPend ********************************) 

Definition sem_pend_null_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
    |(opv, O_opt) =>
     exists k,
       vl = (Vnull :: k :: nil) /\
       opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL) ) /\
      (k = Vint32 (Int.repr OS_ERR_PEVENT_NULL)  /\ O_opt = Some O1
      \/ k <>  Vint32 (Int.repr OS_ERR_PEVENT_NULL)  /\ O_opt = None)
  end.

Definition sem_pend_no_active_evt_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists qid k,
    vl = ((Vptr qid) :: k :: nil) /\  
    exists els,
      get O1 absecblsid = Some (absecblist els) /\
      get els qid = None /\
      opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
      (k = Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = Some O1 \/
       k <> Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = None)
  end.  

(* Definition sem_pend_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) =>  *)
(*    exists qid k, *)
(*    vl= ((Vptr qid) :: k :: nil)/\  *)
(*    ( *)
(*      exists els, *)
(*        get O1 absecblsid = Some (absecblist els) /\ *)
(*        (exists d, get els qid = Some d /\ (~exists x wls, d = (abssem x, wls)) )/\ *)
(*        opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE) ) /\ *)
(*        (k = Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = Some O1 *)
(*         \/ k <>  Vint32 (Int.repr OS_ERR_EVENT_TYPE)  /\ O_opt = None) *)
(*    ) *)
(*   end. *)

Definition sem_pend_from_idle_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (rv, O_opt) =>
      exists qid k, 
        vl=(Vptr qid :: k :: nil) /\
        exists tls st t,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (Int.repr OS_IDLE_PRIO, st) /\ 
          rv = None /\
          O_opt = None
  end.

Definition sem_pend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (rv, O_opt) =>
      exists qid k,
      vl = (Vptr qid :: k :: nil) /\  
        exists tls st prio t,
          get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio, st) /\ 
            ~ (st = rdy) /\
            rv = None /\ 
            O_opt = None
  end.

Definition sem_pend_inst_get_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  |  (opv, O_opt) =>
       (exists qid k,
           vl = ((Vptr qid) :: k :: nil) /\ 
             exists els n wls,
               get O1 absecblsid = Some (absecblist els) /\
                 Int.ltu Int.zero n = true /\
                 get els qid = Some (abssem n, wls) /\
                 opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
                 (k = Vint32 (Int.repr OS_NO_ERR)  
                  /\ O_opt = Some (set O1 absecblsid
                                     (absecblist (set els qid (abssem (Int.sub n Int.one), wls))))
                  \/ k <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
       )
  end.

Definition sem_pend_block (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      exists qid k,
      vl = (Vptr qid :: k :: nil) /\
        exists tls tls' qls qls' wl p st t, 
          get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist qls) /\
            get O1 abstcblsid = Some (abstcblist tls) /\ 
            get qls qid = Some (abssem Int.zero, wl) /\
            qls' = set qls qid (abssem Int.zero, t::wl) /\ 
            get tls t = Some (p, st) /\ 
            tls' = set tls t (p, wait qid) /\  
            O_opt = Some (set (set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist qls')) /\
            opv = None
  end.

Definition sem_pend_rdy_after_sched (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (rv, O_opt) =>
      exists qid k,
      vl = (Vptr qid :: k :: nil) /\
        (
          exists tls p st t,
            get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get tls t =Some (p, st)/\
              rv = None /\
              ((st = rdy /\ O_opt = Some O1) \/ (~(st = rdy) /\ O_opt = None))
        )
  end.

Definition sem_pend_block_get_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (rv, O_opt) =>
      exists qid k,
      vl= (Vptr qid :: k :: nil) /\
        exists tls t p,
          get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls)/\
            get tls t = Some (p, rdy) /\ 
            (* ~(exists wt, st = wait (os_stat_sem qid) wt) /\ *)
            rv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
            (k = Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = Some O1
             \/ k <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
  end.

Definition sem_pend  (vl: vallist):=
  sem_pend_null_err (|vl|)
  ?? sem_pend_no_active_evt_err (|vl|) 
  (* ?? sem_pend_wrong_type_err (|vl|) *) 
  ?? sem_pend_from_idle_err (|vl|)
  ?? sem_pend_not_ready_err (|vl|)
  ?? sem_pend_inst_get_succ (|vl|)
  ?? (sem_pend_block (|vl|);; isched;;
      sem_pend_rdy_after_sched (|vl|);; sem_pend_block_get_succ (|vl|)).    


Local Open Scope int_scope.

Definition OSSemPendPre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s ptrv v', 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** 
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       <|| spec_code_cons (sem_pend (vl ++ (v' :: nil))) s ||> **
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
       (logic_val (V$ 1)
          :: logic_val (V$ __Loc_normal) 
          :: logic_val ptrv :: nil)). 

Theorem OSSemPendPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemPendPre' vl ll ct). 
Proof.
  simpl.
  tauto.
Qed.

Definition OSSemPendPre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemPendPreGood vl ll ct).

Definition OSSemPendPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' k ptrv,  
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** 
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       [| v = Some v' /\ v' = Vint32 k  /\ 
            Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] ** 
       <|| s ||> **
       [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] ** 
       p_local OSLInv ct
       (logic_val (V$ 1) 
          :: logic_val (V$ __Loc_normal)
          :: logic_val ptrv :: nil)).  

Theorem OSSemPendPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSSemPendPost' vl v ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition OSSemPendPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSSemPendPostGood vl v ll ct).


(********************************* OSSemPost ********************************)

Definition sem_post_null_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists v', 
      vl = (Vnull :: v' :: nil) /\
        opv = (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) /\
        (v' = (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ O2 = Some O1 \/
           v' <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ O2 = None)  
  end.

Definition sem_post_no_active_evt_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists qid v',
      vl = ((Vptr qid) :: v' :: nil) /\ 
        exists els,
          get O1 absecblsid = Some (absecblist els) /\
            get els qid = None /\
            opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
            (v' = (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O_opt = Some O1 \/ 
               v' <> (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O_opt = None) 
  end.

(* Definition sem_post_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O2) => *)
(*       exists qid v',  *)
(*       vl= ((Vptr qid) :: v' :: nil) /\  *)
(*         exists els, *)
(*           get O1 absecblsid = Some (absecblist els) /\ *)
(*             (exists d, get els qid = Some d /\ (~exists n wls, d = (abssem n, wls))) /\   *)
(*             opv = (Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE))) /\  *)
(*             (v' = (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O2 = Some O1 \/ *)
(*                v' <> (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\ O2 = None)  *)
(*   end. *)

Definition sem_post_ovf_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, O2) =>
      exists sid v',
      vl=  (Vptr sid :: v' :: nil) /\
        exists sls n wl,
          get O1 absecblsid = Some (absecblist sls) /\
            get sls sid = Some (abssem n,wl) /\
            (Int.ltu n (Int.repr 65535) = false) /\
            opv = (Some (Vint32 (Int.repr OS_SEM_OVF))) /\
            (v' = (Vint32 (Int.repr OS_SEM_OVF)) /\ O2 = Some O1 \/
               v' <> (Vint32 (Int.repr OS_SEM_OVF)) /\ O2 = None) 
  end.

Definition sem_post_ex_wt_succ (vl: vallist) (O1: osabst) (rst:option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els tls t' wl p st n tls' els', 
          get O1 abtcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wl)) /\
            (~ wl = nil) /\ 
            (GetHWait tls wl t') /\
            opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
            get tls t' = Some (p, st) /\
            v' = (Vint32 (Int.repr OS_NO_ERR)) /\
            tls' = set tls t' (p, rdy) /\ 
            els' = set els qid (abssem n, (remove_tid t' wl)) /\
            O2 = Some (set (set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist els'))
  end.

Definition sem_post_ex_wt_abt (vl: vallist) (O1: osabst) (rst:option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els tls wl n, 
          get O1 abtcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wl)) /\
            (~ wl = nil) /\ 
            opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
            v' <> (Vint32 (Int.repr OS_NO_ERR)) /\
            O2 = None
  end.

Definition sem_post_inc_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els n wls,
          get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wls)) /\
            Int.ltu n (Int.repr 65535) = true /\
            opv = (Some (Vint32 (Int.repr OS_NO_ERR ))) /\
            (v' = (Vint32 (Int.repr OS_NO_ERR)) /\ 
               O2 = Some(set O1 absecblsid (absecblist (set els qid (abssem (Int.add n Int.one), wls)))) \/
               v' <> (Vint32 (Int.repr OS_NO_ERR )) /\ O2 = None) 
  end.

Definition sem_post (vl: vallist) := 
  match vl with
    v1 :: v2 :: nil => 
      sem_post_null_err (|vl|)
        ?? sem_post_no_active_evt_err (|vl|)  
        (* ?? sem_post_wrong_type_err (|vl|) *) 
        ?? sem_post_ovf_err (|vl|)
        ?? ((sem_post_ex_wt_succ (|vl|) ?? sem_post_ex_wt_abt (|vl|));; 
            isched ;;
            END (Some (Vint32 (Int.repr OS_NO_ERR)))) 
        ?? sem_post_inc_succ (|vl|)
  | _ => spec_abort 
  end.


Definition OSSemPostPre' (vl: vallist) (logicl: list logicvar) ct :=  
  EX s ptrv v',  
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr ** 
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] ** 
       <|| spec_code_cons (sem_post (vl ++ (v' :: nil))) s ||> **   
       [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
       (logic_val (V$ 1)
          :: logic_val (V$ __Loc_normal)
          :: logic_val ptrv :: nil)).  

Theorem OSSemPostPreGood (vl:vallist) ll ct:
  GoodFunAsrt (OSSemPostPre' vl ll ct).
Proof.
  simpl. tauto.
Qed.

Definition OSSemPostPre : fpre :=
  fun vl ll ct => mkfunasrt (OSSemPostPreGood vl ll ct). 

Definition OSSemPostPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv k,  
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **  
       [| logicl = logic_val v' :: logic_code s :: logic_val ptrv :: nil |] **  
       [| v = Some v' /\ v' = Vint32 k /\
            Z.le 0%Z (Int.unsigned k) /\ Z.le (Int.unsigned k) (Byte.max_unsigned) |] **  
       <|| s ||> **
       [| nth_val' 0 vl = Vnull -> Int.ltu Int.zero k = true |] **
       p_local OSLInv ct
       (logic_val (V$ 1) 
          :: logic_val (V$ __Loc_normal)
          :: logic_val ptrv :: nil)).  

Theorem OSSemPostPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (OSSemPostPost' vl v ll ct). 
Proof.
  simpl. tauto.
Qed.

Definition OSSemPostPost : fpost :=
  fun vl v ll ct => mkfunasrt (OSSemPostPostGood vl v ll ct). 

