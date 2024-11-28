
Require Import memory.
Require Import anno_language.

Require Import aux_notations.

Require Import common_defs. 

Definition nsc (O : osabst) (_: LAuxSt) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'.

Definition sc (O : osabst) (_: LAuxSt) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; Sched) ?? (ASSUME nsc).

Definition pend_asrt vl := (fun lau => lau = {| tskpt := PtPend (nth 0 vl Vnull) |}). 

Definition isched_pt vl :=
  (spec_assume (pend_asrt vl) sc;; (sched (pend_asrt vl)))
    ?? (spec_assume (pend_asrt vl) nsc).


Definition OS_LOWEST_PRIO := 63%Z.
Definition OS_IDLE_PRIO := OS_LOWEST_PRIO.

Definition OS_NO_ERR := 0%Z.
Definition OS_ERR_EVENT_TYPE := 1%Z.
Definition OS_ERR_PEND_ISR := 2%Z.
Definition OS_ERR_POST_NULL_PTR :=3%Z.
Definition OS_ERR_PEVENT_NULL := 4%Z.
Definition OS_ERR_TASK_WAITING := 8%Z.
Definition OS_TIMEOUT := 10%Z.

Definition SEM_VALUE_MAX := 65535%Z.
Definition OS_SEM_OVF := 50%Z.

Definition MAX_OBJ_NUM := 20%Z.


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
             exists els n wls gaump ni ns1 na1 ns0 na0 gaump',
               get O1 absecblsid = Some (absecblist els) /\
                 Int.ltu Int.zero n = true /\
                 get els qid = Some (abssem n, wls) /\
                 get O1 gauxstid = Some (gauxst gaump) /\ 
                 get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
                 gaump' = set gaump qid {| ninit:=ni; nsig1:=ns1; nacq1:=S na1; nsig0:=ns0; nacq0:=na0 |}  /\ 
                 opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
                 (k = Vint32 (Int.repr OS_NO_ERR)  
                  /\ O_opt = Some (set (set O1 absecblsid
                                          (absecblist (set els qid (abssem (Int.sub n Int.one), wls)))) gauxstid (gauxst gaump'))
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
        exists tls t p gaump ni ns1 na1 ns0 na0 gaump',
          get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls)/\
            get tls t = Some (p, rdy) /\ 
            get O1 gauxstid = Some (gauxst gaump) /\ 
            get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            gaump' = set gaump qid {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=S na0 |} /\ 
            rv = Some (Vint32 (Int.repr OS_NO_ERR) ) /\
            (k = Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = Some (set O1 gauxstid (gauxst gaump')) 
             \/ k <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
  end.

Definition sem_pend  (vl: vallist):=
  sem_pend_null_err (|vl|)
    ?? sem_pend_no_active_evt_err (|vl|) 
    ?? sem_pend_from_idle_err (|vl|)
    ?? sem_pend_not_ready_err (|vl|)
    ?? sem_pend_inst_get_succ (|vl|)
    ?? (spec_atm (
            sem_pend_block (|vl|);;
            spec_set_lst {| tskpt := (PtPend (nth 0 vl Vnull)) |});;  
        isched_pt vl;;
        (pend_asrt vl) # sem_pend_rdy_after_sched [|vl|];; 
        spec_atm (
            (pend_asrt vl) # sem_pend_block_get_succ [|vl|];;
            spec_set_lst {| tskpt := PtNormal |})).    

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
        exists gaump ni ns1 na1 ns0 na0 qid gaump', 
          get O1 abstcblsid = Some (abstcblist tls) /\
            get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wl)) /\
            (~ wl = nil) /\ 
            (GetHWait tls wl t') /\
            opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
            get tls t' = Some (p, st) /\
            v' = (Vint32 (Int.repr OS_NO_ERR)) /\
            tls' = set tls t' (p, rdy) /\ 
            els' = set els qid (abssem n, (remove_tid t' wl)) /\
            get O1 gauxstid = Some (gauxst gaump) /\ 
            get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            gaump' = set gaump qid {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=S ns0; nacq0:=na0 |} /\ 
            O2 = Some (set (set (set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist els')) gauxstid (gauxst gaump'))
  end.

Definition sem_post_ex_wt_abt (vl: vallist) (O1: osabst) (rst:option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      exists qid v',
      vl = (Vptr qid :: v' :: nil) /\ 
        exists els tls wl n, 
          get O1 abstcblsid = Some (abstcblist tls) /\
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
        exists els n wls gaump ni ns1 na1 ns0 na0 gaump', 
          get O1 absecblsid = Some (absecblist els) /\
            (get els qid = Some (abssem n, wls)) /\
            Int.ltu n (Int.repr 65535) = true /\
            get O1 gauxstid = Some (gauxst gaump) /\ 
            get gaump qid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            gaump' = set gaump qid {| ninit:=ni; nsig1:=S ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0 |} /\ 
            opv = (Some (Vint32 (Int.repr OS_NO_ERR ))) /\
            (v' = (Vint32 (Int.repr OS_NO_ERR)) /\ 
               O2 = Some
                      (set
                         (set O1 absecblsid (absecblist (set els qid (abssem (Int.add n Int.one), wls))))
                         gauxstid (gauxst gaump')) \/
               v' <> (Vint32 (Int.repr OS_NO_ERR )) /\ O2 = None) 
  end.

Definition sem_post (vl: vallist) := 
  match vl with
    v1 :: v2 :: nil => 
      sem_post_null_err (|vl|)
        ?? sem_post_no_active_evt_err (|vl|)  
        ?? sem_post_ovf_err (|vl|)
        ?? ((sem_post_ex_wt_succ (|vl|) ?? sem_post_ex_wt_abt (|vl|));; 
            isched ;;
            END (Some (Vint32 (Int.repr OS_NO_ERR)))) 
        ?? sem_post_inc_succ (|vl|)
  | _ => spec_abort 
  end.


(* (****************************** service_sema_P ************************************) *)  

Definition semwait_idx_err 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idxv, 
      vl = ((Vint32 idxv) :: nil) /\ 
        (Int.ltu idxv Int.zero = true \/
           Int.ltu (Int.repr MAX_OBJ_NUM) idxv = true \/ Int.eq idxv (Int.repr MAX_OBJ_NUM) = true) /\
        opv = Some (Vint32 (Int.mone)) /\ 
        O_opt = Some O1
  end.

Definition semwait_kobj_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx objs,
     vl = (Vint32 idx) :: nil /\
     Int.ltu idx Int.zero = false /\
     Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
     get O1 absobjsid = Some (absobjs objs) /\
     ~ (exists ptr attr, get objs idx = Some (objid ptr, attr)) /\
      opv = Some (Vint32 (Int.mone)) /\
       O_opt = Some O1
  end.

Definition semwait_get_kobj
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx objs attr ptr vptr,
     vl = (Vint32 idx) :: (vptr) :: nil /\
     Int.ltu idx Int.zero = false /\
     Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
     get O1 absobjsid = Some (absobjs objs) /\
     get objs idx = Some (objid ptr, attr) /\
     opv = None /\
     (vptr = Vptr ptr /\ O_opt = Some O1
      \/ vptr <> Vptr ptr /\ O_opt = None)
  end.

Definition semwait_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr,
      vl = verr :: nil /\
        opv = Some verr /\
        O_opt = Some O1
  end.

Definition semwait (vl: vallist) :=
  match vl with
    vidx :: vptr :: verr :: nil => 
      (semwait_idx_err (|vidx :: nil|) ??
         semwait_kobj_err (|vidx :: nil|) ??
         (semwait_get_kobj (|vidx :: vptr :: nil|) ;;
          (sem_pend (vptr :: verr :: nil);; semwait_ret (|verr :: nil|))))
  | _ => spec_abort
  end.

Definition semwaitapi := (semwait, (Tint32, Tint32 :: nil)). 

(* (****************************** service_sema_V ************************************) *)

Definition semsignal_idx_err 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idxv,
      vl = ((Vint32 idxv) :: nil) /\
        (Int.ltu idxv Int.zero = true \/
           Int.ltu (Int.repr MAX_OBJ_NUM) idxv = true \/ Int.eq idxv (Int.repr MAX_OBJ_NUM) = true) /\ 
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semsignal_kobj_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idx objs,
      vl = (Vint32 idx) :: nil /\
        Int.ltu idx Int.zero = false /\
        Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
        get O1 absobjsid = Some (absobjs objs) /\
        ~ (exists ptr attr, get objs idx = Some (objid ptr, attr)) /\
        opv = Some (Vint32 (Int.mone)) /\
        O_opt = Some O1
  end.

Definition semsignal_get_kobj
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists idx objs attr ptr vptr, 
      vl = (Vint32 idx) :: (vptr) :: nil /\
        Int.ltu idx Int.zero = false /\
        Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
        get O1 absobjsid = Some (absobjs objs) /\
        get objs idx = Some (objid ptr, attr) /\
        opv = None /\
        (vptr = Vptr ptr /\ O_opt = Some O1
         \/ vptr <> Vptr ptr /\ O_opt = None)
  end.

Definition semsignal_ret
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr,  
      vl = verr :: nil /\
        opv = Some verr /\
        O_opt = Some O1 
  end.

Definition semsignal (vl: vallist) := 
  match vl with
    v1 :: v2 :: v3 :: nil =>  
      (semsignal_idx_err (|v1 :: nil|) ??
         semsignal_kobj_err (|v1 :: nil|) ??
         semsignal_get_kobj (|v1 :: v2 :: nil|) ;; 
       (sem_post (v2 :: v3 :: nil);; semsignal_ret (| v3 :: nil |)))
  | _ => spec_abort
  end.

Definition semsignalapi := (semsignal, (Tint32, Tint32::nil)).


Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.


Definition service_sema_P := 301%Z.
Definition service_sema_V := 302%Z.
Definition OSTickISR : hid := 0%nat.  

Definition api_spec_list := 
  (service_sema_P, semwaitapi)  
  :: (service_sema_V, semsignalapi) 
  :: nil.

Definition api_spec := convert_api_spec api_spec_list.

Definition timetick := (isched ;; END None ?? END None). 
Definition int_spec_list : list (hid * int_code) := (OSTickISR, timetick)  ::  nil.  
Definition int_spec  := convert_int_spec int_spec_list.  

Definition os_spec := (api_spec, int_spec, GetHPrio).


