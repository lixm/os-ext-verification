Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Definition PRIO_ERR := OS_PRIO_INVALID.
Definition PRIO_EXIST_ERR := OS_PRIO_EXIST.
Definition NO_TCB_ERR := OS_NO_MORE_TCB .
Definition NO_ERR := OS_NO_ERR.
Definition MAX_TCB := OS_MAX_TASKS.

Definition get_tls_len (tm:TcbMod.map) :=
  length (TcbMod.lst tm).

Definition get_els_len (tm:EcbMod.map) :=
  length (EcbMod.lst tm).

Definition DEL_IDLE_ERR := OS_TASK_DEL_IDLE.
Definition DEL_NO_EXIST_ERR := OS_TASK_DEL_ERR.
Definition SELF := OS_PRIO_SELF.

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.


Definition isrdy (st: taskstatus):= 
  match st with
    | rdy => True
    | _ => False
  end.


Notation abtcblsid:=abstcblsid.

Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
  (exists tls prio st,
      get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (prio, st) /\ isrdy st /\  
        forall i prio' st',
          i <> t -> get tls i = Some (prio', st') -> isrdy st'->  
          Int.ltu prio prio'=true). 

Definition nsc (O : osabst) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'. 

Definition sc (O : osabst) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; sched) ?? (ASSUME nsc).


(* (**************************** sem_absop begin ****************************) *)
(* Definition TIME_OUT := OS_TIMEOUT. *)
Definition GetHWait (tls:TcbMod.map) (wl:list tid) (t:tid) :=
  In t wl /\
  exists p st,
    get tls t = Some (p, st) /\  
    forall t', t <> t' -> In t' wl -> exists p' st', get tls t' = Some (p', st') /\ (Int.ltu p p' = true)%Z. 


(* (*interrupts*) *)

(* Inductive tickchange : tid -> taskstatus -> EcbMod.map -> taskstatus -> EcbMod.map -> Prop:= *)
(* | rdy_change: *)
(*   forall t st els eid, *)
(*     (st=rdy) \/ (st = wait eid) -> *)
(*     tickchange t st els st els.   *)

(* Inductive tickstep': TcbMod.map -> EcbMod.map -> TcbMod.map -> EcbMod.map -> TcbMod.map -> Prop := *)
(*   endtls_step : *)
(*     forall (tls: TcbMod.map) (qls: EcbMod.map),  *)
(*       tickstep' tls qls tls qls emp *)
(* | ext_step : forall (tls tls' tls'' : TcbMod.map) *)
(*                     (els els' els'' : EcbMod.map) (t : tidspec.A) *)
(*                     (p : priority) (st st' : taskstatus) *)
(*                     tls_used tls_used', *)
(*     TcbMod.joinsig t (p, st) tls_used' tls_used -> *)
(*     tickchange t st els st' els' -> *)
(*     set tls t (p, st') = tls' -> *)
(*     tickstep' tls' els' tls'' els'' tls_used'-> *)
(*     tickstep' tls els tls'' els'' tls_used. *)

(* Definition tickstep tls els tls' els' := tickstep' tls els tls' els' tls. *)

(* Definition timetick_spec (vl: vallist) (O : osabst) (rst : option val * osabst):= *)
(*   match rst with *)
(*     | (opv, O') => *)
(*   exists tls els tm, *)
(*     exists tls' els' tm', *)
(*        get O abstcblsid = Some (abstcblist tls) /\ *)
(*        get O absecblsid = Some (absecblist els)/\ *)
(*        get O ostmid = Some (ostm tm) /\ *)
(*       O'= *)
(*       ( set ( set ( set O absecblsid (absecblist els')) abstcblsid (abstcblist tls')) *)
(*       ostmid (ostm tm')) /\ *)
(*       tm'=(Int.add tm Int.one)/\ *)
(*       tickstep tls els tls' els'/\ *)
(*       opv = None *)
(*   end. *)


(* Definition timetick := *)
(*   timetick_spec (|nil|);; (isched ;; END None ?? END None). *)


Definition timetick := (isched ;; END None ?? END None). 


(* Definition toyint_spec  (vl: vallist) (O : osabst) (rst : option val * osabst):= *)
(*   match rst with *)
(*     | (opv, O') => O = O'/\ *)
(*       opv = None *)
(*   end. *)

(* Definition toyint := toyint_spec (|nil|);; (isched ;; END None ?? END None). *)



(* task *)


(* task create *)

Definition taskcre_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr PRIO_ERR))) /\
        O2 = Some O1 /\
        (exists v1 v2 v3,
            vl= (v1::v2::(Vint32 v3)::nil)/\
              Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true)
  end.

Definition taskcre_err_prio_already_exists (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_EXIST))) /\
      O2 = Some O1 /\
      (
        exists v1 v2 v3, 
          vl = (v1::v2::(Vint32 v3)::nil) 
          (* cannot describe vholder *)
(*             exists tls, *)
(*               get O1 abstcblsid = Some (abstcblist tls) /\ *)
(*               (exists tid st msg, TcbMod.get tls tid= Some (v3, st, msg))  *)
(*           *)
      )
  end.

Definition taskcre_err_no_more_tcb (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_NO_MORE_TCB))) /\
      O2 = Some O1
  end.

(* Definition taskcre_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O2) => *)
(*       exists v1 v2 v3, *)
(*       vl = (v1::v2::(Vint32 v3)::nil) /\  *)
(*         ( *)
(*           opv = None /\ *)
(*             Int.lt (Int.repr 63) v3 = false /\ *)
(*             exists tls, *)
(*               OSAbstMod.get O1 abtcblsid = Some (abstcblist tls) /\ *)
(*                 (~ exists t' st, TcbMod.get tls t' = Some (v3, st)) /\  *)
(*                 exists tls' t', *)
(*                   TcbMod.join tls (TcbMod.sig t' (v3, rdy)) tls'/\ *)
(*                     O2 = Some (OSAbstMod.set O1 abtcblsid (abstcblist tls')) *)
(*         ) *)
(*   end. *)

Definition scrt (vl : vallist) :=
  match vl with
    | v1 :: v2 :: (Vint32 v3) :: nil => spec_crt v1 v2 (Vint32 v3)
    | _ => spec_done None
  end.

(* task :: pdata :: prio *) 
Definition taskcrecode (vl : vallist) :=
  match vl with
    v1 :: v2 :: v3 :: nil =>
      taskcre_err_prio_invalid (|vl|) ??
        taskcre_err_prio_already_exists (|vl|) ??
        taskcre_err_no_more_tcb (|vl|) ??
         (scrt vl ;; (* taskcre_succ  (|vl|) ;;  *)isched ;; END (Some (Vint32 (Int.repr NO_ERR))))
  | _ => spec_abort
  end.
    

Definition taskcreapi := (taskcrecode, (Tint8, Tptr Tvoid::Tptr Tvoid::Tint8::nil)). 

(* task delete *)

Definition taskdel_err_prio_is_idle (vl: vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_IDLE))) /\
      O2 = Some O1 /\
      (exists v3,
         vl= ((Vint32 v3)::nil)/\
         (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true
          (* Int.eq (Int.repr OS_PRIO_SELF) v3 =  true  (* /\ current is idle *) *)
         )
      )
  end.


Definition taskdel_err_prio_invalid (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      O2 = Some O1 /\
      (exists v3,
         vl= ((Vint32 v3)::nil)/\
         Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true
         (* Int.eq (Int.repr OS_PRIO_SELF) v3 = false *)
      )
  end.

(*  (* placeholder or null *) *)
Definition taskdel_err_no_such_tcb (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_ERR))) /\
      O2 = Some O1 /\
      (
        exists v3,
          vl= ((Vint32 v3)::nil) /\
          (exists tls,
             get O1 abstcblsid = Some (abstcblist tls) /\
             (~ exists tid st, TcbMod.get tls tid= Some (v3, st))
          )
      )
  end.

(* Definition taskdel_err_is_some_mutex_owner (vl: vallist) (O1 : osabst) (rst : option val * osabst):= *)
(*   match rst with *)
(*     | (opv, O2) => *)
(*       opv = (Some (Vint32 (Int.repr OS_TASK_DEL_SOME_MUTEX_OWNER))) /\ *)
(*       O2=O1 /\ *)
(*       ( *)
(*         exists v3, *)
(*           vl= ((Vint32 v3)::nil) /\ *)
(*           (exists tls els eid tid t m opr wls pr, *)
(*              get O1 abstcblsid = Some (abstcblist tls) /\ *)
(*              get O1 absecblsid = Some (absecblist els) /\ *)
(*              get tls tid = Some (v3, t, m) /\ *)
(*              get els eid = Some (absmutexsem pr (Some (tid, opr)), wls)  *)
(*           ) *)
(*       ) *)
(*   end. *)

Definition taskdel_err_has_no_next (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_DEL_HAS_NO_NEXT))) /\
        O2 = Some O1
  end.

(* Definition isWait4Ecb x t := *)
(*   x = os_stat_sem t \/ x = os_stat_q t \/ x = os_stat_mbox t \/ x = os_stat_mutexsem t. *)

Definition taskdel_clear_waitls_bit (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
      exists v3,
      vl = (Vint32 v3) :: nil/\ 
          (
            opv = None /\
            exists tls els tid eid ehb wl els',
              get O1 abtcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
              get tls tid = Some (v3, wait eid) /\
              (* isWait4Ecb st eid /\ *)
              get els eid = Some (ehb, wl) /\
              els' = set els eid (ehb, (remove_tid tid wl)) /\
              O2 = Some (set O1 absecblsid (absecblist els'))
          )
  end.

Definition sdel (vl : vallist) :=
  match vl with
  | (Vint32 v3) :: nil => spec_del (Vint32 v3)
  | _ => spec_done None
  end.

Definition taskdelcode (vl : vallist) :=
  match vl with
    v :: nil => 
      taskdel_err_prio_invalid (|vl|)
        ?? taskdel_err_no_such_tcb (|vl|)
        ?? taskdel_err_prio_is_idle (|vl|)
        (* ?? taskdel_err_is_some_mutex_owner  (|vl|) *)
        ??  taskdel_err_has_no_next (|vl|)
        ?? (sdel vl ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR))))
        ?? ( taskdel_clear_waitls_bit (|vl|) ;; sdel vl ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR))))
  | _ => spec_abort
  end.

Definition taskdelapi := (taskdelcode, (Tint8, Tint8::nil)).  

Fixpoint spec_code_cons (s1:spec_code) (s2:spec_code) :=
  match s1 with
  | sp1 ?? sp2 => (spec_code_cons sp1 s2) ?? (spec_code_cons sp2 s2)
  | sp1 ;; sp2 => sp1 ;; (spec_code_cons sp2 s2)
  | _ => s1 ;; s2
  end.
