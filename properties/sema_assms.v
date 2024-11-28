
Require Import memory. 
Require Import anno_language.
Require Import anno_opsem.
Require Import sema_invs.

(* 
     According to the global invariant used in the refinement verification,
     if a task is in the "wl" of semaphore eid, then the status of the task
     is (wait (os_stat_sem eid), _).
     Therefore, a task cannot be in the "wl" of different semaphores. 
 *)
Axiom no_multiple_wait: 
  forall (O: osabst), 
  forall els eid1 eid2 t n1 n2 wl1 wl2,
    get O absecblsid = Some (absecblist els) ->
    get els eid1 = Some (abssem n1, wl1) ->
    get els eid2 = Some (abssem n2, wl2) ->
    In t wl1 ->
    In t wl2 ->
    False. 

(* If a task is in the list of waiting tasks for a semaphore eid, then the
     task is in the status of waiting for the semaphore eid *)
(* This is also according to the global inv. established in
    the refinement verification. *)
Axiom sem_tst_est_:
  forall (O: osabst) tls els n wls t eid,
    get O abstcblsid = Some (abstcblist tls) -> 
    get O absecblsid = Some (absecblist els) ->
    get els eid = Some (abssem n, wls) ->
    In t wls ->
    exists p,  get tls t = Some (p, wait eid).  

