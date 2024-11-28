
Require Import memory. 
Require Import anno_language.
Require Import anno_opsem.
Require Import common_defs. 


(*
  for each active semaphore,
    the current value of the semaphore, increased by the number of
    successful V operations that change the value of the semaphore, decreased by the number of
    successful P operations that change the value of the semaphore, is equal to the current value
    of the semaphore
 *) 
Definition cond_pv1 gau els :=
  forall eid n wls,
    get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65536) = true /\     
    exists ga,
      get gau eid = Some ga /\
        Int.unsigned n = (Int.unsigned (ninit ga) + Z_of_nat (nsig1 ga) - Z_of_nat (nacq1 ga))%Z. 

Definition n_wait_rdy (eid: ecbid) tids (tls: TcbMod.map) (aust: LAuxStMod.map) :=
  List.length
    (List.filter
       (fun t =>
          match (get tls t), (get aust t) with
            Some (_, rdy), Some (mkLAuxSt (PtPend (Vptr eid'))) =>
              beq_tid eid eid' 
          | _, _ => false
          end) tids). 

(*
  The number of successful V operations that do not change the value of a semaphore is equal to: 
    the number of  successful P operations that do not change the value of a semaphore,  
    plus the number of tasks still at the program point of pending on the semaphore  
    but are already made ready
*)
Definition cond_pv0 els tls ts gau (aust: LAuxStMod.map) :=
  forall eid n wls,
    get els eid = Some (abssem n, wls) ->
    exists ga, 
      get gau eid = Some ga /\
        nsig0 ga = (nacq0 ga + n_wait_rdy eid ts tls aust)%nat. 

Definition wait_progpt (els: EcbMod.map) (aust: LAuxStMod.map) :=
  forall eid n wls,
    get els eid = Some (abssem n, wls) -> 
    forall t,
      List.In t wls ->
      exists lau,
        get aust t = Some lau /\ tskpt lau = PtPend (Vptr eid).

Definition none_progpt (els: EcbMod.map) (aust: LAuxStMod.map) ts :=
  forall eid,
    (~(exists n wl, get els eid = Some (abssem n, wl))) ->
    forall t,
      In t ts -> 
      get aust t <> Some {| tskpt := PtPend (Vptr eid) |}. 

(* 
  The global invariant on the data relevant to semaphores. 
  The invariant is shown to be preserved by the atomic execution steps
    of the P and V operations. 
*)
Definition dtinv (O: osabst) (laust: LAuxStMod.map) :=
  exists tls ts els gau,
    get O abstcblsid = Some (abstcblist tls) /\
      get O atidlsid = Some (atidls ts) /\ 
      get O absecblsid = Some (absecblist els) /\ 
      get O gauxstid = Some (gauxst gau) /\
      atids_valid tls ts /\ 
      cond_pv1 gau els /\
      cond_pv0 els tls ts gau laust /\
      wait_progpt els laust /\
      none_progpt els laust ts.


Require Import join_lib.
Require Import aux_tacs.


(* The helper lemma expressing that if the key data components are 
     not changed from O to O', then the global invariant on the abstract
     states is trivially preserved. *) 
Lemma steq_preserves_inv: 
  forall O O' lau lau' t (laump laump': LAuxStMod.map), 
    (get O abstcblsid = get O' abstcblsid /\
       get O absecblsid = get O' absecblsid /\
       get O gauxstid = get O' gauxstid /\
       get O atidlsid = get O' atidlsid /\ 
       lau = lau') -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Heq Hgl Hl' Hdti.  
  simpljoin.
  unfold dtinv in *.
  simpljoin.
  assert (Hseq: set laump t lau' = laump).
  { eapply get_set_same; eauto. }
  repeat rewrite Hseq. 
  l_rew21 (get O abstcblsid).
  l_rew21 (get O absecblsid). 
  l_rew21 (get O atidlsid).
  l_rew21 (get O gauxstid). 
  do 4 eexists.
  split; eauto.
  split; eauto. 
  split; eauto.
  split; eauto.
Qed.   
