
(* new inOSSemPostProof.v *)
Require Import kernel_sema_oper.
Require Import kernel_sema_oper_spec.

Require Import ucos_include.
Require Import absop_rules.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
(* Require Import oscore_common. *)

Require Import sem_common.
Require Import obj_common.
Require Import obj_common_ext.

Require Import sempend_pure.
Require Import sempost_pure. 
Require Import tcblist_setnode_lemmas.
(* Import OSQPostPure. *)

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

(* basically the same tac or lemma in OSSemPostProof.v *)

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
  lzh_hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                       ?v <> Vnull /\
                                       ?v <> Vundef|]}} ?stmts {{_}} =>
      (* ** ac: idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* ** ac: idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Hint Resolve noabs_oslinv.
Hint Extern 2 (_ <= _) => apply Z.leb_le; trivial.

Require Import abs_infer_abt.
Require Import seplog_pattern_tacs.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
    can_change_aop p ->
    sc ⊢ <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
    sc ⊢ <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; try eauto.
Qed.

Lemma absimp_sem_post_null_return:
  forall sid v' P sch s,
    sid = Vnull ->
    v' = (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) ->  
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (sid :: v' :: nil)) s ||> ** P) 
      (<|| s ||> ** P ). 
Proof.
  introv Hsid Hv' Hcop.
  eapply absinfer_trans. 
  simpl.
  eapply absinfer_choice1.
  3: eauto. 
  pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)))).
  infer_solver 0%nat. 
  eexists.
  splits; eauto.
  subst sid. auto. 
  eapply absinfer_seq_end; try pure_auto.
Qed.

Lemma absimp_sem_post_null_return_abt:
  forall sid v' P sch s,
    sid = Vnull ->
    v' <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) -> 
    can_change_aop P -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (sid :: v' :: nil)) s ||> ** P) 
      (<|| ABORT ||> ** P ). 
Proof.
  introv Hsid Hv' Hcop.
  simpl.
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.

Lemma absinfer_sem_post_no_active_evt_err: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k = V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| s ||> ** HECBList els ** P). 
Proof.
  introv Hcop Hnone Hk.
  subst.
  simpl spec_code_cons.
  infer_solver 1%nat.
Qed.

Lemma absinfer_sem_post_no_active_evt_err_abt: 
  forall a P els sch k s,
    can_change_aop P ->
    EcbMod.get els a = None ->
    k <> V$ OS_ERR_EVENT_TYPE -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr a :: k :: nil)) s ||> ** HECBList els ** P)
      (<|| ABORT ||> ** HECBList els ** P). 
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
  instantiate (1:=HECBList els ** P).
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

(* Lemma absimp_sem_post_pevent_not_in_dom_abt:  *)
(*   forall sid els qid v' P sch s, *)
(*     sid = Vptr qid -> *)
(*     get els qid = None ->  *)
(*     can_change_aop P ->  *)
(*     absinfer sch *)
(*       (<|| spec_code_cons (sem_post (sid :: v' :: nil)) s ||> ** HECBList els ** P)  *)
(*       (<|| ABORT ||> ** HECBList els ** P ).   *)
(* Proof. *)
(*   introv Hsid Hnone Hcop. *)
(*   simpl. *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_choice2. *)
(*   3: eauto. pure_auto. pure_auto. *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_choice1. *)
(*   3: eauto. pure_auto. pure_auto.  *)
(*   eapply absinfer_trans. *)
(*   eapply absinfer_seq1. *)
(*   pure_auto. *)
(*   eapply absinfer_abt; try pure_auto. *)
(*   absimp_abt_solver. *)
(*   pure_auto. *)
(*   eapply absinfer_seq_abt; try pure_auto.  *)
(* Qed. *)

Lemma absimp_sem_post_put_sem_return: 
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' = (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| s ||> ** HECBList (EcbMod.set els sid (abssem (Int.add n Int.one), wls)) ** P).          
Proof.
  introv Hcop Habsem Hrgn Hv'.
  simpl.
  do 4 (
       eapply absinfer_trans;
       [eapply absinfer_choice2; [  | instantiate (1:=HECBList els ** P) | ]; pure_auto | ]).  
  infer_solver 0%nat.   
Qed.

Lemma absimp_sem_post_put_sem_abt:  
  forall P els sid n wls sch v' s, 
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = true ->
    v' <> (Vint32 (Int.repr OS_NO_ERR)) -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** HECBList els ** P) 
      ( <|| ABORT ||> ** HECBList els ** P).   
Proof. 
  introv Hcop Habsem Hrgn Hv'.
  simpl.
  repeat
    (try eapply absinfer_trans;
     [eapply absinfer_choice2; [ | instantiate (1:=HECBList els ** P) | ]; pure_auto | ]).
  eapply absinfer_trans.
  eapply absinfer_seq1; try pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma absimp_sem_post_ovf_err_return:
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    v'1 = Vint32 (Int.repr OS_SEM_OVF) ->  
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| s ||> ** HECBList els ** P).     
Proof.
  introv Hcop Hget Hltu Hv'1.
  simpl.
  infer_solver 2%nat.   
Qed. 

Lemma absimp_sem_post_ovf_err_abt: 
  forall P els eid n wls sch v'1 s,  
    can_change_aop P ->
    EcbMod.get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65535) = false ->
    v'1 <> Vint32 (Int.repr OS_SEM_OVF) -> 
    absinfer sch
      (<|| spec_code_cons (sem_post (Vptr eid :: v'1 :: nil)) s ||> ** HECBList els ** P) 
      (<|| ABORT ||> ** HECBList els ** P).   
Proof.
  introv Hcop Hget Hltu Hneq.
  simpl.
  do 2 (
       eapply absinfer_trans;
       [ eapply absinfer_choice2; [ | | eauto ]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto.
Qed.   

(* Require Import ucos_frmaop. *)
(* Require Import abs_step. *)

Lemma absimp_sem_post_ex_wt_succ_return:
  forall P els sid tls t' n wls p st sch v' s t ct,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    GetHWait tls wls t' ->
    TcbMod.get tls t' = Some (p, st) -> 
    v' = V$ OS_NO_ERR -> 
    absinfer sch
      ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> ** 
          HECBList els ** HTCBList tls **
          HTime t ** HCurTCB ct ** P ) 
      ( <|| isched;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ;; s ||> **
          HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
          HTCBList (TcbMod.set tls t' (p, rdy)) ** 
          HTime t ** HCurTCB ct ** P ). 
Proof.
  introv Hcop Hget Heq Hhw Htlsget Hv'.
  simpl.
  do 3 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1. 3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto. 
  instantiate (1:=HECBList (EcbMod.set els sid (abssem n, (remove_tid t' wls))) **
                           HTCBList (TcbMod.set tls t' (p, rdy)) ** HTime t ** HCurTCB ct ** P ).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto. 
  instantiate (1:=HECBList els ** HTCBList tls ** HTime t ** HCurTCB ct ** P).
  pure_auto. pure_auto.
  instantiate (1:=END (Some (Vint32 (Int.repr OS_NO_ERR)))).
  infer_solver 0%nat. 

  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_eq. 
  eapply absinfer_seq_end; try pure_auto. 
Qed.

Lemma absimp_sem_post_ex_wt_succ_abt:
  forall P els sid tls n wls sch v' s,
    can_change_aop P ->
    EcbMod.get els sid = Some (abssem n, wls) ->
    ~ wls = nil ->
    v' <> V$ OS_NO_ERR -> 
    absinfer sch
             ( <|| spec_code_cons (sem_post ((Vptr sid) :: v' :: nil)) s ||> **
                   HECBList els ** HTCBList tls ** P )  
             ( <|| ABORT ||> ** HECBList els ** HTCBList tls ** P ). 
Proof.
  introv Hcop Hget Hneq Hv'.
  simpl.
  do 3 (
       eapply absinfer_trans; 
       [ eapply absinfer_choice2; [ | | eauto]; pure_auto | ]
     ).
  eapply absinfer_trans. 
  eapply absinfer_choice1.
  3: eauto. pure_auto. pure_auto.
  eapply absinfer_trans. 
  eapply absinfer_seq1. pure_auto.
  eapply absinfer_choice2; try pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1. pure_auto. 
  eapply absinfer_abt; pure_auto.
  absimp_abt_solver.
  instantiate (1:=HECBList els ** P).
  instantiate (2:=sem_post_ex_wt_succ (|Vptr sid :: v' :: nil|)). 
  instantiate (2:=s0).
  sep pauto.
  can_change_aop_solver.
  eapply absinfer_seq_abt; try pure_auto. 
Qed. 

Require Import sem_lab.

Require Import objauxvar_lemmas.
Require Import objaux_pure.
Require Import freeevtlist_lemmas.

Ltac get_hsat Hs := 
  match goal with
    H: _ |= _ |- _ => rename H into Hs
  end.

Lemma beq_addrval_true : forall a, beq_addrval a a = true.
Proof.
  intro.
  destruct a; simpl.
  rewrite Int.eq_true.
  rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_refl.
  simpl; auto.
Qed.

Lemma beq_val_true : forall v, beq_val v v = true.
Proof.
  intro.
  destruct v; simpl; auto.
  rewrite Int.eq_true; auto.
  rewrite beq_addrval_true; auto.
Qed.

Lemma tcbdllseg_ptr_in_tcblist_head :
  forall vl head headprev tail tailnext s P,
    s |= tcbdllseg head headprev tail tailnext vl ** P ->
    vl <> nil ->
    ptr_in_tcblist head head vl.
Proof.
  destruct vl; intros; tryfalse.
  destruct_s s; unfold tcbdllseg in H; unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  simpl.

  rewrite beq_val_true.
  auto.
Qed.

Lemma tcbdllseg_combine_ptr_in_tcblist :
  forall vl1 vl2 head1 headprev1 tail1 tailnext1 tail2 tailnext2 s P,
    s |= tcbdllseg head1 headprev1 tail1 tailnext1 vl1 ** tcbdllseg tailnext1 tail1 tail2 tailnext2 vl2 ** P ->
    vl2 <> nil ->
    ptr_in_tcblist tailnext1 head1 (vl1 ++ vl2).
Proof.
  inductions vl1; intros.
  unfold tcbdllseg in H at 1.
  simpl dllseg in H.
  sep split in H; substs.
  rewrite app_nil_l.
  apply tcbdllseg_ptr_in_tcblist_head in H; auto.
  unfold tcbdllseg in H at 1.
  unfold dllseg in H; fold dllseg in H.
  sep normal in H; destruct H; sep split in H.
  sep remember (1::nil)%nat in H.
  destruct_s s.
  unfold sat in H; fold sat in H.
  simpl_state; simpljoin1.
  unfold tcbdllseg in IHvl1 at 1.
  lets Hx: IHvl1 H9 H0.
  rewrite <- app_comm_cons.
  simpl.
  destruct (beq_val tailnext1 head1); auto.
  rewrite H1; auto.
Qed.

Ltac mttac C tac :=
  match goal with H: context[C] |- _ => (tac H) end. 

Lemma nth_val'2nth_val:
  forall n rtbl x,
    nth_val' n rtbl = Vint32 x ->
    nth_val n rtbl = Some (Vint32 x).
Proof.
  intros.
  inductions n;
  simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.

Lemma r_priotbl_p_set_hold:
  forall v'7 prio st v'36 tid x vhold,
    R_PrioTbl_P v'36 v'7 vhold->
    TcbMod.get v'7 tid = Some (prio, st) ->
    R_PrioTbl_P v'36
                (TcbMod.set v'7 tid
                            (prio, x)) vhold.
Proof.
  intros.
  unfolds in H.
  unfolds.
  splits.
  intros.
  destruct H.
  lets Hs : H H1 H2.
  simpljoin1.
  assert (tcbid = tid \/ tcbid <> tid) by tauto.
  destruct H7.
  subst.
  unfold get; simpl.
  rewrite TcbMod.set_sem.
  rewrite tidspec.eq_beq_true; auto.
  apply Hs in H3; auto.
  unfold get in H3; simpl in H3.
  rewrite H0 in H3.
  simpljoin1.
  inverts H3.
  do 2 eexists; eauto.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; auto.
  intros.
  assert (tcbid = tid \/ tcbid <> tid) by tauto.
  destruct H2.
  subst.
  rewrite  TcbMod.set_sem in H1.
  rewrite tidspec.eq_beq_true in H1.
  inverts H1.
  eapply H; eauto.
  auto.
   rewrite  TcbMod.set_sem in H1.
  rewrite tidspec.neq_beq_false in H1; auto.
  eapply H; eauto.
  destruct H.
  destruct H1.
  eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.   

Lemma kernel_sema_post_proof:  
  forall vl p r logicl ct, 
    Some p =
      BuildPreI os_internal OSSemPost vl logicl OSSemPostPre ct->
    Some r =
      BuildRetI os_internal OSSemPost vl logicl OSSemPostPost ct-> 
    exists t d1 d2 s,
      os_internal OSSemPost = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.

  hoare forward prim.
  hoare unfold.
  
  lzh_hoare_if2. 
  hoare forward prim.
  pure_auto.

  assert (Hor: v'2 <> (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) \/ 
                 v'2 = (Vint32 (Int.repr OS_ERR_PEVENT_NULL))) by tauto. 
  inversion Hor.
  (* v'2 <> ... *) 
  eapply abscsq_rule.
  pure_auto.
  (* change ((x :: nil) ++ v'1 :: nil) with (x::v'1::nil). *)
  eapply absimp_sem_post_null_return_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq. 
  eapply absabort_rule.
  (* v'2 = ... *)  
  eapply abscsq_rule.
  pure_auto.
  eapply absimp_sem_post_null_return; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  (* return in case pevent = NULL *)
  hoare forward. 
  
  rename v'14 into els.
  
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
  hoare_assert_pure (Vptr v'31 = v'8).   
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (llsegobjaux, AOSTCBList). 
    eapply tcblist_llsegaux_match_tn_frm in Hsat; eauto. 
  }
  hoare_split_pure_all.
  subst v'8. 

  hoare_assert_pure (ct = v'31).  
  {
    match goal with H: _ |= _ |- _ => rename H into Hsat end.
    unfold AOSTCBList in Hsat. 
    sep normal in Hsat. sep destruct Hsat. sep split in Hsat.
    simpljoin1.
    congruence.        
  }
  hoare_split_pure_all.
  rename H into Hcteq. (* ct = ... *)

  unfold p_local at 2. 
  unfold OSLInv at 3.
  unfold LINV.
  hoare_split_pure_all.
  destruct H. 
  inverts H. (* logiv_val ... :: ... = logic_val ... :: ... *)  

  hoare_assert_pure (Vptr x = v'23). { gen_eq_ptr. }
  hoare_split_pure_all. subst v'23. 
  rename v'14 into ptrmp.  
  assert (Hevptr: get ptrmp ct = Some (Vptr x)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    subst ct. join auto.
  }
  hoare_assert_pure (v'17 = V$ os_code_defs.__Loc_normal).
  { gen_eq_loc. }
  hoare_split_pure_all. subst v'17.
  subst v'31. (* current task id is ct *)   
  rename v'1 into locmp.
  assert (Hevloc: get locmp ct = Some (V$ os_code_defs.__Loc_normal)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }  

  rename v'20 into fecbh.
  rename v'3 into fecbvl. 
  rename v'22 into objs. 

  assert (Hevt: is_kobj els x \/ ptr_in_ecblist (Vptr x) fecbh fecbvl).  
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

  hoare_assert_pure (get els (v'23, Int.zero) = None).
  {
    get_hsat Hsat. 
    lets H00: semcre_ecblist_star_not_inh H Hsat. 
    auto.
  }
  hoare_split_pure_all.
  rename H14 into Hnone. 
  rename v'2 into errcode.  
  casetac errcode (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid).  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_post_no_active_evt_err_abt; try pure_auto.
    go. unfold CurTid. go.
    eapply absinfer_eq. 
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_post_no_active_evt_err; eauto. 
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
  instantiate (2:=v'3++((V$ OS_EVENT_TYPE_UNUSED :: Vint32 i :: Vint32 i1 :: x3 :: x4 :: v'22 :: nil) :: v'14)).  
  instantiate (2:=Vptr v'1). 
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
  rename H into H_elp. (* ECBList_P ... *)  
  assert (Hecb: exists ecb, get els x = Some ecb). 
  {
    unfold is_kobj in Hevt.
    rename Hevt into Hsem.
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

  hoare_assert_pure (length v'8 = length v'17).  
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg. 
    eapply evsllseg_aux in Hsat. 
    destruct Hsat.
    eauto. 
  }
  eapply pure_split_rule'; introv Heqlen. 
  lets H00: ecblist_p_decompose H_elp; eauto.  
  destruct H00 as (els1 & els2 & x' & H''). 
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).      
  hoare_assert_pure (x' = Vptr (v'31, Int.zero)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 
  
  assert (Hecbl' := Hecbl2).
  (* do 2 (rewrite ele_lst_cons in Hecbl').  *)
  unfold ECBList_P in Hecbl'.
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hex).
  inverts Hqid. 
  destruct Hex as (absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.
  
  lzh_hoare_if.
  pure_auto.
  pure_auto.  

  (* the concrete type is not OS_EVENT_TYPE_SEM *) 
  hoare_assert_pure (~exists n wls, get els (v'31, Int.zero) = Some (abssem n, wls)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_eventtype_neq_sem in Hsat; eauto.
    sep split in Hsat.
    auto.
    go.
  }
  hoare_split_pure_all.

  rename v'2 into errcode.
  casetac errcode (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) Heeq Hene.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid).  
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absinfer_sem_post_no_active_evt_err_abt; eauto.
    can_change_aop_solver.
    unfold CurTid. go.
    false.
    apply H.
    destruct e.
    do 2 eexists; eauto.
    eapply absinfer_eq.
    eapply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, absecblsid).  
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_sem_post_no_active_evt_err; eauto. 
  go. unfold CurTid. go.
  unfold get, EcbMap in Hgetecb.
  false.
  apply H. unfold get. unfold EcbMap.
  destruct e.
  do 2 eexists.
  eauto.
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
  sep pauto.
  sep cancel AObjs.
  unfold tcbllsegobjaux.
  eapply llsegobjaux_merge2_frm; eauto.
  sep cancel llsegobjaux.
  eapply llsegobjaux_merge_hd; eauto.
  eauto.
  eauto.
  eauto.
  go.
  
  (* return OS_ERR_EVENT_TYPE *) 
  hoare forward.
  
  (* the concrete type is OS_EVENT_TYPE_SEM *)
  apply semacc_int_eq_true in Hif_false. 
  subst.
  hoare_assert_pure (exists wls, v'22 = DSem i1 /\ absmq = (abssem i1, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: go. 
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H as (Hdsem & Habssem). 
  match type of Habssem with
    _ = (?e, ?w) =>
    assert (Hsem: get els (v'31, Int.zero) = Some (e, w)) 
  end.
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    rewrite get_a_sig_a; eauto. subst. auto.
  }

  subst.
  
  hoare_unfold.
  lzh_hoare_if2.

  2: {
    
    lzh_hoare_if2. 
    
    lzh_simpl_int_eq.
    unfold AOSTCBPrioTbl.
    hoare_split_pure_all.
    assert (Hnil : v'3 = nil).
    {
      lets Fnil: sempost_grp_wls_nil' H Hecbetbl; eauto.  
    }
    subst v'3.
    hoare forward. 
    struct_type_match_solver.
    unfold p_local.
    sep normal. sep cancel CurTid.
    unfold LINV, OSLInv. sep pauto. 
    
    assert (Hret: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/ v'2 = Vint32 (Int.repr OS_NO_ERR)) 
      by tauto.
    inversion Hret as [Hretcase | Hretcase]. 
    (* v'2 <> ... *)
    hoare_lifts_trms_pre (Aop, absecblsid). 
    eapply abscsq_rule.
    pure_auto. 
    eapply absimp_sem_post_put_sem_abt; eauto. 
    go. unfold CurTid. go. 
    eapply absinfer_eq. 
    eapply absabort_rule.
    
    (* v'2 = ... *)  
    hoare_lifts_trms_pre (Aop, absecblsid). 
    eapply abscsq_rule.
    pure_auto. 
    eapply absimp_sem_post_put_sem_return; eauto. 
    go. unfold CurTid. go. 
    eapply absinfer_eq. 

    
    transform_pre sempost_inc_cnt_prop ltac:(sep cancel AEventData). 
    hoare_split_pure_all. 
    clear Hrlh Hecbetbl. 

    hoare forward prim.
    unfold AECBList.
    sep pauto.
    eapply lzh_evsllseg_compose.
    sep cancel evsllseg.
    sep cancel evsllseg.
    unfold AEventNode.
    sep cancel AEventData.
    unfold AOSEvent.
    unfold node.
    unfold AOSEventTbl.
    instantiate(9:= etbl).
    sep pauto; eauto.
    sep cancel Astruct.
    sep cancel Aarray.
    unfold AOSTCBPrioTbl.
    sep pauto.
    sep cancel 2%nat 1%nat. (* PV vhold_addr ... *)
    unfold p_local.
    sep normal. sep cancel CurTid.
    unfold LINV, OSLInv. sep pauto.

    unfold AOBJ.
    sep pauto.
    unfold tcbllsegobjaux.
    sep_lifts_trms llsegobjaux.
    eapply llsegobjaux_merge2_frm; eauto.
    sep cancel llsegobjaux.
    eapply llsegobjaux_merge_hd; eauto.
    sep cancel objaux_node.
    sep cancel llsegobjaux.
    unfold AObjs in *.
    sep pauto.
    sep cancel AObjArr.
    2: { eapply RH_OBJ_ECB_P_sem_inc; eauto. }
    eauto.
    auto. (* ObjArray_P ... *)

    auto.
    auto.

    eapply obj_aux_p_sem_inc_preserve; eauto.
    
    auto.
    auto. eauto.

    split; [auto | eapply sempost_struct_type_vallist_match_sem; auto (* struct_type_vallist_match *)].
    unfolds; simpl. auto.
    eauto.
    eauto.

    assert (Heget: EcbMod.get els (v'31, Int.zero) = Some (abssem i1, nil)) by auto.
    assert (Hjsig: EcbMod.joinsig (v'31, Int.zero) (abssem i1, nil) mqls' els2) by auto. 
    lets Hnewjoin: ecb_get_set_join_join Heget Hjsig Hjo. 
    destruct Hnewjoin as [? [? ?]]. 
    eapply semacc_compose_EcbList_P; eauto.
    eapply sempost_inc_RH_TCBList_ECBList_P_hold; eauto.
    pauto.
    
    (* RETURN ′ OS_NO_ERR *) 
    hoare forward.
    introv Hf. simpl in Hf. inverts Hf. 

    
    (********************** cnt = 65535, overflow! ************************)
    lzh_simpl_int_eq. 
    unfold AOSTCBPrioTbl.
    hoare_split_pure_all.
    assert (Hnil : v'3 = nil).
    {
      lets Fnil: sempost_grp_wls_nil' H Hecbetbl; eauto.
    }
    subst v'3.

    assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_SEM_OVF) \/
                      v'2 = Vint32 (Int.repr OS_SEM_OVF)) by tauto. 
    inversion Hv'1cs.
    (* v'2 <> ... *) 
    hoare_lifts_trms_pre (Aop, absecblsid). 
    eapply abscsq_rule.
    pure_auto.
    eapply absimp_sem_post_ovf_err_abt; eauto.
    go. unfold CurTid. go. 
    eapply absinfer_eq. 
    eapply absabort_rule.
    (* v'2 = ... *)
    hoare_lifts_trms_pre (Aop, absecblsid). 
    eapply abscsq_rule.
    pure_auto.
    eapply absimp_sem_post_ovf_err_return; eauto.
    go. unfold CurTid. go. 
    eapply absinfer_eq. 

    fold_AEventNode_r.
    compose_evsllseg.
    fold_AECBList.

    hoare forward prim. 
    unfold AOSTCBPrioTbl.
    sep pauto.
    unfold AOBJ.
    sep pauto.
    unfold tcbllsegobjaux.
    sep_lifts_trms llsegobjaux.
    eapply llsegobjaux_merge2_frm; eauto.
    sep cancel llsegobjaux.
    eapply llsegobjaux_merge_hd; eauto.
    sep cancel objaux_node.
    sep cancel llsegobjaux.
    sep cancel AObjs.
    unfold p_local.
    sep normal. sep cancel CurTid.
    unfold LINV, OSLInv.
    sep pauto; eauto.
    auto.
    auto.
    auto.
    auto.
    auto.
    auto. (* RL_RTbl_PrioTbl *)
    go.

    hoare forward. 
  }

  (******************************* OSEventGrp != 0 ******************************)

  inverts Hsem. 
  hoare forward.
  unfold p_local.
  sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto. 

  hoare_unfold. 
  unfold AOSTCBPrioTbl.
  unfold AOSTCBList.
  hoare_split_pure_all.
  destruct H17. 
  
(****************************** L2: event_task_rdy ******************************)
  destruct H36. 
  hoare forward.

  unfold_msg.
  sep cancel AEventData.
  sep pauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop.
  sep cancel AOSRdyTblGrp.
  instantiate (3:= (v'9 ++ v'10 :: v'11)). 
  eapply tcbdllseg_compose.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  unfold p_local.
  sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto. 

  eauto.
  unfold V_OSEventGrp; simpl. auto.
  pauto.
  pauto. 
  splits; eauto. 
  struct_type_match_solver.

  split.
  unfold V_OSEventGrp; simpl; eauto.
  lzh_simpl_int_eq. auto.
  simpl; eauto.
  simpl; eauto.
  pure_auto.

  (* ** ac: SearchAbout TCBList_P. *)
  (* ** ac: Locate tcbdllseg_get_last_tcb_ptr. *)
  (* ** ac: Check tcbdllseg_get_last_tcb_ptr. *)
  eapply TCBList_P_Combine.
  eapply tcbdllseg_get_last_tcb_ptr.
  instantiate (5:=s).
  sep cancel (tcbdllseg).
  sep pauto.
  2:eauto.
  2:eauto.
  eauto.
  
  eauto.
  eauto.
  eauto.

  eapply tcbdllseg_combine_ptr_in_tcblist.
  instantiate (7:=s).
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  pure_auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  (** implication of precondition of OSEventTaskRdy proven **)
  Set Printing Depth 500.
  hoare unfold.

  remember (spec_code_cons
              (sem_post ((Vptr (v'31, Int.zero) :: nil) ++ v'2 :: nil)) v'0) as abs_code. 
  inverts H71.
  subst v'52. 

  (** renameing **)
  rename v'31 into pevent_addr.
  rename ct into ctcb.
  rename v'78 into htcb_addr. (** highest tcb in pevent waitlist **)
  rename H44 into Hhtcb. 
  rename H65 into Hctcb_in_tcblist. 
  rename v'53 into tcblist_head. 
  rename v'9 into tcblist_seg1.
  rename v'10 into ctcb_node.
  rename v'11 into tcblist_seg2.
  rename H48 into Hrel_et. 

  (* ** ac: Print prio_in_tbl. *)
  rename v'40 into rtbl. 
  (* ** ac: Print TCBList_P. *)

  rename v'36 into tcbls. 
  rename v'30 into tcbls1. 
  rename v'33 into tcbls2.
  (** tcbls = tcbls1 ++ tcbls2, tcbls2 = cur_node ++ tcbls2' **)
  
  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.
  
  rename v'73 into hprio. 
  assert (exists hprio', hprio = Vint32 hprio'). 
  {
    clear - H75. (** struct_type_vallist_match **)
    rename H75 into H. 
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
    
  destruct H39. 
  subst hprio.
  rename x into hprio.
  
  rename v'67 into hnext. 
  rename v'74 into htcbx.
  rename v'75 into htcby.
  rename v'76 into hbitx.
  rename v'77 into hbity.

  assert (Hhtcb_get: exists st, get tcbls (htcb_addr, Int.zero) = Some (hprio, st)). 
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }

  destruct Hhtcb_get as (st & Hhtcb_get).

  assert (Hs1: Int.unsigned v'61 <= 7). 
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H49 H25. 
    apply osunmapvallist_prop in H25.
    mytac.
    rewrite H in H49.
    inverts H49. 
    pure_auto.
  }
  
  assert (Hs2: Int.unsigned v'62 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H50 Hs1 H61 H22. 
    assert (Z.to_nat (Int.unsigned v'61) < length v'46)%nat. 
    {
      rewrite H22; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H61 H.
    mytac.
    rewrite H50 in H0.
    inverts H0.
    auto.
  }

  assert (Hs3: Int.unsigned v'60 <= 7). 
  {
    clear - H51 Hs2. 
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H51; inverts H51. 
    pure_auto.
  }

  (* ** ac: Check post_exwt_succ_pre_sem. *)
  rename v'3 into pwls.
  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  assert (Hpre: pwls <> nil /\ GetHWait tcbls pwls (htcb_addr, Int.zero) /\
                TcbMod.get tcbls (htcb_addr, Int.zero) = Some (hprio, st) /\
                hprio = ((v'61<<ᵢ$ 3) +ᵢ  v'60)). 
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    apply semacc_int_eq_false in H. 
    eapply post_exwt_succ_pre_sem; eauto.
  }

  destruct Hpre as [? [? [? ?]]]. 
  subst hprio.

  assert (Hv'1cs: v'2 <> Vint32 (Int.repr OS_NO_ERR) \/ v'2 = Vint32 (Int.repr OS_NO_ERR)) by tauto. 
  inversion Hv'1cs.
  (* v'2 <> ... *)
  hoare_abscsq.
  auto.
  eapply absimp_sem_post_ex_wt_succ_abt; eauto.
  can_change_aop_solver.
  eapply absabort_rule.
  (* v'2 = ... *) 
  hoare_abscsq.
  auto.
  eapply absimp_sem_post_ex_wt_succ_return; eauto.
  can_change_aop_solver.
  
  unfold AEventData.
  unfold_msg.
  hoare_split_pure_all.
  destruct H46. 
  inverts H46. 
  rename v'7 into pevent_addr.

  mttac V_OSEventGrp ltac: (fun H=> unfolds in H; simpl in H; inverts H). 
  rename v'46 into etbl.

  rename H70 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get.
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.  

  mttac V_OSTCBPrio ltac:(fun H=> inverts H).
  
  mttac RL_TCBblk_P ltac:(fun H=> rename H into Hh_tcbblk).
  mttac R_TCB_Status_P ltac:(fun H=> rename H into Hh_tcbstat).
  
  unfolds in Hh_tcbblk.
  mytac.
  (* inverts H49.  *)
  mttac V_OSTCBStat ltac: (fun H=> inverts H).
  mttac V_OSTCBEventPtr ltac: (fun H=> inverts H).
  mttac R_ECB_ETbl_P ltac: (fun H=> inverts H).
  mttac V_OSTCBY ltac: (fun H=> inverts H).
  mttac V_OSTCBX ltac: (fun H=> inverts H).
  mttac V_OSTCBBitX ltac: (fun H=> inverts H).
  mttac V_OSTCBPrio ltac: (fun H=> inverts H).
 
  rename v'61 into p1.
  rename v'60 into p2. 
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.
  
  (* ** ac: Check sem_post_get_tcb_stat. *)

  assert (Hx: x6 = $ OS_STAT_SEM).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
  subst x6.

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }

  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  }

  assert (Hs4: Int.unsigned v'79 <= 255). 
  {
    clear - Hs1 H41 H73 H58. 
    assert (Z.to_nat (Int.unsigned p1) < length rtbl)%nat.
    {
      rewrite H73. 
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H58 H. 
    mytac.
    rewrite H41 in H0. 
    inverts H0.
    auto.    
  }
  
  assert (Htmp: v'63 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst v'63. 
  
  assert (Hno_dup: R_Prio_No_Dup tcbls).
  {
    clear - H38.
    unfolds in H38. 
    mytac.
  }
  (** zhang hui's lemma **)
  hoare_lifts_trms_pre tcbdllseg. 
  eapply set_node_elim_hoare with (tid:=ctcb) (tcbls:=tcbls); eauto.
  {
    eapply TCBNode_P_set_rdy; auto.
    3:eauto.
    rewrite Hp1.
    apply nth_val'2nth_val; eauto.
    auto.
  }
  {
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  }
  {
    unfolds.
    unfold V_OSTCBNext , V_OSTCBPrev.
    simpl.
    auto.
  }

 (************************* exit critical ***********************************)
  hoare_split_pure_all.
  subst hprio.
  rewrite Hp1 in *.
  rewrite Hp2 in *.

  Ltac hoare_exit_critical2 :=
    match goal with
    | |- {|_ , _, ?li , _, _, _|}|- _ {{?P}} (sprim excrit) {{_}} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil) pre;
        eapply excrit1_rule'_ISnil_ISRemp'''_lg(* excrit1_rule'_ISnil_ISRemp''' *);
        [ intros; try (unfold OldOSInvWL); (*sep pauto;*)trycancel
        | idtac
        ]
      | _ => fail 1
      end
    end.
  Ltac hoare_forward_prim'2 :=
    let s := fresh in
    let H := fresh in
    match goal with
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} (sseq _ _) {{ _ }} =>
      eapply seq_rule; [ hoare_forward_prim'2
                       | try hoare_invchange ]
    | |- {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} =>
      eapply forward_rule2; [ first [ hoare_enter_critical
                                    | hoare_exit_critical2
                                    | idtac ]
                            | first [ intros s H; exact H
                                    | sep pauto ] ]
    end.
  hoare_forward_prim'2. 
  (*hoare forward prim.*)

  sep normal.
  sep eexists.
  sep cancel AOSEventFreeList.
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl.
  sep cancel AOSIntNesting.
  sep cancel AOSTCBFreeList.
  sep cancel AOSTime.
  sep cancel AGVars.
  sep cancel A_isr_is_prop.
  sep cancel absecblsid. 
  sep cancel abstcblsid.
  sep cancel ostmid. 
  sep cancel curtid. 
  sep split; auto. 
  sep cancel p_local. 
  sep cancel atoy_inv'.
  sep cancel AOSRdyTblGrp.
  
  (** AECBList **)
  unfold AECBList.
  sep normal.
  sep eexists.
  sep cancel OSEventList. 
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold_msg.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel Astruct.
  sep cancel Aarray.
  instantiate (20 := DSem i1). 
  unfold AEventData.
  sep split; auto.

  (** AOSTCBPrioTbl **)
  unfold AOSTCBPrioTbl.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel 7%nat 1%nat. (* PV vhold_addr .. *)
  (* inverts H88. *)
  sep cancel GAarray.
  sep cancel OSPlaceHolder. 

  (** AOSTCBList **)
  unfold AOSTCBList.
  sep normal.
  sep eexists.
  sep split; auto.
  sep cancel OSTCBList. 
  sep cancel tcbdllseg.
  sep cancel OSTCBCur. 
  sep cancel tcbdllseg.
  
  (** tcbdllflag **) 
  get_hsat Hsat.
  sep_lifts_trms_in Hsat tcbdllflag.
  unfold AEventData in Hsat. 
  eapply tcbdllflag_set_node in Hsat; eauto.
  sep cancel tcbdllflag. 
  2: { unfold same_prev_next. simpl. splits; auto. }

  sep_lifts_skp_in Hsat (objaux_node, (llsegobjaux, _N_ 1)). 
  eapply llsegobjaux_merge_hd in Hsat; eauto. 
  sep_lifts_trms_in Hsat (llsegobjaux tcblist_head, llsegobjaux (Vptr ctcb)). 
  eapply llsegobjaux_merge2_frm in Hsat; eauto. 
  unfold AOBJ.
  sep pauto. 
  unfold tcbllsegobjaux.
  sep_lifts_trms llsegobjaux.
  eapply llsegobjaux_set_node; eauto.
  2: { unfold same_prev_next. simpl. splits; auto. } 
  sep cancel llsegobjaux. 
  eapply AObjs_sem_set_wls'_preserve; eauto.
  sep cancel AObjs.
  eauto. 

  auto.
  auto.
  eapply obj_aux_p_sem_set_wls'_preserve; eauto. 

  (** TCBList_P **)
  eauto.
  eauto.
  eauto.
  split; auto.  

  
  (*RH_PrioTbl_P*)
  eauto.
  (** R_PrioTbl_P **)
  eapply r_priotbl_p_set_hold; auto; eauto.
  eauto.
  split; auto.

  clear - H26. 
  int auto.

  (** ecblist_p **)
  eapply ecblist_p_post_exwt_hold_sem
    with (v'12:=v'44) (v'39:=p2) (v'69:=v'62) (v'38:=p1) (v'13:=etbl) (v'36:=v'39); eauto. 
  
  eapply rl_etbl_ptbl_p; auto; eauto.

  lzh_simpl_int_eq; auto.
  
  clear - Hs3.
  mauto.

  (* RL_Tbl_Grp_P *)
  eauto.
  go. eauto.
  go.
  split; auto.
  go.
  simpl. eauto. eauto.

  assert (Htmp: ctcb = (htcb_addr, Int.zero) \/ ctcb <> (htcb_addr, Int.zero)) by tauto.
  destruct Htmp.
  subst ctcb.
  unfolds.
  unfold get; simpl.
  rewrite TcbMod.set_a_get_a.
  eauto.
  apply tidspec.eq_beq_true; auto.

  Set Nested Proofs Allowed. 
  Lemma rh_curtcb_set_nct:
    forall v'8 v'7 x tid ,
      RH_CurTCB v'8 v'7 ->
      v'8 <> tid ->
      RH_CurTCB v'8 (TcbMod.set v'7 tid x).
  Proof.
    intros.
    unfolds in H.
    simpljoin1.
    unfolds.
    exists x0 x1.
    rewrite TcbMod.set_sem.
    rewrite tidspec.neq_beq_false; eauto.
  Qed.

  eapply rh_curtcb_set_nct; auto.

  assert (st = wait (pevent_addr, Int.zero)).
  {
    eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto.
    mttac GetHWait ltac:(fun H=> rename H into Hgw).
    clear -Hgw.
    unfolds in Hgw; mytac; auto. 
  }
  subst st. 

  eapply rh_tcblist_ecblist_p_post_exwt_sem;eauto.
  (* ** ac: Check rh_tcblist_ecblist_p_post_exwt_sem. *)
  mttac GetHWait ltac:(fun H=> rename H into Hgw).
  clear -Hgw.
  unfolds in Hgw; mytac; auto. 

  (* unfold AEventData. *)
  pure_auto.

  (* crit. region exited *)

  hoare_split_pure_all.

  Ltac hoare_call2 :=
    match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
      match find_aop P with
      | some ?n =>
        hoare lifts (n::nil)%nat pre;
        eapply call_rule';
        [intuition eauto |
         intros;
         do 5 try (apply rvl_elim;[ symbolic_execution | ]);
         first [apply rvl_nil | simpl;auto] |
         intros;unfold_spec(*;sep pauto*) |
         idtac |
         sep_unfold_funpost |
         sep_unfold_funpre |
         simpl;eauto
        ]
      | none _ => idtac
      end
    end.
  eapply seq_rule; eapply forward_rule2.
  1: hoare_call2.
  5: try sep_unfold_funpost; sep pauto.
  6: sep pauto.
  (*hoare forward.*)

  sep normal.
  sep eexists.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel Aop. 
  sep cancel p_local. 
  sep split; auto.
  exact_s.
  go.  
  intros.
  get_hsat Hsat. sep destruct Hsat.
  exists (logic_val (V$ 1) :: x1).
  sep cancel p_local.
  sep auto.

  intros.
  get_hsat Hsat. sep destruct Hsat. 
  exists (logic_val x0 :: x1). 
  sep cancel p_local. 
  sep auto.

  hoare unfold.
  inverts H69. 

  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  pure_auto.
  eapply absinfer_seq_end.
  pure_auto.
  2: eauto.
  pure_auto.
  eapply absinfer_eq.

  eapply forward_rule2.
  1: eapply rete_rule'; [symbolic execution | intros].
  2: try sep_unfold_funpost; sep pauto.
  (*hoare forward.*)
  
  sep cancel A_dom_lenv.
  sep normal.
  exists (Vptr (pevent_addr, Int.zero)).
  exists (V$ OS_STAT_SEM).
  exists v'0. 
  sep eexists.
  sep cancel Aop. 
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel p_local. 
  sep cancel x.
  sep cancel ptr.
  sep pauto.

  introv Hp. simpl in Hp. inverts Hp. 

  Unshelve.
  auto.
  auto.
  auto.
  
Qed. 
