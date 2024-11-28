
Require Import memory.
Require Import anno_language.
Require Import anno_opsem.
Require Import aux_notations.
Require Import sem_sys.
Require Import succ_gen.
Require Import common_defs.
Require Import protect.
Require Import aux_lemmas.

Lemma nml_asrt_tskpt:
  forall lau, 
    nml_asrt lau -> tskpt lau = PtNormal.
Proof.
  introv Hna.
  unfolds in Hna.
  subst.
  simpl; auto.
Qed.

Local Hint Resolve nml_asrt_tskpt: nml_ppt_lemmas.

Ltac desvl0 vl :=
  match goal with
    Hhs: context[has_succ], Hsp: context[spec_step] |- _ => 
      destruct vl;
      [ simpl in Hhs; 
        lets Heq: abt_succs_contra Hhs; eauto; subst; 
        inverts Hsp | idtac ]
  end. 

Ltac des_vl :=
  match goal with
    vl: vallist |- _ => desvl0 vl
  | vl: list val |- _ => desvl0 vl
  end. 

Ltac end_abt H tac := 
  match type of H with
    ?P /\ ?Q => let h1 := fresh in let h2 := fresh in destruct H as (h1 & h2); first [tac h1 | tac h2]
  | ?P \/ ?Q => let h1 := fresh in let h2 := fresh in destruct H as [h1 | h2]; [tac h1 | tac h2]
  | ABORT <> ABORT => solve [false]
  | ~exists vo, END ?vo_ = END vo => solve [false; apply H; eexists; eauto]
  end. 
       
Ltac end_abt_tac H := 
  match type of H with
    context [ABORT <> ABORT] => end_abt H end_abt_tac
  | context [~exists vo, END ?vo1 = END vo] => end_abt H end_abt_tac
  end.

Ltac symexe0 :=
  (* let symexe0 := idtac in *)
  match goal with
    H: has_succ0 _ _ |- _ =>
      inverts H;
      try (
          match goal with
            H_: has_succ0 _ _ |- _ =>
              protect H_;
              try (match goal with
                     H__: spec_step _ _ _ _ _ _ _ |- _ => protect H__
                   end)
          end); symexe0
  | H: spec_step _ (spec_atm _) _ _ _ _ _ |- _ => idtac
  | H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; symexe0
  | H: context[ABORT <> ABORT] |- _ => end_abt_tac H
  | H: context[~exists vo, END ?vo1 = END vo] |- _ => end_abt_tac H
  | Hhsat: context[head_asrt_sat] |- _ =>
      solve [
          simpl in Hhsat; simpljoin;
          simpl; unfold nml_asrt; unfold pend_asrt; simpl; (try splits);
          eauto with nml_ppt_lemmas
        ]                                                                  
  | _ => idtac
  end.

Ltac symexe :=
  match goal with
    H1: ProtectWrapper _, H2: ProtectWrapper _ |- _ =>
      unprotect H1; unprotect H2;
      symexe0
  | _ => symexe0
  end.

Lemma semwait_nabt_spec_step_sat_preserve:
  forall sc vl cd O cd' O' lau lau', 
    semwait vl <> ABORT -> 
    has_succ (semwait vl) cd ->     
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  repeat des_vl.
  unfolds in Hnth.
  simpl in *.
  destruct vl.
  2: false.

  destruct Hnth.
  {
    subst cd.
    simpl in Hhsat.
    inverts Hstep; simpl; simpljoin; eauto.
  }
  repeat symexe.
  simpl; auto.
  {
    simpl.
    inverts H9.
    repeat symexe.
    inverts H1.
    inverts H6.
    repeat symexe.
    clear H4; symexe.
    clear H6; symexe.
    inverts H4.
    inverts H6.
    repeat symexe.
    inverts H0.
    inverts H7.
    symexe.
    clear H10; symexe.
    clear H7; symexe.
    clear H7; symexe.
    clear H6; symexe.
  }
  clear H9; symexe.
  {
    inverts H3.
    repeat symexe.
    repeat symexe.
    clear H4; repeat symexe.
  }
  {
    inverts H7.
    repeat symexe.
    inverts H1.
    inverts H6.
    symexe.
    clear H4; symexe.
    clear H6; symexe.
    inverts H4. inverts H6. inverts H1; symexe.
    clear H7; inverts H0; symexe.
    clear H6; symexe.
  }
  {
    inverts H7.
    repeat symexe.
  }
  {
    inverts H2; symexe.
    clear H4; symexe.
  }
Qed. 

Lemma semwait_nabt_spec_step_sat_end:
  forall sc vl cd O vo O' lau lau',
    semwait vl <> ABORT ->
    has_succ (semwait vl) cd -> 
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  repeat des_vl.
  unfolds in Hnth.
  simpl in *.
  destruct vl.
  2: false.
  destruct Hnth.
  {
    subst cd.
    simpl in Hhsat.
    inverts Hstep; simpl; simpljoin; eauto.
  }
  repeat symexe.
Qed.

Lemma semsignal_nabt_spec_step_sat_preserve:
  forall sc vl cd O cd' O' lau lau',
    semsignal vl <> ABORT ->
    has_succ (semsignal vl) cd -> 
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  repeat des_vl.
  unfolds in Hnth.
  simpl in *.
  destruct vl.
  2: false.
  destruct Hnth.
  {
    subst cd.
    simpl in Hhsat.
    inverts Hstep; simpl; simpljoin; eauto.
  }
  repeat symexe.
Qed.

Lemma semsignal_nabt_spec_step_sat_end:
  forall sc vl cd O vo O' lau lau',
    semsignal vl <> ABORT ->
    has_succ (semsignal vl) cd -> 
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  repeat des_vl.
  unfolds in Hnth.
  simpl in *.
  destruct vl.
  2: false.
  destruct Hnth.
  {
    subst cd.
    simpl in Hhsat.
    inverts Hstep; simpl; simpljoin; eauto.
  }
  repeat symexe.  
Qed.

