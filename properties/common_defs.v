
Require Import memory. 
Require Import anno_language.
Require Import anno_opsem.

Definition distinct (ts: list tid) :=
  forall i j t1 t2,
    List.nth_error ts i = Some t1 ->
    List.nth_error ts j = Some t2 ->
    i <> j ->
    t1 <> t2. 

Definition atids_valid (tls: TcbMod.map) (ts: list tid) :=
  distinct ts /\ 
    forall t, (get tls t <> None <-> List.In t ts). 

Definition in_rtbl (st:taskstatus):=
  match st with
  | rdy => True
  | wait x => False
  end.

Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.

Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
  (exists tls prio st,
      get O abstcblsid = Some (abstcblist tls) /\
        get tls t = Some (prio,st) /\
        in_rtbl st /\
        forall i prio' st',
          i <> t ->
          get tls i = Some (prio',st') ->
          in_rtbl st'-> 
          Int.ltu prio prio'=true). 

Definition GetHWait (tls:TcbMod.map) (wl:list tid) (t:tid) := 
  In t wl /\ 
    exists p st,
      get tls t = Some (p, st) /\
        forall t',
          t<>t' ->
          In t' wl ->
          exists p' st', get tls t' = Some (p',st') /\ (Int.ltu p p' = true)%Z. 

Definition eqdomto :=
  fun (T: tasks) (O: osabst) => 
    exists tls,
      get O abstcblsid = Some (abstcblist tls)
      /\ (forall t, (exists a, get tls t = Some a ) <-> (exists C,get T t = Some C)). 

Definition init_tsk (p:progunit) (T:tasks) (O:osabst) := 
  eqdomto T O
  /\ forall t C,
      get T t = Some C ->
      exists s f d1 d2 t, C = nilcont s /\ p f = Some (t, d1, d2, s). 

Definition reachable
  (hp: hprog)
  (ini_st: progunit -> tasks -> clientst -> osabst -> LAuxStMod.map -> Prop) 
  (T: tasks) (cst: clientst) (O: osabst) aust :=
  exists pu spc,
    hp = (pu, spc)
    /\ (exists T0 cst0 O0 aust0,
           init_tsk pu T0 O0 /\ ini_st pu T0 cst0 O0 aust0
           /\ hpstepokstar hp T0 cst0 O0 aust0 T cst O aust). 


(* the satisfaction of the current annotated assertion in a given
    annotated abstract statement cd, by a given local auxiliary state lau *)   
Fixpoint head_asrt_sat (cd: spec_code) (lau: LAuxSt) := 
  match cd with
    spec_prim asrt _ _ => asrt lau
  | sched asrt => asrt lau
  | spec_done _ => True 
  | spec_seq cd1 cd2 => head_asrt_sat cd1 lau
  | spec_choice cd1 cd2 => head_asrt_sat cd1 lau /\ head_asrt_sat cd2 lau
  | spec_assume asrt _ => asrt lau
  | spec_assert _ => True
  | spec_abort => True 
  | spec_set_lst _ => True
  | spec_atm cd => head_asrt_sat cd lau
  end.

Fixpoint hasrt_sat_cont (ks: stmtcont) lau (li: LAuxSt -> Prop) :=
  match ks with
    kstop => True
  | kseq _ ks
  | kint _ _ _ ks
  | kassignr _ _ ks
  | kassignl _ _ ks
  | kfuneval _ _ _ _ ks
  | kif _ _ ks
  | kwhile _ _ ks
  | kret ks => hasrt_sat_cont ks lau li
  | kcall f s E ks => (* no abs stmt in s *)
      hasrt_sat_cont ks lau li
  | kevent c ke ks =>
      hasrt_sat_cont ks lau li
      /\
        (absintcont ks = None ->
         ((forall cd, c = curs (hapi_code cd) -> head_asrt_sat cd lau)
          /\
            (((exists vo, c = curs (hapi_code (spec_done vo))) \/ ~(exists cd, c = curs (hapi_code cd))) ->
             li lau)))
  end.

Definition hasrt_sat (C: code) lau (li: LAuxSt -> Prop) :=
  exists c ke ks,
    C = (c, (ke, ks))
    /\ (
        absintcont ks = None ->
        ((forall cd, c = curs (hapi_code cd) -> head_asrt_sat cd lau)
         /\
           (((exists vo, c = curs (hapi_code (spec_done vo))) \/ ~(exists cd, c = curs (hapi_code cd))) ->
            li lau)
        )
      )
    /\ hasrt_sat_cont ks lau li.

Definition pool_hasrt_sat (T: tasks) laump (li: LAuxSt -> Prop) := 
  forall t C lau, get T t = Some C -> get laump t = Some lau -> hasrt_sat C lau li.
