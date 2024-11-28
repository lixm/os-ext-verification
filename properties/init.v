
Require Import memory.
Require Import anno_language.
Require Import anno_opsem.
Require Import common_defs. 

Open Scope int_scope. 


Definition init_tsk_st (O: osabst) := 
  exists tls ts,
    get O abstcblsid = Some (abstcblist tls)
    /\ get O atidlsid = Some (atidls ts)
    /\ (forall t st p, get tls t = Some (p, st) -> st = rdy)
    /\ atids_valid tls ts.  

Definition init_objs_st (O: osabst) :=
  (exists objs, get O absobjsid = Some (absobjs objs)) 
  /\ (exists els,
         get O absecblsid = Some (absecblist els)
         /\ forall eid, get els eid = None). 
                 
Definition init_gaump (O: osabst) :=
  exists gaump, 
    get O gauxstid = Some (gauxst gaump) 
    /\ forall eid, get gaump eid = None. 
      
Definition init_laump (T: tasks) (laump: LAuxStMod.map) := 
  forall t,
    get T t <> None -> 
    get laump t = Some {| tskpt := PtNormal |}.
  
Definition init_st_sema
  (_: progunit) (T: tasks) (cst: clientst) (O: osabst) (laump: LAuxStMod.map) :=  
  (* init_cli_st cst /\  *)
  init_tsk_st O /\ init_objs_st O /\
    init_gaump O /\ init_laump T laump.  



(* Set Asymmetric Patterns. *)
(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)

(* Definition init_cli_st (cst: clientst) := *)
(*   exists ges ces m, *)
(*     cst = (ges, ces, m) *)
(*     /\ (forall t E x b tp, *)
(*            get ces t = Some E -> *)
(*            get E x = Some (b, tp) -> *)
(*            get m (b, 0%Z) <> None).  *)

(* Definition init *)
(*   (pu: progunit) *)
(*   (T: tasks) (cst: clientst) (O: osabst) (laump: LAuxStMod.map) := *)
  
(*   init_tsk pu T cst O /\ init_st T cst O laump.  *)


