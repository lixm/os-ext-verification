
Require Import memory.
Require Import anno_language.
Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.


Definition OSTCBHighRdy:= 59%Z.
Definition OSTCBCur:=60%Z.

Definition gets_g (s:osstate):= (fst (fst (fst (fst s)))).
Definition gets_m (s:osstate) := (snd (fst (fst s))).
Definition get_env (m:smem):= (snd (fst m)).

Definition Dteq (D1 D2:clientst)(t:tid):Prop:=
  match D1 with 
    | ( _ ,evs1, _) => match D2 with
                         | ( _, evs2, _) =>
                           forall (t':tid), ~(t'=t) ->  get evs1 t' = get evs2 t'
                       end
  end. 

Definition Piteq (pi1 pi2: ltaskstset) (t:tid):Prop:=
  forall (t':tid), ~(t'=t) -> get pi1 t'= get pi2 t'.

Definition Steq (S1 S2 :osstate) (t:tid):Prop:=
  match S1 with
    | (D1, ir,  pi1)  => match S2 with 
                           | ( D2 , ir',  pi2) => Dteq D1 D2 t /\ Piteq pi1 pi2 t
                         end
  end.

Definition Dnewt (D:clientst) (t:tid):clientst:=
  match D with 
    | ( ge, cvs,  M) => ( ge, ( set cvs t emp), M)
  end.

Definition Tlnewt (tl:ltaskstset) (t:tid) :ltaskstset:=
  set tl t (true, nil, nil).

Definition Snewt (S:osstate) (t:tid):osstate:=
  match S with
    | (D, ir, tl) =>  ((Dnewt D t),   ir,  (Tlnewt tl t))
  end.


Definition projD (D:clientst) (t:tid) := 
  match D with (x,y,z) => 
               match  get y t with
                 | Some e => Some (x, e , z)
                 | _ => None
               end
  end.

Definition projS (S:osstate) (t:tid) :=
  match S with ( x, y, z)  =>
               match (projD x t),(get z t) with
                 | Some m,Some n => Some (m , y  , n)
                 | _,_ => None
               end
  end.


Definition vtoZ (v:val):option Z:=
  match v with
    | Vint32 a => Some (Int.unsigned a)
    |_=>None
  end.


Open Scope Z_scope.
Definition type_val_match (t:type) (v:val) :=
  match t,v with
    | Tnull, Vnull => true
    | Tptr t, Vnull => true
    | Tcom_ptr id,Vnull => true
    | Tint8,Vint32 v => (*if v is in the range of Tint8 return True, if not return False*)
      match (Int.unsigned v) <=? Byte.max_unsigned with
        | true => true
        | false => false
      end
    | Tint16,Vint32 v => (*if v is in the range of Tint16 return True, if not return False*)
      match (Int.unsigned v) <=? Int16.max_unsigned with
        | true => true
        | false => false
      end
    | Tint32,Vint32 v =>true
    | Tptr t,Vptr l => true
    | Tcom_ptr id,Vptr l => true
    | Tarray _ _, _ => true
    | Tstruct _ _, _ =>true
    | _,_=> false
  end.

Fixpoint tl_vl_match (tl:typelist) (vl:vallist) :=
  match tl with 
    | nil => 
      match vl with 
        | nil => true
        | _ => false
      end
    | t :: tl' => 
      match vl with
        | v :: vl' => if type_val_match t v then tl_vl_match tl' vl' else false
        | _ => false
      end
  end.  

Fixpoint field_offsetfld (id:var) (fld:decllist) (pos:int32):option int32:=
  match fld with 
    |dnil => None
    |dcons id' t fld'=>if Zeq_bool id id' then Some pos else field_offsetfld id fld' (Int.add (Int.repr (Z_of_nat (typelen t))) pos)
  end.

Definition field_offset (id:var) (fld:decllist) : option int32:= field_offsetfld id fld (Int.zero).

Definition istrue (v:val) : option bool :=
  match v with 
    | Vptr a => Some true
    | Vnull => Some false
    | Vint32 a =>  if (Int.eq a Int.zero) then Some false else Some true
    | _ => None
  end.

Fixpoint revlcons (d1 d2 :decllist): decllist :=
  match d1 with 
    | dnil => d2 
    | dcons x y d1' => revlcons d1' (dcons x y d2)
  end.

Fixpoint callcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> None
    | kcall  f  y z ks'=> Some (kcall f  y z ks')
    | kseq x  ks' => callcont ks'
    | kassignl x y ks' => callcont ks'
    | kassignr x y ks' => callcont ks'
    (*
| kcalle x y z ks' => callcont ks'
     *)
    | kfuneval  x y z w ks' => callcont ks'
    | kif x y ks' => callcont ks'
    | kwhile x y ks' => callcont ks'
    | kret  ks' => callcont ks'
    | kevent _ _ ks' => callcont ks'
  end .

Fixpoint intcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> Some (kint x y e ks')
    | kcall f  y z ks'=> None
    | kseq x  ks' => intcont ks'
    | kassignl x y ks' => intcont ks'
    | kassignr x y ks' => intcont ks'
    (*
| kcalle x y z ks' => intcont ks'
     *)
    | kfuneval   x y z w ks' => intcont ks'
    | kif x y ks' => intcont ks'
    | kwhile x y ks' => intcont ks'
    | kret  ks' => intcont ks'
    | kevent _ _ ks' => intcont ks'
  end .


Fixpoint AddStmtToKs (s:stmts) (ks:stmtcont):stmtcont:=
  match ks with
    | kstop => kseq s kstop
    | kseq s' ks' => kseq s' (AddStmtToKs s ks')
    | kcall f x E ks' => kcall f x  E (AddStmtToKs s ks')
    | kint c ke e ks' => kint c ke e (AddStmtToKs s ks')
    | kassignl e t ks' => kassignl e t (AddStmtToKs s ks')
    | kassignr v t ks' => kassignr v t (AddStmtToKs s ks')
    (*
    | kcalle f el t ks' => kcalle  f el t (AddStmtToKs s ks')
     *)
    | kfuneval  f vl tl el ks' => kfuneval  f vl tl el (AddStmtToKs s ks')
    | kif s' s'' ks' => kif s' s'' (AddStmtToKs s ks')
    | kwhile e s' ks' => kwhile e s' (AddStmtToKs s ks')
    | kret ks' => kret (AddStmtToKs s ks')

    | kevent a b  ks' => kevent a b (AddStmtToKs s ks')
  end.


Fixpoint AddKsToTail (ks1 ks2:stmtcont):stmtcont:=
  match ks2 with
    | kstop => ks1
    | kseq s' ks' => kseq s' (AddKsToTail ks1 ks')
    | kcall f x E ks' => kcall f x E (AddKsToTail ks1 ks')
    | kint c ke e ks' => kint c ke e (AddKsToTail ks1 ks')
    | kassignl e t ks' => kassignl e t (AddKsToTail ks1 ks')
    | kassignr v t ks' => kassignr v t (AddKsToTail ks1 ks')
    (*
    | kcalle f el t ks' => kcalle  f el t (AddKsToTail ks1 ks')
     *)
    | kfuneval  f vl tl el ks' => kfuneval  f vl tl el (AddKsToTail ks1 ks')
    | kif s' s'' ks' => kif s' s'' (AddKsToTail ks1 ks')
    | kwhile e s' ks' => kwhile e s' (AddKsToTail ks1 ks')
    | kret  ks' => kret  (AddKsToTail ks1 ks')
    | kevent a b  ks' => kevent a b (AddKsToTail ks1 ks')
  end.


Notation " ks2 '##' ks1 " := (AddKsToTail ks1 ks2)(at level 25, left associativity).

Fixpoint len_exprcont (ke : exprcont) : nat :=
  match ke with
    | kenil => O
    | keop1 _ _ ke' => S (len_exprcont ke')
    | keop2r _ _ _ _ ke' => S (len_exprcont ke')
    | keop2l _ _ _ _ ke' => S (len_exprcont ke')
    | kederef _ ke' => S (len_exprcont ke')
    | keoffset _ ke' => S (len_exprcont ke')
    | kearrbase _ _ ke' => S (len_exprcont ke')
    | kearrindex _ _ ke' => S (len_exprcont ke')
    | kecast _ _ ke' => S (len_exprcont ke')
  end.

Fixpoint len_stmtcont (ks : stmtcont) : nat :=
  match ks with
    | kstop => O
    | kseq _ ks' => S (len_stmtcont ks')
    | kcall  _ _ _ ks' => S (len_stmtcont ks')
    | kint _ _ _ ks' => S (len_stmtcont ks')
    | kassignl _ _ ks' => S (len_stmtcont ks')
    | kassignr _ _ ks' => S (len_stmtcont ks')
    (*
  | kcalle _ _ _ ks' => S (len_stmtcont ks')
     *)
    | kfuneval  _ _ _ _ ks' => S (len_stmtcont ks')
    | kif _ _ ks' => S (len_stmtcont ks')
    | kwhile _ _ ks' => S (len_stmtcont ks')
    | kret ks' => S (len_stmtcont ks')

                    
    | kevent a b ks' => S (len_stmtcont ks')
  end.


Definition nilcont (s:stmts): code := ((curs s), (kenil, kstop)).

Definition is_int_type t:=
  match t with
    | Tint8 => true
    | Tint16 => true
    | Tint32 => true
    | _ => false
  end.

Fixpoint evaltype (e:expr) (m:smem){struct e}:option type:=
  match m with 
      (genv, lenv, my) =>
      match e with
      | enull => Some Tnull
      | econst32 n => Some Tint32
      | eptrconst a => Some (Tptr Tint32)
      | evar x => match get lenv x with 
                      | Some (pair a t) =>  Some t 
                      | None => match get genv x with 
                                  | Some (pair a t) => Some t 
                                  | None => None
                                end
                    end
        | eunop uop e1 => match evaltype e1 m with
                            | Some t => uop_type t uop 
                            | None => None
                          end
        | ebinop bop e1 e2 => match evaltype e1 m, evaltype e2 m  with
                                | Some t1, Some t2 => bop_type t1 t2 bop
                                | _, _ => None
                              end   
        | ederef e' => match evaltype e' m with
                         | Some (Tptr t) => Some t
                         (*if type is Tcom_ptr ??*)
                         | _ => None
                       end
        | eaddrof e' => match e' with
                          | evar x  =>  match evaltype e' m  with
                                          | Some t =>  Some (Tptr t)
                                          | None => None
                                        end
                          | ederef e'' =>  match evaltype e'' m with
                                             | Some (Tptr t) => Some (Tptr t)
                                             | _=> None
                                           end
                          | efield e'' id  =>  match evaltype e' m  with
                                                 | Some t =>  Some (Tptr t)
                                                 | None => None
                                               end
                          | earrayelem e1 e2 =>  match evaltype e' m  with
                                                   | Some t =>  Some (Tptr t)
                                                   | None => None
                                                 end
                          | _ => None
                        end
        | efield e' id => match evaltype e' m with
                            | Some (Tstruct id' dl) => ftype id dl
                            | _=> None
                          end
        | ecast e' t => match evaltype e' m, t with 
                        | Some (Tptr t'), Tptr t'' => Some t
                        | Some Tnull, Tptr t' => Some t
                        | Some (Tcom_ptr t'), Tptr t'' => Some t  
                        | Some Tint8 , Tint8 => Some t
                        | Some Tint8 , Tint16 => Some t
                        | Some Tint8 , Tint32 => Some t
                        | Some Tint16 , Tint8 => Some t
                        | Some Tint16 , Tint16 => Some t
                        | Some Tint16 , Tint32 => Some t
                        | Some Tint32 , Tint8 => Some t
                        | Some Tint32 , Tint16 => Some t
                        | Some Tint32 , Tint32 => Some t
                        | _,_ => None
                        end

        | earrayelem e1 e2 => match evaltype e1 m, evaltype e2 m with
                                |Some (Tarray t n), Some Tint8 => Some t
                                |Some (Tarray t n), Some Tint16 => Some t
                                |Some (Tarray t n), Some Tint32 => Some t
                                |Some (Tptr t), Some Tint8 => Some t
                                |Some (Tptr t), Some Tint16 => Some t
                                |Some (Tptr t), Some Tint32 => Some t
                                | _ , _=>None
                              end
      end
  end.

Inductive assign_type_match : type -> type -> Prop:=
| eq_tnull: forall t1, (exists t, t1 = (Tptr t)) \/ (exists t,t1=(Tcom_ptr t)) \/ (t1=Tnull) -> assign_type_match t1 Tnull 
| eq_tvoid: assign_type_match Tvoid Tvoid
| eq_vptr: forall t1 t2, (exists t t', t1= (Tptr t) /\ t2 = (Tptr t'))->
                         assign_type_match t1 t2
| eq_vcomptr: forall t1 t2, ((exists t, t1= (Tptr t)) \/ (exists t, t1= (Tcom_ptr t))) /\ ((exists id,t2 = (Tcom_ptr id))\/(exists t,t2 = Tptr t)) ->
                            assign_type_match t1 t2
| eq_array: forall t1 t2, (exists t n, t1= (Tarray t n) /\ t2 = (Tarray t n))->
                          assign_type_match t1 t2
| array_to_vptr:  forall t1 t2, (exists t n, t1= (Tptr t) /\ t2 = (Tarray t n))->
                                assign_type_match t1 t2
| eq_struct: forall t1 t2,  (exists id dl, t1= (Tstruct id dl) /\ t2 = (Tstruct id dl))->
                            assign_type_match t1 t2
| eq_int: forall t1 t2, ((t1=Tint8\/t1=Tint16\/t1=Tint32)/\(t2=Tint8\/t2=Tint16\/t2=Tint32))->
                        assign_type_match t1 t2.



Fixpoint typematch (el:exprlist) (dl:decllist) (m:smem) :Prop:=
  match el,dl with
    | nil,dnil => True
    | cons e el',dcons x t dl' => (exists t',evaltype e m = Some t' /\ assign_type_match t t')/\ typematch el' dl' m
    | _,_=> False
  end.

Definition getoff (b:block) (i:offset) (id:ident) (e:expr) (m:smem):option addrval:=
  match evaltype e m with
    | Some (Tstruct id' dl) => match field_offset id dl with
                                 | Some off => Some ( b, ( Int.add (Int.repr i) off))
                                 | _ => None
                               end
    | _ => None
  end.


Definition get_genv (m : smem) :=
  match m with
    | (ge, le , M) => ge
  end.


Definition get_lenv (m : smem) :=
  match m with
    | (ge, le , M) => le
  end.


Definition get_mem (m : smem) :=
  match m with
    | (ge, le , M) => M
  end.

Definition addrval_to_addr (a:addrval):=
  match a with
    | (b,i) => (b,Int.unsigned i)
  end.
Definition addr_to_addrval (a:addr):=
  match a with
    | (b,i) => (b,Int.repr i)
  end.

Definition load (t : type) (m : mem) (l : addr) : option val :=
  match t with 
    | Tarray _ _ => Some (Vptr (addr_to_addrval l))
    | _ => loadm t m l 
  end.

Definition cast_eval i t t':=
  match t,t' with
    | Tint8,Tint8 => Some i
    | Tint8,Tint16 => Some i
    | Tint8,Tint32 => Some i
    | Tint16,Tint16 => Some i
    | Tint16,Tint32 => Some i
    | Tint32,Tint32 => Some i
                            
    | Tint32,Tint8 => Some (Int.modu i (Int.repr Byte.modulus))
    | Tint32,Tint16 => Some  (Int.modu i (Int.repr Int16.modulus))
    | Tint16,Tint8 => Some (Int.modu i (Int.repr Byte.modulus))
    | _,_ => None
  end.


Lemma cast_eval_tptr_none:
  forall x t,cast_eval x (Tptr t) (Tptr t) = None.
Proof.
  intros.
  simpl.
  auto.
Qed.


Fixpoint evalval (e:expr) (m:smem) :option val:= 
  match evaltype e m with
    | Some t =>  
        match e with 
        | enull => Some Vnull
        | econst32 n => Some (Vint32 n)
        | eptrconst a => Some (Vptr a)
        | evar x => match get (get_lenv m) x with
                      | Some (pair a t) => load t (get_mem m) (a,0%Z)
                      | None =>
                        match get (get_genv  m) x with
                          | Some (pair a t) => load t (get_mem m) (a,0%Z)
                          | None => None
                        end
                    end
        | eunop op1 e' =>  match evalval e' m with
                             | Some v=> uop_eval v op1
                             | _ => None
                           end
                             
        | ebinop op2 e1 e2 =>  match evalval e1 m, evalval e2 m with
                                 | Some v1,Some v2 => match evaltype e1 m, evaltype e2 m with
                                                        | Some t1, Some t2 => bop_eval v1 v2 t1 t2 op2
                                                        | _,_ => None
                                                      end 
                                 | _,_ => None
                               end
        | eaddrof e' =>  match e' with
                           | evar x =>  evaladdr e' m 
                           | ederef e'' => evalval e'' m
                           | efield e'' id => evaladdr e' m 
                           | earrayelem e1 e2 => evaladdr e' m 
                           | _ => None
                         end
        | ederef e' => match evalval e' m with
                         | Some (Vptr ad) =>  load t (get_mem  m) (addrval_to_addr ad) 
                         | _ => None
                       end
        | efield e' id => match (evaladdr e' m) with
                            | (Some (Vptr ( b,  i))) => match getoff b (Int.unsigned i) id e' m with
                                                          | Some ad => load t (get_mem m) (addrval_to_addr ad)
                                                          | _ => None
                                                        end
                            | _ => None
                          end
        | ecast e' t' =>
          match evaltype e' m with
            | Some te =>
              match is_int_type te,is_int_type t' with
                | true, true =>
                  match evalval e' m with
                    | Some (Vint32 x) => match (cast_eval x te t') with
                                           | Some x' => Some (Vint32 x')
                                           | None => None
                                         end
                    | _ => None
                  end
                | _ , _ => evalval e' m
              end
            | _ => None
          end
        | earrayelem e1 e2 => match (evalval e1 m),(evalval e2 m) with
                                |Some (Vptr ( b,  i)), Some v =>
                                 match v with
                                   | Vint32 z => load t (get_mem m) ( b, Int.unsigned (Int.add i
                                                                                               (Int.mul (Int.repr (Z_of_nat (typelen t))) z )))
                                   |_ => None
                                 end
                                |_,_=>None
                              end
                                
      end
    | _ => None
  end
with evaladdr (e:expr) (m:smem) :option val:=
       match e with
         | evar x => match get (get_lenv m) x with
                       |Some (pair a t) => Some (Vptr (a,Int.zero))
                       |_ => match get (get_genv m) x with
                               |Some (pair a t) => Some (Vptr (a,Int.zero))
                               |_ => None
                             end
                     end
         | ederef e' => evalval e' m
         | efield e' id => match evaladdr e' m with
                             | (Some (Vptr ( b, i))) => match getoff b (Int.unsigned i) id e' m with
                                                          |Some ad => Some (Vptr  ad)
                                                          |_=> None
                                                        end
                             | _ => None
                           end
         | earrayelem e1 e2 => match (evaltype e1 m), (evalval e1 m),(evalval e2 m) with
                                 |Some (Tarray t n), Some (Vptr (b, i)), Some v =>
                                  match v with
                                    | Vint32 z => Some (Vptr (b, (Int.add i (Int.mul (Int.repr (Z_of_nat (typelen t))) z))))
                                    |_=>None
                                  end
                                 |Some (Tptr t), Some (Vptr (b, i)), Some v =>
                                  match v with
                                    | Vint32 z => Some (Vptr (b, (Int.add i (Int.mul (Int.repr (Z_of_nat (typelen t))) z))))
                                    |_=>None
                                  end
                                 |_, _ ,_=>None
                               end
         |_=> None
       end.


Fixpoint getaddrlist (l:list (prod var (prod block type))):list (prod block type):=
  match l with
    | nil => nil
    | cons (pair x (pair ad t)) l'=> cons (pair ad t) (getaddrlist l')  
  end.

Definition getaddr (le:env):list (prod block type):=
  match le with
    | EnvMod.listset_con a _=> getaddrlist a
  end.

Fixpoint tlmatch (tl:typelist) (dl:decllist) :Prop:=
  match tl with
    | nil => match dl with
               | dnil => True
               | _ => False
             end
    | cons t tl' => match dl with
                      | dcons  _ t' dl'=> tlmatch tl' dl'/\ t'=t
                      | _ => False
                    end
  end.


Inductive estep: cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop :=
| enull_step : forall m ke,
                 estep (cure enull) ke m [Vnull] ke m
| ec32_step: forall (i:int32) (m:smem) (ke:exprcont), 
               estep (cure (econst32 i)) ke m [Vint32 i] ke m
| eptrc_step: forall a m ke, 
               estep (cure (eptrconst a)) ke m [Vptr a] ke m
| evar_step : forall (x:var) (v:val) (m:smem) (ke:exprcont),
                evalval (evar x) m =Some v ->  estep (cure (evar x)) ke m [v] ke m
| eaddr_step: forall (x:var) (v:val) (m:smem) (ke:exprcont),
                evalval (eaddrof (evar x)) m = Some v ->  
                estep (cure (eaddrof (evar x))) ke m [v] ke m
| ederef_step: forall (e:expr) (t:type) (m:smem) (ke:exprcont),
                 evaltype e m = Some (Tptr t) -> 
                 estep (cure (ederef e)) ke m (cure e) (kederef t ke) m
| eaddrderef_step: forall e m ke,
                     estep (cure (eaddrof (ederef e))) ke m (cure e) ke m
| esidaddr_step: forall (e:expr) (id id':ident) i (dl:decllist) (ke:exprcont) (m:smem),
                   evaltype e m = Some (Tstruct id' dl) ->
                   field_offset id dl = Some i -> 
                   estep (cure (eaddrof (efield e id))) ke m (cure (eaddrof e))
                         (keoffset i ke) m
| eaptrelemaddr_step:  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem),
                         evaltype e1 m = Some (Tptr t) ->  
                         estep (cure (eaddrof (earrayelem e1 e2))) ke m  
                               (cure e1) (kearrbase e2 t ke) m
| eaelemaddr_step:  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem),
                      evaltype e1 m = Some (Tarray t n) ->  
                      estep (cure (eaddrof (earrayelem e1 e2))) ke m  
                            (cure  e1) (kearrbase e2 t ke) m
| esid_step : forall (e:expr) (id id':ident) (t:type) (dl:decllist)
                     (ke:exprcont) (m:smem),
                evaltype e m = Some (Tstruct id' dl) -> ftype id dl = Some t -> 
                estep (cure (efield e id)) ke m (cure (eaddrof (efield e id)))
                      (kederef t ke) m
| eaelem_step :  forall (e1 e2:expr) (t:type) (n:nat)  (ke:exprcont) (m:smem),
                   evaltype e1 m = Some (Tarray t n) ->  
                   estep (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
                         (kederef t ke) m
| eaptrelem_step :  forall (e1 e2:expr) (t:type)  (ke:exprcont) (m:smem),
                      evaltype e1 m = Some (Tptr t) ->  
                      estep (cure (earrayelem e1 e2)) ke m (cure (eaddrof (earrayelem e1 e2)))
                            (kederef t ke) m
| euopstep:  forall (e:expr) (t:type) (op1:uop) (ke:exprcont) (m:smem),
               evaltype e m = Some t ->  
               estep (cure (eunop op1 e)) ke m (cure e) (keop1 op1 t ke) m
| ebop_step:  forall (e1 e2:expr) (t1 t2:type) (op2:bop) (ke:exprcont) (m:smem),
                evaltype e1 m = Some t1 -> evaltype e2 m =Some t2 ->  
                estep (cure (ebinop op2 e1 e2)) ke m (cure e1) (keop2r op2 e2 t1 t2 ke) m
| ecast_step: forall (e:expr) (t t' t'': type) (m:smem) (ke:exprcont),
                t=Tptr t' -> evaltype e m = Some (Tptr t'') ->  
                estep (cure (ecast e t)) ke m (cure e) ke m
| ecastnull_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                    t=Tptr t' -> evaltype e m = Some Tnull ->  
                    estep (cure (ecast e t)) ke m (cure e) ke m
| ecastcomptr_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont) x,
                      t = Tptr t' -> evaltype e m = Some (Tcom_ptr x) ->  
                      estep (cure (ecast e t)) ke m (cure e) ke m
| ecastint_step: forall (e:expr) (t t' : type) (m:smem) (ke:exprcont),
                   evaltype e m = Some t' -> is_int_type t = true -> is_int_type t' = true ->  
                   estep (cure (ecast e t)) ke m (cure e) (kecast t' t ke) m
| evcastint_step: forall v v' ke t t' m,
                    cast_eval v t t' = Some v' ->
                    estep [Vint32 v] (kecast t t' ke) m [Vint32 v'] ke m
| evderef_step : forall (genv lenv:env) (M:mem) (a:addrval) (v:val) (t:type) 
                        (m:smem) (ke:exprcont),
                   m= (genv, lenv, M) -> load t M (addrval_to_addr a) =Some v -> 
                   estep [Vptr a] (kederef t ke) m  [v] ke m
| evoff_step : forall (b:block) (i i':int32) (ke:exprcont) (m:smem),
                 estep [Vptr (b, i)] (keoffset i' ke) m 
                       [Vptr (b, (Int.add i i'))] ke m
| evaddrelem_step : forall (v:val) (e:expr) (t:type) (ke:exprcont) (m:smem),
                      estep [v] (kearrbase e t ke) m (cure e) (kearrindex v t ke) m
| evaddrv_step: forall (v:val) (b:block) (i i' i'':int32)
                       (t:type) (ke:exprcont) (m:smem),
                  v = Vint32 i'' -> i'= Int.repr (Z_of_nat (typelen t)) ->
                  estep  [v] (kearrindex (Vptr (b, i)) t ke) m
                         [Vptr ( b, (Int.add i (Int.mul i' i'')))] ke m
| evuop_step : forall (op1:uop) (v v':val) (ke:exprcont) (m:smem) (t:type),
                 uop_eval v op1 = Some v' -> 
                 estep [v] (keop1 op1 t ke) m [v'] ke m
| evbop1_step : forall (op2:bop) (e:expr) (v:val) (t1 t2:type) (ke:exprcont) (m:smem),
                  estep [v] (keop2r op2 e t1 t2 ke) m
                        (cure e) (keop2l op2 v t1 t2 ke) m
| evbop2_step : forall (op2:bop) (v v' v'':val) (t1 t2 :type) (ke:exprcont) (m:smem),
                  bop_eval v' v t1 t2 op2=Some v'' -> 
                  estep [v] (keop2l op2 v' t1 t2 ke) m  [v'']  ke m.


Inductive estepstar :  cureval -> exprcont -> smem -> cureval -> exprcont -> smem -> Prop:=
| e_step0 : forall c ke m, estepstar c ke m c ke m
| e_stepn : forall c ke m c' ke' m' c'' ke'' m'', estep c ke m c' ke' m'-> 
                                                  estepstar c' ke' m' c'' ke'' m'' -> 
                                                  estepstar c ke m c'' ke'' m''.

Definition getfunrettype (fn : function) := match fn with
                                              | (t, _ ,_,_) => t
                                            end.


Inductive sstep: progunit -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> Prop :=
(*Assign Steps*)
| sassign_step: forall (e1 e2:expr) (t1 t2:type) (ks:stmtcont) (m:smem) (p:progunit),
                  evaltype e1 m =Some t1 -> 
                  evaltype e2 m=Some t2 -> 
                  assign_type_match t1 t2 ->
                  sstep p (curs (sassign e1 e2)) ks m (cure e2) (kassignr e1 t1 ks) m

| sassignrv_step : forall (m:smem) (p:progunit) (v:val) (e:expr) (t:type) (ks:stmtcont),
                     sstep p [v] (kassignr e t ks) m 
                           (cure (eaddrof e))(kassignl v t ks) m

| sassignend_step : forall (m m':smem) (ge le :env) (M M':mem) (a:addrval) (v:val) 
                           (p:progunit) (ks:stmtcont) (t:type),
                      m= (ge, le, M) -> 
                      m'= ( ge, le, M') ->
                      store t M (addrval_to_addr a) v =Some M' ->
                      sstep p [Vptr a] (kassignl v t ks) m (curs (sskip None)) ks m' 

(*Function call Steps*)
| scalle_step: forall (p:progunit) (e:expr) (t:type) (m:smem) 
                      (f:fid) (ks:stmtcont) (el:exprlist),
                 evaltype e m =Some t ->
                 sstep p (curs (scalle e f el)) ks m (curs (scall f el))(kassignr e t ks) m

| spcall_step : forall (p:progunit) (t:type) (e:expr) (el:exprlist)
                       (m:smem) (ks:stmtcont) (f:fid), 
                  evaltype e m =Some t ->
                  sstep p (curs (scall f (cons e el))) ks m 
                        (cure e) (kfuneval f nil (t::nil) el ks) m

| snpcall_step : forall (m:smem)(f:fid) (p:progunit) (ks: stmtcont),
                   sstep p (curs (scall f nil)) ks m (curs (sfexec f nil nil)) ks m

| svfeval_step: forall (p:progunit) (v:val) (e:expr) (vl:vallist)
                       (el:exprlist) (ks:stmtcont) (m:smem) (f:fid) (tl:typelist) (t:type),
                  evaltype e m = Some t -> 
                  sstep p  [v] (kfuneval f vl tl (cons e el) ks) m 
                        (cure e) (kfuneval f (cons v vl) (t::tl) el ks) m
| svfevalnil_step: forall (p:progunit) (v:val) (vl:vallist) 
                          (ks:stmtcont) (m:smem) (f:fid) tl,
                     sstep p [v] (kfuneval f vl tl nil ks) m 
                           (curs (sfexec f (cons v vl ) tl)) ks m

| sfexec_step : forall (m m' :smem) (ge le:env) (M:mem) (p:progunit)
                       (t:type)(d1 d2:decllist)
                       (s:stmts) (ks:stmtcont) (vl:vallist) (f:fid) tl,
                  m=(ge, le, M) -> 
                  m'=  (ge, emp, M) -> 
                  p f=Some (t, d1, d2, s)->  
                  tlmatch (List.rev tl) d1  -> 
                  tl_vl_match tl vl = true ->
                  sstep p (curs (sfexec f vl tl)) ks m 
                        (curs (salloc vl (revlcons d1 d2))) 
                        (kcall f  s le ks) m'

| sallocp_step : forall (m m':smem) (ge le le':env) (M M' M'':mem)
                        (b:block) (v:val) (p:progunit) 
                        (vl:vallist) (dl:decllist) (ks:stmtcont) (x:var) (t:type),
                   m= (ge, le, M) -> 
                   m' = ( ge, le', M'') ->
                   alloc x t le M le' M' -> 
                   get le' x = Some (b,t)-> 
                   store t M'  (b, 0%Z) v = Some M''->
                   sstep p (curs (salloc  (cons v vl) (dcons x t dl))) ks m 
                         (curs (salloc  vl dl)) ks m'

| salloclv_step : forall (m m':smem) (ge le le':env) (M M':mem)
                         (t:type) (x:var) (p:progunit)
                         (dl:decllist) (ks:stmtcont),
                    m =  (ge, le, M) -> 
                    m' = (ge,le', M') ->
                    alloc x t le M le' M' ->
                    sstep p (curs (salloc  nil (dcons x t dl))) ks m
                          (curs (salloc  nil dl)) ks m'

| sallocend_step: forall (p:progunit) (f :fid) 
                         (s:stmts) (ks:stmtcont) (m:smem) (E:env),
                    sstep p (curs (salloc  nil dnil)) (kcall f s E ks) m 
                          (curs s) (kcall f s  E ks) m

| sret_step: forall (p:progunit) (m:smem)(M:mem) (ge le le':env)(f :fid)
                    (ks ks':stmtcont)  (al:freelist) (s: stmts),
               m=(ge, le, M) -> 
               callcont ks =Some (kcall f s le' ks') ->
               getaddr le = al ->
               sstep p (curs sret) ks m (curs (sfree al None)) ks m


| srete_step : forall (p:progunit) (ks:stmtcont)  
                      (e:expr) (m:smem),
                 sstep p (curs (srete e)) ks m (cure e) (kret ks) m

| sretv_step: forall (p:progunit) (m:smem) (le ge:env)
                     (M:mem) (ks:stmtcont) (f:fid)  
                     (al:freelist) (v:val)(s : stmts) ,
                m=(ge, le, M) ->
                callcont ks <> None -> 
                getaddr le = al->
                sstep p [v] (kret ks) m (curs (sfree al (Some v))) ks m 

| sfree_step : forall (m m':smem) (le ge :env) (M M':mem) (b:block) (t:type) (p:progunit) 
                      (al:freelist) (ks:stmtcont) (v:option val),
                 m=(ge, le, M) -> 
                 m' = (ge, le , M') -> 
                 free t b M =Some M' -> 
                 sstep p (curs (sfree (cons (pair b t) al) v)) ks m 
                       (curs (sfree al v)) ks m'

| sfreeend_step : forall (p:progunit) (ks ks':stmtcont) (m m':smem)
                         (ge le le':env) (M:mem) (s : stmts)(f:fid) (v:option val),
                    m= (ge, le, M) -> 
                    m' = (ge, le', M) -> 
                    callcont ks =Some (kcall f  s le' ks') ->
                    sstep p (curs (sfree nil v)) ks m (curs (sskip v)) ks' m'

(*Sequential Step*)                   
| sseq_step : forall (s1 s2:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                sstep p (curs (sseq s1 s2)) ks m (curs s1) (kseq s2 ks) m

| svseq_step : forall (p:progunit) (v:val) (s:stmts) (ks:stmtcont) (m:smem),
                 sstep p [v] (kseq s ks) m (curs s) ks m

| sskip_step : forall (s:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                 sstep p SKIP (kseq s ks) m (curs s) ks m


(*If then else Step*)
| sif_step : forall (e:expr) (s1 s2 :stmts) (ks:stmtcont) (m:smem) (p:progunit),
               sstep p (curs (sif e s1 s2)) ks m (cure e) (kif s1 s2 ks) m

| sifthen_step: forall  (e:expr) (s :stmts) (ks:stmtcont) (m:smem) (p:progunit),
                  sstep p (curs (sifthen e s)) ks m (cure e) (kif s (sskip None) ks) m

| svift_step: forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem),
                istrue v = Some true ->
                sstep p (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s1) ks m
| sviff_step: forall (p:progunit) (v:val) (s1 s2:stmts) (ks:stmtcont) (m:smem),
                istrue v = Some false ->
                sstep p (curs (sskip (Some v))) (kif s1 s2 ks) m (curs s2) ks m

(*While Step*)

| swhile_step : forall (e:expr) (s:stmts) (ks:stmtcont) (m:smem) (p:progunit),
                  sstep p (curs (swhile e s)) ks m (cure e) (kwhile e s ks) m


| svwhilet_step: forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem),
                   istrue v=Some true ->
                   sstep p  (curs (sskip (Some v))) (kwhile e s ks) m (curs s) (kseq (swhile e s) ks) m

| svwhilef_step: forall (p:progunit) (v:val) (s:stmts) (e:expr) (ks:stmtcont) (m:smem),
                   istrue v=Some false ->
                   sstep p (curs (sskip (Some v))) (kwhile e s ks) m SKIP ks m.



Inductive sstepev : progunit -> cureval -> stmtcont -> smem -> cureval -> stmtcont -> smem -> val -> Prop:=
|sprint_step: forall (e:expr) (v:val) (m:smem) (ks:stmtcont) (s:stmts) (p:progunit),
                evalval e m = Some v -> sstepev p (curs (sprint e)) ks m SKIP ks m v.


Inductive cstep: progunit -> code -> smem -> code -> smem -> Prop :=
| expr_step : forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
                     (ke ke':exprcont) (ks:stmtcont),
                C = ( c, ( ke, ks)) -> 
                estep c ke m c' ke' m' ->
                cstep p C m (c', ( ke', ks)) m'
| stmt_step : forall (p:progunit) (C:code) (m m':smem) (c c':cureval)
                     (ks ks':stmtcont),
                C = (c, (kenil, ks)) -> 
                sstep p c ks m c' ks' m' ->
                cstep p C m (c', (kenil , ks')) m'.

Inductive cstepev : progunit-> code -> smem -> code -> smem -> val-> Prop :=
| stmt_stepev :  forall (expr_step p p:progunit) (C:code) (m:smem) (c c':cureval)
                        (ks ks':stmtcont) (v:val),
                   C = (c, (kenil, ks)) -> 
                   sstepev p c ks m c' ks' m v ->
                   cstepev p C m (c', (kenil, ks')) m v. 

Inductive cstepstar: progunit -> code -> smem -> code -> smem -> Prop :=
| c_stepstar0: forall (p:progunit) (C:code) (m:smem),
                 cstepstar p C m C m
| c_stepstarn: forall (p:progunit) (C C' C'':code) (m m' m'':smem),
                 cstep p C m C' m' -> cstepstar p C' m' C'' m''->
                 cstepstar p C m C'' m''.

Definition cstepabt (p:progunit) (C:code) (m:smem) := 
  ~ (exists C' m' ev, cstep p C m C' m' \/ cstepev p C m C' m' ev).


Definition pumerge (p1 p2:progunit):=
  fun (f:fid) => match p1 f with 
                   | Some fc => Some fc 
                   | None => match p2 f with 
                               | Some fc => Some fc
                               | None => None
                             end
                 end.

Open Scope Z_scope.
Definition is_length (si:is):=
  match (length si) with
    | 1%nat => Vint32 Int.one
    | _ => Vint32 Int.zero
  end.


Open Scope nat_scope.

Definition IsEnd (C : code) : Prop := exists v, C = (curs (sskip v), (kenil, kstop)).

Definition IsSwitch (C : code) : Prop := exists x ks,
                                           C = (curs (sprim (switch x)),(kenil, ks)).

Definition IsFcall (C:code) : Prop := exists f vl tl ks,
                                        C = (curs (sfexec f vl tl), (kenil,ks)).

Definition IsRet (C : code) : Prop := (exists ks, C = (curs sret, (kenil, ks))
                                                  /\ callcont ks = None/\intcont ks =None).

Definition IsRetE (C : code) : Prop := (exists v ks, C = ([v], (kenil , 
                                                                (kret ks)))/\
                                                     callcont ks = None/\intcont ks =None).

Definition IsIRet (C : code) : Prop := (exists ks, C = (curs (sprim exint), (kenil, ks)) /\ intcont ks = None/\callcont ks =None).


Definition IsStkInit (C:code) := (exists e1 e2 e3 ks, C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))).

Definition IsStkFree (C:code) := (exists e ks, C = (curs (sprim (stkfree e)),(kenil,ks))).


(****)
Definition eqdomtls (tls tls':TcbMod.map):=
  forall tid, indom tls tid <-> indom tls' tid.


Definition eqdomO (O O':osabst):= (forall (x:absdataid), indom O x <-> indom O' x) /\
                                  ( forall tls,  get O abstcblsid = Some (abstcblist tls) ->
                                                 exists tls',  get O' abstcblsid = Some (abstcblist tls') /\ eqdomtls tls tls' ).

Definition tidsame (O O':osabst):=  get O curtid =  get O' curtid.


(* the new definition of a step of execution by an abstract statement *)
(* the modification is performed to take care of partiality ---
     the result of an atomic operation or an assumption can be the abstract statement "spec_abort"
     (the notation for it is ABORT) *)
(* the result of evaluating an explicity assumption (ASSERT b) is also the abstract statement
     "spec_abort" in case the assumed conditoin b is not satisfied *)
Inductive spec_step:
  ossched ->
  spec_code -> osabst -> LAuxSt ->
  spec_code -> osabst -> LAuxSt -> Prop :=

| spec_prim_step:
    forall sc O O' (step:osabstep) v Of vl OO OO' lau asrt,
      step vl O (v, Some O') ->
      eqdomO O O' ->
      tidsame O O' ->
      join O Of OO ->
      join O' Of OO' ->
      spec_step sc (spec_prim asrt vl step) OO lau (spec_done v) OO' lau
                
| spec_prim_step_abt:
  forall sc O (step:osabstep) v Of vl OO lau asrt, 
    step vl O (v, None) -> 
    join O Of OO ->
    spec_step sc (spec_prim asrt vl step) OO lau spec_abort OO lau 
  
| spec_seq_step_end:
  forall v s1 s2 O O' sc lau lau',
    spec_step sc s1 O lau (spec_done v) O' lau' ->
    spec_step sc (spec_seq s1 s2) O lau s2 O' lau'

| spec_seq_step_abt:
  forall s1 s2 O O' sc lau lau',
    spec_step sc s1 O lau spec_abort O' lau' -> 
    spec_step sc (spec_seq s1 s2) O lau spec_abort O lau

| spec_seq_step_cont: 
  forall O O' s1 s2 s1' sc lau lau',
    spec_step sc s1 O lau s1' O' lau' ->
    ((~exists vo, s1' = spec_done vo) /\ s1' <> spec_abort) -> 
    spec_step sc (spec_seq s1 s2) O lau (spec_seq s1' s2) O' lau' 

| spec_choice_step1:
    forall O s1 s2 sc lau,
      spec_step sc (spec_choice s1 s2) O lau s1 O lau

| spec_choice_step2:
    forall O s1 s2 sc lau,
      spec_step sc (spec_choice s1 s2) O lau s2 O lau 

| spec_assume_step:
    forall O Of (b:absexpr) OO sc lau asrt,
      b O lau ->
      join O Of OO ->
      spec_step sc (spec_assume asrt b)  OO lau (spec_done None) OO lau

| spec_assert_step_cont:
  forall O Of (b:absexpr) OO sc lau,
    b O lau ->
    join O Of OO ->
    spec_step sc (spec_assert b) OO lau (spec_done None) OO lau

| spec_assert_step_abt:
    forall O Of (b:absexpr) OO sc lau,
      ~(b O lau) ->
      join O Of OO -> 
      spec_step sc (spec_assert b) OO lau spec_abort OO lau 
                
| spec_sched_step:
    forall t O Of OO (sc:ossched) lau asrt,
      get O curtid = Some (oscurt t) ->
      sc O t -> 
      join O Of OO ->
      spec_step sc (sched asrt) OO lau (spec_done None) OO lau
                
| spec_setpt_step:
  forall sc OO lau lau', 
    spec_step sc (spec_set_lst lau') OO lau (spec_done None) OO lau'  

| spec_atm_step1:
  forall sc cd OO OO'  lau lau' vo, 
    spec_step sc cd OO lau (spec_done vo) OO' lau' ->
    spec_step sc (spec_atm cd) OO lau (spec_done None) OO' lau'

| spec_atm_spep1_abt:
  forall sc cd OO OO'  lau lau',  
    spec_step sc cd OO lau spec_abort OO' lau' ->
    spec_step sc (spec_atm cd) OO lau spec_abort OO lau 

| spec_atm_step2:
  forall sc cd cd' OO OO' OO'' lau lau' lau'', 
    spec_step sc cd OO lau cd' OO' lau' ->
    ((~exists vo, cd' = spec_done vo) /\ cd' <> spec_abort) ->  
    spec_step sc (spec_atm cd') OO' lau' (spec_done None) OO'' lau'' -> 
    spec_step sc (spec_atm cd) OO lau (spec_done None) OO'' lau''
. 


Inductive spec_stepstar:
  ossched -> spec_code -> osabst -> LAuxSt -> spec_code -> osabst -> LAuxSt -> Prop :=
  
| spec_stepO:
    forall c O sc lau,
      spec_stepstar sc c O lau c O lau
                    
| spec_stepS:
    forall c O c' O' c'' O'' lau lau' lau'' sc,
      spec_step sc c O lau c' O' lau' ->
      spec_stepstar sc c' O' lau' c'' O'' lau'' ->
      spec_stepstar sc c O lau c'' O'' lau''.


Fixpoint absintcont (ks:stmtcont): option stmtcont:=
  match ks with
    | kstop => None
    | kint x y e ks'=> absintcont ks'
    | kcall f  y z ks'=> absintcont ks'
    | kseq x  ks' => absintcont ks'
    | kassignl x y ks' => absintcont ks'
    | kassignr x y ks' => absintcont ks' 
    | kfuneval   x y z w ks' => absintcont ks'
    | kif x y ks' => absintcont ks'
    | kwhile x y ks' => absintcont ks'
    | kret  ks' => absintcont ks'
    | kevent c ke ks' => Some (kevent c ke ks')
  end .


Inductive hapistep:
  osspec ->
  code -> osabst -> LAuxSt ->
  code -> osabst -> LAuxSt -> Prop:=

(* the constructor is modified by introducing an arbitrary list vl' of values *)
(* the values in vl' is used to represent the intermediate results of computation
     in a service function 
     --- including the return values from the underlying kernel functions *)
| hapienter_step:
  forall (A :osspec) (B:osapispec) (C:osintspec) (D : ossched) (O:osabst) (cd cd':code)
         (ks:stmtcont) (f:fid) (vl:vallist) r tl tp vl' lau,
    A= (B, C, D) ->
    tl_vl_match tl vl = true->
    cd = (curs (sfexec f (List.rev vl) (List.rev tl)), (kenil, ks)) ->
    cd'=  (curs (hapi_code (r (vl++vl'))), (kenil, ks))->
    B f = Some (r,(tp,tl)) ->
    hapistep A cd O lau cd' O lau
              
| hidapi_step :
  forall (A :osspec) (O O':osabst) ke ks cd cd' lau lau',
    spec_step (snd A) cd O lau cd' O' lau' ->
    hapistep A ((curs (hapi_code cd )),(ke, ks)) O lau ((curs (hapi_code cd')),(ke,ks)) O' lau'

| hapiexit_step :
  forall (A :osspec) (O:osabst) ke ks v lau,
    absintcont ks = None -> 
    hapistep A ((curs (hapi_code (spec_done v))),(ke, ks)) O lau ((curs (sskip v)),(ke,ks)) O lau
             
| hintex_step: forall  (A :osspec) c ke ks O lau,
    hapistep A  (curs (hapi_code (spec_done None)),(kenil,kevent c ke ks)) O lau (c,(ke,ks)) O lau
.

Inductive htstep:
  hprog -> tid -> code -> clientst -> osabst -> LAuxSt -> code -> clientst -> osabst -> LAuxSt -> Prop:=

| htclt_step : forall (p:hprog) (pc:progunit) (A:osspec) (c c':code) (m m':smem)
                      (cenvs:cltenvs)  (ge le le':env) (M M':mem) (t:tid) 
                      (cst cst':clientst) (O:osabst) lau,
    p= (pc, A) -> 
    cstep pc c m c' m' -> 
    m = (ge, le, M) -> m' = (ge, le', M') ->
    get cenvs t = Some le ->
    cst = (ge,cenvs, M) ->
    cst'=  (ge, ( set cenvs t le'), M') ->
    htstep p t c cst O lau c' cst' O lau

| hapi_step : forall (p:hprog)(A: osspec) (pc:progunit) (O O':osabst) (c c':code) (cst:clientst) t lau lau',
    p=(pc, A) ->
    hapistep  A c O lau c' O' lau' ->
    htstep p t c cst O lau c' cst O' lau'.


Inductive htstepstar:
  hprog -> tid -> code -> clientst -> osabst -> LAuxSt -> code -> clientst -> osabst -> LAuxSt -> Prop:=
  
| ht_starO: forall (p:hprog)  (c:code) (cst:clientst) (O:osabst) t lau,
    htstepstar p t c cst O lau c cst O lau 
               
| ht_starS: forall (p:hprog)  (c c' c'':code) (cst cst' cst'':clientst) (O O' O'':osabst) t lau lau' lau'',
    htstep p t c cst O lau c' cst' O' lau' ->
    htstepstar p t c' cst' O' lau' c'' cst'' O'' lau'' ->
    htstepstar p t c cst O lau c'' cst'' O'' lau''.


Inductive htistep: osintspec -> code  -> osabst -> code  -> osabst -> Prop :=
  
| hinten_step:
  forall  (C :osintspec)  (O:osabst) c ke ks (i:hid) l,
    C i = Some l ->
    htistep C (c,(ke,ks)) O (curs (hapi_code l),(kenil,kevent c ke ks)) O.


Inductive hpstep:
  hprog ->
  tasks -> clientst -> osabst -> LAuxStMod.map -> 
  tasks -> clientst -> osabst -> LAuxStMod.map -> Prop:=
  
| hp_step: forall (p:hprog) (T T':tasks) (O O':osabst) (cst cst':clientst) 
                  (C C':code) (t:tid) laust laust' lau lau',
    get O curtid = Some (oscurt t) ->
    htstep p t C cst O lau C' cst' O' lau' ->
    get T t = Some C ->
    T' =  set T t C' ->
    get laust t = Some lau ->
    laust' = set laust t lau' -> 
    hpstep p T cst O laust T' cst' O' laust'
           
| hi_step : forall (p:hprog) pc A  ispec B  (T T':tasks)
                   (O O':osabst) (cst:clientst) 
                   (C C':code) (t:tid) laust,
    p = (pc, (A, ispec, B)) ->
    get O curtid = Some (oscurt t) ->
    get T t = Some C ->
    T' =  set T t C' ->
    htistep ispec C O C' O' ->
    hpstep p T cst O laust T' cst O' laust
           
| hswi_step: forall (p:hprog) pc A B sd (T T':tasks) (cst:clientst) (O:osabst) (t t':tid) C ke ks s laust asrt,
    p = (pc,(A,B,sd)) ->
    sd O t'->
    get O curtid = Some (oscurt t) ->
    get T t = Some C ->
    C = (curs (hapi_code (spec_seq (sched asrt) s)), (ke,ks)) ->
    T' =  set T t (curs (hapi_code s),(ke,ks)) ->
    hpstep p T cst O laust T' cst (set O curtid (oscurt t')) laust
.            
      

Definition nabt (T: tasks) : Prop :=
  forall t c ke ks,
    get T t = Some (c, (ke, ks)) -> c <> curs (hapi_code spec_abort).

Definition hpstep_ok p T cst O aust T' cst' O' aust' :=
  hpstep p T cst O aust T' cst' O' aust' /\ nabt T'. 
  
Inductive hpstepokstar:
  hprog ->
  tasks -> clientst -> osabst -> LAuxStMod.map ->
  tasks -> clientst -> osabst -> LAuxStMod.map -> Prop :=  

| hp_stepO:
  forall (p:hprog) (T:tasks) (cst:clientst) O aust,
    hpstepokstar p T cst O aust T cst O aust

| hp_stepS:
  forall p (T T' T'': tasks) cst cst' cst'' O O' O'' aust aust' aust'',
    hpstep_ok p T cst O aust T' cst' O' aust' ->
    hpstepokstar p T' cst' O'  aust' T'' cst'' O'' aust'' ->
    hpstepokstar p T cst O aust T'' cst'' O'' aust''.
