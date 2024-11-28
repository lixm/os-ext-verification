
Require Import anno_language.

Definition nml_asrt := (fun lau => lau = {| tskpt := PtNormal |}). 
                         
Notation " x '(|' vl '|)' " := (spec_prim nml_asrt vl x) (at level 40). 

Notation  " 'END' v " := (spec_done v) (at level 40). 
Notation  " x ';;' y " := (spec_seq x y) (right associativity, at level 44). 
Notation  " x '??' y " := (spec_choice x y) (right associativity, at level 45). 
Notation  " 'ASSUME' b " := (spec_assume nml_asrt b) (at level 40). 
Notation " 'ASSERT' b " := (spec_assert b) (at level 40). 
Notation " 'ABORT' " := (spec_abort) (at level 40). 
Notation "'Sched'" := (sched nml_asrt) (at level 40). 

(* Notation " x '|!' vl '!|' " := (spec_prim nml_asrt vl x) (at level 40).   *)

Notation "asrt '#' x '[|' vl '|]' " := (spec_prim asrt vl x) (at level 40). 
