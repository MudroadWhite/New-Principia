Require Import PM.pm.lib.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.

Open Scope single_app_equiv.
Open Scope double_app_equiv.

(* 
Starting from chapter 12, every variables being quantified at the rhs has to be
either an "Individual" or a "Predicate". For example, "forall P, P /\ Q" might 
never appear, and instead, it will be either "forall Individual P, P /\ Q" or 
"forall Predicate Phi, Phi (Individual P)" where Phi P = P /\ Q
*)

Definition n12_1 (X : Prop) (f Phi : Prop -> Prop) : 
  let f := Predicate f X 1 in
  exists f, (Phi X) <[- x -]> f x.
Admitted.

Definition n12_11 (X Y : Prop) (f Phi : Prop -> Prop -> Prop) :
  let f := Predicate_2 f X Y 1 in
  exists f, (Phi X Y) <[- x y -]> f x y.
Admitted.

Close Scope single_app_equiv.
Close Scope double_app_equiv.
