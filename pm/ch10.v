Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch9.

(* The goal of chapter 10 is extend the propositions from `p -> q` 
to `forall x, p x-> q x`. In order to do this, we mostly don't use the 
definitions in chapter 9 and develop a new way to interpret `exists` 
instead.
*)

Notation " P -[ x ]> Q " := (forall x, P -> Q) 
  (at level 80, x binder, right associativity,
  format " '[ ' P '/' '[ ' -[ x ]> ']' '/' Q ']' ")
  : type_scope.

Notation " P <[- x -]> Q " := (forall x, P <-> Q)
  (at level 80, x binder, right associativity,
  format " '[ ' P '/' '[ ' <[- x -]> ']' '/' Q ']' ")
  : type_scope.

Definition n10_01 (Phi : Prop -> Prop) : (exists x, Phi x) = ~ (forall x, ~ Phi x). Admitted.

Definition n10_02 (Phi Psi : Prop -> Prop) : Phi x -[ x ]> Psi x = forall x, Phi x -> Psi x.
  Admitted.

Definition n10_03 (Phi Psi : Prop -> Prop) : Phi x <[- x -]> Psi x = forall x, (Phi x <-> Psi x).
  Admitted.

Theorem n10_1 (Phi : Prop -> Prop) (Y : Prop) : (forall x, Phi x) -> Phi Y.
Proof.
  pose proof n9_2.
Admitted.