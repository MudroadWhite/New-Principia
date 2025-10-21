Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch9.
Require Import PM.pm.ch10.

(* TODO: change the name of these scopes *)
Declare Scope double_app_impl.
Declare Scope double_app_equiv.

Open Scope double_app_impl.
Open Scope double_app_equiv.

(* TODO: extend these notations to arbitrary amount of parameters *)
Notation " A -[ x y : P ]> B " := (∀ (x y : P), A → B)
  (at level 85, x name, y name, right associativity,
  format " '[' A '/' '[ ' -[ x y '/' : P ]> ']' '/' B ']' ")
  : double_app_impl.

Notation " A -[ x y ]> B " := (∀ (x y : Prop), A → B)
  (at level 80, x name, y name, right associativity,
  format " A '/' '[ ' -[ x y ]> ']' '/' B ")
  : double_app_impl.

Notation " A <[- x y : P -]> B " := (∀ (x y : P), A ↔ B)
  (at level 85, x name, right associativity,
  format " '[' A '/' '[ ' <[- '[ ' x y ']' : P -]> ']' '/' B ']' ")
  : double_app_equiv.

Notation " A <[- x y -]> B " := (∀ (x y : Prop), A ↔ B)
  (at level 80, x name, right associativity,
  format " '[' A '/' '[ ' <[- '[ ' x y ']' -]> ']' '/' B ']' ")
  : double_app_equiv.

Definition n11_01 (Phi : Prop -> Prop -> Prop) : 
  (forall x y, (Phi x y)) = (forall x, forall y, Phi x y).
Admitted.

Definition n11_02 (Phi : Prop -> Prop -> Prop -> Prop) :
  (forall x y z, Phi x y z) 
  = (forall x, forall y, forall z, Phi x y z).
Admitted.

Definition n11_03 (Phi : Prop -> Prop -> Prop) :
  (exists x y, Phi x y) = (exists x, exists y, Phi x y).
Admitted.

Definition n11_04 (Phi : Prop -> Prop -> Prop -> Prop) :
  (exists x y z, Phi x y z) = (exists x, exists y, exists z, Phi x y z).
Admitted.

Definition n11_05 (Phi Psi : Prop -> Prop -> Prop) :
  (Phi x y -[ x y ]> Psi x y) = (forall x y, Phi x y -> Psi x y).
Admitted.

Definition n11_06 (Phi Psi : Prop -> Prop -> Prop) :
  (Phi x y <[- x y -]> Psi x y) = (forall x y, (Phi x y <-> Psi x y)).
Admitted.

(* Pp *11.07: "Whatever possible argument `x` may be, `Phi(x, y)` is true 
whatever possible argument `y` may be" implies that the corresponding 
statement with `x` and `y` interchanged except in "Phi(x, y)". *)
Definition n11_07 (Phi : Prop -> Prop -> Prop) :
  (forall x y, Phi x y) -> (forall y x, Phi x y).
Admitted.

(* Here we make a little difference because this order is prettier *)
Theorem n11_1 (W Z : Prop) (Phi : Prop -> Prop -> Prop) : 
  (forall x y, Phi x y) -> Phi W Z.
Proof.
Admitted.

(* Thm *11.11 : to be filled *)

Theorem n11_12 (P : Prop) (Phi : Prop -> Prop -> Prop) : 
  (forall x y, P \/ Phi x y) -> (P \/ forall x y, Phi x y).
Proof.
Admitted.

(* Thm *11.13 : to be filled *)

(* An alternative version of *11.13, but with more limited usages 
  than *11.13 *)
Theorem n11_14 (W Z : Prop) (Phi Psi : Prop -> Prop -> Prop) : 
  ((forall x y, Phi x y) /\ (forall x y, Psi x y))
  -> (Phi W Z /\ Psi W Z).
Proof.
Admitted.

(* WTF?!! *)
Theorem n11_2 (Phi : Prop -> Prop -> Prop) : 
  (forall x y, Phi x y) <-> (forall y x, Phi x y).
Proof.
Admitted.

