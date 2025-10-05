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

Definition n10_01 (Phi : Prop -> Prop) : 
  (exists x, Phi x) = ~ (forall x, ~ Phi x). Admitted.

Definition n10_02 (Phi Psi : Prop -> Prop) : 
  Phi x -[ x ]> Psi x = forall x, Phi x -> Psi x. Admitted.

Definition n10_03 (Phi Psi : Prop -> Prop) : 
  Phi x <[- x -]> Psi x = forall x, (Phi x <-> Psi x). Admitted.

Theorem n10_1 (Phi : Prop -> Prop) (Y : Prop) : (forall x, Phi x) -> Phi Y.
Proof.
  pose proof n9_2.
Admitted.

(* Thm 10.11: If Phi y is true whatever possible argument y may be, then forall, Phi x is true. [*9.13] *)

Theorem n10_12 (Phi : Prop -> Prop) (P : Prop) : 
  (forall x, P \/ Phi x) -> P \/ forall x, Phi x.
Proof.
  pose proof n9_25.
Admitted.

(* Thm 10.121: If Phi x is significant, then if a is of the same type as x, Phi a is significant, and vice versa. [*9.14] *)

(* Thm 10.122: If for some a, there is a proposition Phi a, then there is a function Phi x^, and vice versa. [*9.15] *)

(* Thm 10.13: If Phi x^ and Psi x^ takes arguments of the same type, and we have |- Phi x and |- Psi x, we shall have |- Phi x /\ Psi x . *)

Theorem n10_14 (Phi Psi : Prop -> Prop) (Y : Prop) : 
  (forall x, Phi x) /\ (forall x, Psi x)
  -> Phi Y /\ Psi Y.
Proof.
Admitted.

Theorem n10_2 (Phi : Prop -> Prop) (P : Prop) :
  (forall x, P \/ Phi x) <-> P \/ (forall x, Phi x).
Proof. 
Admitted.

Theorem n10_21 (Phi : Prop -> Prop) (P : Prop) :
  (forall x, P -> Phi x) <-> P -> (forall x, Phi x).
Proof. 
Admitted.

Theorem n10_22 (Phi Psi : Prop -> Prop) (P : Prop) :
  (forall x, Phi x /\ Psi x) <-> (forall x, Phi x) /\ (forall x, Psi x).
Proof. 
Admitted.

(* Thm *10.221: omitted *)

Theorem n10_23 (Phi : Prop -> Prop) (P : Prop) :
  (forall x, Phi x -> P) <-> (exists x, Phi x) -> P.
Proof.
Admitted.

Theorem n10_23_alt (Phi : Prop -> Prop) (P : Prop) :
  (forall x, Phi x -> P) <-> (exists x, Phi x) -> P.
Proof.
Admitted.

Theorem n10_24 (Phi : Prop -> Prop) (Y : Prop) :
  Phi Y -> exists x, Phi x.
Proof.
Admitted.

Theorem n10_25 (Phi : Prop -> Prop) : (forall x, Phi x) -> (exists x, Phi x).
Proof.
Admitted.

Theorem n10_251 (Phi : Prop -> Prop) : (forall x, ~Phi x) -> ~(forall x, Phi x).
Proof.
Admitted.

Theorem n10_252 (Phi : Prop -> Prop) : ~(exists x, Phi x) <-> (forall x, Phi x).
Proof.
Admitted.

Theorem n10_253 (Phi : Prop -> Prop) : ~(forall x, Phi x) -> (exists x, ~Phi x).
Proof.
Admitted.

Theorem n10_252_alt (Phi : Prop -> Prop) : ~(exists x, Phi x) <-> (forall x, Phi x).
Proof.
Admitted.

Theorem n10_253_alt (Phi : Prop -> Prop) : ~(forall x, Phi x) -> (exists x, ~Phi x).
Proof.
Admitted.

Theorem n10_252 (Phi : Prop -> Prop) : ~(exists x, Phi x) <-> (forall x, Phi x).
Proof.
Admitted.

Theorem n10_26 (Phi Psi : Prop -> Prop) : 
  ((forall z, Phi z -> Psi z) /\ Phi x) -> Psi x.
Proof.
Admitted.

Theorem n10_27 (Phi Psi : Prop -> Prop) : 
  (forall z, Phi z -> Psi z) -> ((forall z, Phi z) -> (forall z, Psi z)).
Proof.
Admitted.

Theorem n10_28 (Phi Psi : Prop -> Prop) :
  (forall x, Phi x -> Psi x) -> ((exists x, Phi x) -> (exists x, Psi x)).
Proof.
Admitted.

Theorem n10_281 (Phi Psi : Prop -> Prop) :
  (forall x, Phi x <-> Psi x) -> ((exists x, Phi x) <-> (exists x, Psi x)).
Proof.
Admitted.

Theorem n10_29 (Phi Psi Chi : Prop -> Prop) :
  (forall x, Phi x -> Psi x) /\ (forall x, Phi x /\ Chi x) 
  <-> forall x, Phi x -> (Psi x /\ Chi x).
Proof.
Admitted.

Theorem n10_3 (Phi Psi Chi : Prop -> Prop) :
  ((forall x, Phi x -> Psi x) /\ (forall x, Psi x -> Chi x)) -> forall x, Phi x -> Chi x.
Proof.
Admitted.

Theorem n10_301 (Phi Psi Chi : Prop -> Prop) :
  (forall x, Phi x <-> Psi x) /\ (forall x, Psi x <-> Chi x) -> forall x, Phi x <-> Chi x.
Proof.
Admitted.

Theorem n10_31 (Phi Psi Chi : Prop -> Prop) :
  