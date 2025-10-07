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

(* TODO: extend the notation to multiple arguments *)
Notation " A -[ x : P ]> B " := (forall (x : P), A -> B)
  (at level 85, x name, right associativity,
  format " '[ ' A '/' '[ ' -[ x : P ]> ']' '/' B ']' ")
  : type_scope.

Notation " A -[ x ]> B " := (( A -[ x : Prop ]> B ))
  (at level 80, x name, right associativity,
  format " '[ ' A '/' '[ ' -[ x ]> ']' '/' B ']' ")
  : type_scope.

Notation " A <[- x : P -]> B " := (forall (x : P), A <-> B)
  (at level 85, x name, right associativity,
  format " '[ ' A '/' '[ ' <[- x : P -]> ']' '/' B ']' ")
  : type_scope.

Notation " A <[- x -]> B " := (A <[- x : Prop -]> B)
  (at level 80, x name, right associativity,
  format " '[ ' A '/' '[ ' <[- x -]> ']' '/' B ']' ")
  : type_scope.

Definition n10_01 (Phi : Prop -> Prop) : 
  (exists x, Phi x) = ~ (forall x, ~ Phi x). Admitted.

Definition n10_02 (Phi Psi : Prop -> Prop) : 
  Phi x -[ x ]> Psi x = forall x, Phi x -> Psi x. Admitted.

Definition n10_03 (Phi Psi : Prop -> Prop) : 
  Phi x <[- x -]> Psi x = forall x, (Phi x <-> Psi x). Admitted.

Theorem n10_1 (Phi : Prop -> Prop) (Y : Prop) : (forall x, Phi x) -> Phi Y.
Proof.  exact (n9_2 Phi Y). Qed.

(* Thm 10.11: If Phi y is true whatever possible argument y may be, then forall, Phi x is true. [*9.13] *)
Theorem n10_11 (Y : Prop) (Phi : Prop -> Prop) : Phi Y -> forall x, Phi x.
Proof.
Admitted.

Theorem n10_12 (Phi : Prop -> Prop) (P : Prop) : 
  (forall x, P \/ Phi x) -> P \/ forall x, Phi x.
Proof.  exact (n9_25 P Phi). Qed.

(* Thm 10.121: If Phi x is significant, then if a is of the same type as x, Phi a is significant, and vice versa. [*9.14] *)

(* Thm 10.122: If for some a, there is a proposition Phi a, then there is a function Phi x^, and vice versa. [*9.15] *)

(* Thm 10.13: If Phi x^ and Psi x^ takes arguments of the same type, and we have |- Phi x and |- Psi x, we shall have |- Phi x /\ Psi x . *)
(* NOTE: we didn't enforce `is_same_type` so far. Currently I decide to just leave it manually specified *)
Theorem n10_13 (Phi Psi : Prop -> Prop) (X : Prop) :
  Phi X -> Psi X -> (Phi X /\ Psi X).
Proof.
Admitted.

Theorem n10_14 (Phi Psi : Prop -> Prop) (Y : Prop) : 
  (forall x, Phi x) /\ (forall x, Psi x)
  -> Phi Y /\ Psi Y.
Proof.
  pose proof (n10_1 Phi Y) as S1.
  pose proof (n10_1 Psi Y) as S2.
  assert (S3 : ((forall x, Phi x)-> Phi Y) /\ ((forall x, Psi x) -> Psi Y )).
  {
    pose proof (n10_13 (fun x => (forall x, Phi x) -> Phi Y) 
        (fun x => (forall x, Psi x) -> Psi Y) Y) as n10_13.
    MP n10_13 S1.
    MP n10_13 S2.
    exact n10_13. 
  }
  assert (S4 : ((forall x, Phi x) /\ (forall x, Psi x)) -> (Phi Y /\ Psi Y)).
  {
    pose proof (n3_47 (∀ x : Prop, Phi x) (∀ x : Prop, Psi x)
                (Phi Y) (Psi Y)) as n3_47.
    MP n3_47 S3.
    exact n3_47.
  }
  exact S4.
Qed.

Theorem n10_2 (Phi : Prop -> Prop) (P : Prop) :
  (forall x, P \/ Phi x) <-> P \/ (forall x, Phi x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (P \/ forall x, Phi x) -> P \/ Phi Y).
  {
    pose proof (n10_1 Phi Y) as n10_1.
    pose proof (Sum1_6 P (∀ x : Prop, Phi x) (Phi Y)) as Sum1_6.
    MP Sum1_6 n10_1.
    exact Sum1_6.
  }
  assert (S2 : forall y, (P \/ (forall x, Phi x) -> P \/ Phi y)).
  {
    pose proof (n10_11 Y (fun y => (P \/ forall x, Phi x) -> P \/ Phi y)) as n10_11.
    MP n10_11 S1.
    exact n10_11.
  }
  assert (S3 : (P \/ (forall x, Phi x)) -> (forall y, P \/ Phi y)).
  {
    setoid_rewrite -> Impl1_01a in S2.
    pose proof (n10_12 (fun y => P ∨ Phi y) (¬ (P ∨ ∀ x : Prop, Phi x))) as n10_12.
    MP n10_12 S2.
    setoid_rewrite <- Impl1_01a in n10_12.
    exact n10_12.
  }
  assert (S4 : (forall y, (P \/ Phi y)) -> P \/ (forall x, Phi x)).
  { exact (n10_12 Phi P). }
  assert (S5 : (forall x, P \/ Phi x) <-> P \/ (forall x, Phi x)).
  { split; [exact S4 | exact S3]. }
  exact S5.
Qed.

Theorem n10_21 (Phi : Prop -> Prop) (P : Prop) :
  (forall x, P -> Phi x) <-> (P -> (forall x, Phi x)).
Proof. 
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  pose (n10_2 Phi (~P)) as n10_2.
  repeat setoid_rewrite <- Impl1_01a in n10_2.
  exact n10_2.
Qed.

Theorem n10_22 (Phi Psi : Prop -> Prop) (P : Prop) :
  (forall x, Phi x /\ Psi x) <-> (forall x, Phi x) /\ (forall x, Psi x).
Proof. 
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (forall x, Phi x /\ Psi x) -> Phi Y /\ Psi Y).
  { exact (n10_1 (fun x => Phi x /\ Psi x) Y). }
  assert (S2 : (forall x, Phi x /\ Psi x) -> Phi Y).
  { 
    (* TODO: examine the format of the original proof *)
    pose (Simp3_26 (Phi Y) (Psi Y)) as Simp3_26.
    Syll Simp3_26 S1 S2.
    exact S2.
  }
  assert (S3 : )

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

Theorem n10_26 (Phi Psi : Prop -> Prop) (X : Prop) : 
  ((forall z, Phi z -> Psi z) /\ Phi X) -> Psi X.
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
  (forall x, Phi x -> Psi x) -> (forall x, (Phi x /\ Chi x) -> (Psi x /\ Chi x)).
Proof.
Admitted.

Theorem n10_311 (Phi Psi Chi : Prop -> Prop) :
  (forall x, Phi x <-> Psi x) -> (forall x, (Phi x /\ Chi x) <-> (Psi x /\ Chi x)).
Proof.
Admitted.

Theorem n10_32 (Phi Psi : Prop -> Prop) :
  ((Phi x) <[- x -]> (Psi x)) <-> ((Psi x) <[- x -]> (Phi x)).
Proof.
Admitted.

Theorem n10_321 (Phi Psi Chi : Prop -> Prop) :
  ((Phi x) <[- x -]> (Psi x) /\ ((Phi x) <[- x -]> (Chi x))) 
  -> ((Psi x) <[- x -]> (Chi x)).
Proof.
Admitted.

Theorem n10_322 (Phi Psi Chi : Prop -> Prop) :
  ((Psi x) <[- x -]> (Phi x) /\ ((Chi x) <[- x -]> (Phi x))) 
  -> ((Psi x) <[- x -]> (Chi x)).
Proof.
Admitted.

Theorem n10_33 (Phi : Prop -> Prop) (P : Prop) :
  (forall x, Phi x /\ P) <-> ((forall x, Phi x) /\ P).
Proof.
Admitted.

Theorem n10_34 (Phi : Prop -> Prop) (P : Prop) :
  (exists x, Phi x -> P) <-> ((forall x, Phi x) -> P).
Proof.
Admitted.

Theorem n10_35 (Phi : Prop -> Prop) (P : Prop) :
  (exists x, P /\ Phi x) <-> P /\ (exists x, Phi x).
Proof.
Admitted.

Theorem n10_36 (Phi : Prop -> Prop) (P : Prop) :
  (exists x, Phi x \/ P) <-> (exists x, Phi x) \/ P.
Proof.
Admitted.

Theorem n10_37 (Phi : Prop -> Prop) (P : Prop) :
  (exists x, P -> Phi x) <-> (P -> exists x, Phi x).
Proof.
Admitted.

(* TODO: figure out what does Hp mean in PM *)
Theorem n10_39 (Phi Psi Chi Theta : Prop -> Prop) :
  ((Phi x -[ x ]> Chi x) /\ (Psi x -[ x ]> Theta x)) 
  -> (Phi x /\ Psi x) -[ x ]> (Chi x /\ Theta x).
Proof.
Admitted.

Theorem n10_4 (Phi Psi Chi Theta : Prop -> Prop) :
  ((Phi x <[- x -]> Chi x) /\ ((Psi x <[- x -]> Theta x)))
  -> (Phi x /\ Psi x) <[- x -]> (Chi x /\ Theta x).
Proof.
Admitted.

Theorem n10_41 (Phi Psi : Prop -> Prop) :
  (forall x, Phi x) \/ (forall x, Psi x) -> (forall x, Phi x \/ Psi x).
Proof.
Admitted.

Theorem n10_411 (Phi Psi Chi Theta : Prop -> Prop) :
  ((Phi x <[- x -]> Chi x) /\ ((Psi x <[- x -]> Theta x)))
  -> (Phi x \/ Psi x) <[- x -]> (Chi x \/ Theta x).
Proof.
Admitted.

Theorem n10_412 (Phi Psi : Prop -> Prop) :
  (Phi x <[- x -]> Psi x) <-> (~ Phi x <[- x -]> ~ Psi x).
Proof.
Admitted.

Theorem n10_413 (Phi Psi Chi Theta : Prop -> Prop) :
  ((Phi x <[- x -]> Chi x) /\ ((Psi x <[- x -]> Theta x)))
  -> (Phi x -> Psi x) <[- x -]> (Chi x -> Theta x).
Proof.
Admitted.

Theorem n10_414 (Phi Psi Chi Theta : Prop -> Prop) :
  ((Phi x <[- x -]> Chi x) /\ ((Psi x <[- x -]> Theta x)))
  -> (Phi x <-> Psi x) <[- x -]> (Chi x <-> Theta x).
Proof.
Admitted.

Theorem n10_42 (Phi Psi : Prop -> Prop) :
  (exists x, Phi x) \/ (exists x, Psi x) <-> (exists x, Phi x \/ Psi x).
Proof.
Admitted.

Theorem n10_43 (Phi Psi : Prop -> Prop) (X : Prop) :
  (Phi z <[- z -]> Psi z /\ Phi X) <->
  (Phi z <[- z -]> Psi z /\ Psi X).
Proof.
Admitted.

Theorem n10_5 (Phi Psi : Prop -> Prop) :
  (exists x, Phi x /\ Psi x) -> ((exists x, Phi x) /\ (exists x, Psi x)).
Proof. 
Admitted.

Theorem n10_51 (Phi Psi : Prop -> Prop) :
  ~(exists x, Phi x /\ Psi x) <-> (Phi x -[ x ]> ~ Psi x).
Proof.
Admitted.

Theorem n10_52 (Phi : Prop -> Prop) (P : Prop) :
  (exists x, Phi x) -> ((forall x, Phi x -> P) <-> P).
Proof.
Admitted.

Theorem n10_53 (Phi Psi : Prop -> Prop) :
  ~(exists x, Phi x) -> (Phi x -[ x ]> Psi x).
Proof.
Admitted.

Theorem n10_541 (Phi Psi : Prop -> Prop) (P : Prop) :
  (Phi y -[ y ]> (P \/ Psi y)) <-> (P -> (Phi y -[ y ]> Psi y)).
Proof.
Admitted.

Theorem n10_55 (Phi Psi : Prop -> Prop) :
  ((exists x, Phi x /\ Psi x) /\ (Phi x -[ x ]> Psi x))
  <-> ((exists x, Phi x) /\ (Phi x -[ x ]> Psi x)).
Proof.
Admitted.

Theorem n10_56 (Phi Psi Chi : Prop -> Prop) :
  ((Phi x -[ x ]> Psi x) /\ (exists x, Phi x /\ Chi x))
  -> (exists x, Psi x /\ Chi x).
Proof.
Admitted.

Theorem n10_57 (Phi Psi Chi : Prop -> Prop) :
  (Phi x -[ x ]> (Psi x \/ Chi x)) -> ((Phi x -[ x ]> Psi x) \/ (exists x, Phi x /\ Chi x)).
Proof.
Admitted.
