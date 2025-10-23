Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch9.
Require Import PM.pm.ch10.

(* TODO: 
Type of theorems allowed: 
Type of parameters allowed: 
*)

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

Definition n11_01 (Phi : Prop → Prop → Prop) : 
  (∀ x y, (Phi x y)) = (∀ x, ∀ y, Phi x y).
Admitted.

Definition n11_02 (Phi : Prop → Prop → Prop → Prop) :
  (∀ x y z, Phi x y z) 
  = (∀ x, ∀ y, ∀ z, Phi x y z).
Admitted.

Definition n11_03 (Phi : Prop → Prop → Prop) :
  (∃ x y, Phi x y) = (∃ x, ∃ y, Phi x y).
Admitted.

Definition n11_04 (Phi : Prop → Prop → Prop → Prop) :
  (∃ x y z, Phi x y z) = (∃ x, ∃ y, ∃ z, Phi x y z).
Admitted.

Definition n11_05 (Phi Psi : Prop → Prop → Prop) :
  (Phi x y -[ x y ]> Psi x y) = (∀ x y, Phi x y → Psi x y).
Admitted.

Definition n11_06 (Phi Psi : Prop → Prop → Prop) :
  (Phi x y <[- x y -]> Psi x y) = (∀ x y, (Phi x y ↔ Psi x y)).
Admitted.

(* Pp *11.07: "Whatever possible argument `x` may be, `Phi(x, y)` is true 
whatever possible argument `y` may be" implies that the corresponding 
statement with `x` and `y` interchanged except in "Phi(x, y)". *)
Definition n11_07 (Phi : Prop → Prop → Prop) :
  (∀ x y, Phi x y) → (∀ y x, Phi x y).
Admitted.

Theorem n11_1 (Z W : Prop) (Phi : Prop → Prop → Prop) : 
  (∀ x y, Phi x y) → Phi Z W.
Proof.
  assert (S1 : (∀ x y, Phi x y) -> forall y, (Phi Z y)).
  { exact (n10_1 (fun x => forall y, Phi x y) Z). }
  assert (S2 : (∀ x y, Phi x y) → Phi Z W).
  { 
    pose proof (n10_1 (fun y => Phi Z y) W) as n10_1.
    now Syll S1 n10_1 S2.
  }
  exact S2.
Qed.

(* Thm *11.11 : If `Phi(z, w)` is true whatever possible arguments `z` and `w` 
  may be, then `forall x y, Phi x y` is true. *)
Theorem n11_11 (Z W : Prop) (Phi : Prop → Prop → Prop) : 
  (Phi Z W) → (forall x y, Phi x y).
Admitted.

Theorem n11_12 (P : Prop) (Phi : Prop → Prop → Prop) : 
  (∀ x y, P ∨ Phi x y) → (P ∨ ∀ x y, Phi x y).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  Close Scope double_app_impl.
  Close Scope double_app_equiv.

  assert (S1 : (forall y, P \/ Phi X y) -> (P \/ forall y, Phi X y)).
  { apply n10_12. }
  assert (S2 : (forall x y, P \/ Phi x y) -> (forall x, P \/ (forall y, Phi x y))).
  {
    pose proof (n10_11 X (fun x =>
      (forall y, P \/ Phi x y) -> (P \/ forall y, Phi x y))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27 (fun x => (forall y, P \/ Phi x y))
      (fun x => (P \/ forall y, Phi x y))) as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S3 : (∀ x y, P ∨ Phi x y) → (P ∨ ∀ x y, Phi x y)).
  {
    pose proof (n10_12 (fun x => ∀ y : Prop, Phi x y) P) as n10_12.
    now Syll n10_12 S2 S3.
  }
  exact S3.
Qed.

(* Similar to *10.13 *)
(* Thm *11.13 : If `Phi x^ y^`, `Psi x^ y^  take their first and second arguments respectively of the same type, and we have `|-Phi(x, y)` and `|-Psi(x, y)`, we shall have `|-Phi(x, y) /\ Psi(x, y)`. *)

(* An alternative version of *11.13, but can only be used during formal 
  inference. Similar to *10.14 *)
Theorem n11_14 (Z W : Prop) (Phi Psi : Prop → Prop → Prop) : 
  ((∀ x y, Phi x y) ∧ (∀ x y, Psi x y))
  → (Phi Z W ∧ Psi Z W).
Proof.
  assert (S1 : ((∀ x y, Phi x y) ∧ (∀ x y, Psi x y)) 
    -> ((forall y, Phi Z y) /\ (forall y, Psi Z y))).
  {
    exact (n10_14 (fun x => forall y, Phi x y) 
      (fun x => forall y, Psi x y) Z).
  }
  assert (S2 : ((∀ x y, Phi x y) ∧ (∀ x y, Psi x y)) -> (Phi Z W ∧ Psi Z W)).
  {
    pose proof (n10_14 (fun y => Phi Z y) (fun y => Psi Z y) W) as n10_14.
    now Syll S1 n10_14 S2.
  }
  exact S2.
Qed.

Theorem n11_2 (Phi : Prop → Prop → Prop) : 
  (∀ x y, Phi x y) ↔ (∀ y x, Phi x y).
Proof.
  (* TOOLS *)
  (* X and Y are unnecessary, but for redability *)
  set (X := Real "x").
  set (Y := Real "y").
  set (W := Real "w").
  set (Z := Real "z").
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : (forall x y, Phi x y) -> (Phi Z W)).
  { apply n11_1. }
  assert (S2 : forall w z, (forall x y, Phi x y) -> Phi z w).
  {
    (* Here I think the order of theorems is reversed..? 
      Also why we need `z w` in reversed order? *)
    pose proof (n11_11 Z W (fun z w => (forall x y, Phi x y) -> Phi z w))
      as n11_11.
    MP n11_11 S1.
    pose proof (n11_07 (fun z w => (forall x y, Phi x y) -> Phi z w)) as n11_07.
    now MP n11_07 n11_11.
  }
  assert (S3 : (forall x y, Phi x y) -> (forall w z, Phi z w)).
  {
    pose proof (n11_12 (~forall x y, Phi x y) (fun z w => Phi w z)) as n11_12.
    setoid_rewrite <- Impl1_01a in n11_12.
    now MP n11_12 S2.
  }
  assert (S4 : (forall w z, Phi z w) -> (forall x y, Phi x y)).
  {
    assert (S4_1 : (forall w z, Phi z w) -> Phi X Y).
    { exact (n11_1 Y X (fun w z => Phi z w)). }
    assert (S4_2 : forall x y, (forall w z, Phi z w) -> Phi x y).
    {
      pose proof (n11_11 X Y (fun x y => (forall w z, Phi z w) -> Phi x y)) 
        as n11_11.
      now MP n11_11 S4_1.
    }
    pose proof (n11_12 (~ ∀ w z, Phi z w) Phi) as n11_12.
    setoid_rewrite <- Impl1_01a in n11_12.
    now MP n11_12 S4_2.
  }
  assert (S5 : (∀ x y, Phi x y) ↔ (∀ y x, Phi x y)).
  {
    clear S1 S2.
    Conj S3 S4 C1.
    now Equiv C1.
  }
  exact S5.
Qed.  

Theorem n11_21 (Phi : Prop → Prop → Prop → Prop) :
  (∀ x y z, Phi x y z) <-> (∀ y z x, Phi x y z).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  (* We can see that Rocq really doesn't make a distinction here... *)
  assert (S1 : (forall x y z, Phi x y z) <-> 
    (forall x, forall y, forall z, Phi x y z)).
  {
    (* n11_01 ignored *)
    (* It seems that here we're getting a `<->` relation directly 
    from a `=` definition, from original text.
    I'm assumning that the original routine is set up 
    (Phi X Y Z -> Phi X Y Z), instantiate by repeatly applying n11_1,
    and finally arrive at conclusion. Here, we omit the routine
    *)
    pose proof (n11_02 Phi) as n11_02.
    reflexivity.
  }
  assert (S2 : (forall x y z, Phi x y z) <-> 
    (forall y, forall x, forall z, Phi x y z)).
  {
    pose proof (n11_2 (fun x y => forall z, Phi x y z)) as n11_2.
    (* Since Rocq doesn't make a difference, we here still try to stick to 
    original routine, with all the `Syll` treatment omitted... *)
    now rewrite -> n11_2 in S1 at 2.
  }
  assert (S3 : (forall x y z, Phi x y z) <-> 
    (forall y, forall z, forall x, Phi x y z)).
  {
    pose proof (n11_2 (fun x z => Phi x Y z)) as n11_2.
    pose proof (n10_11 Y (fun y => (∀ x z : Prop, Phi x y z) ↔ ∀ z x : Prop, Phi x y z)) 
      as n10_11.
    MP n10_11 n11_2.
    pose proof (n10_271 (fun y => ∀ x z : Prop, Phi x y z)
      (fun y => (∀ z x : Prop, Phi x y z))) as n10_271.
    now MP n10_271 n10_11.
  }
  assert (S4 : (∀ x y z, Phi x y z) <-> (∀ y z x, Phi x y z)).
  {
    (* Since it only involves n11_01 and n11_02, we skip the routine *)
    exact S3.
  }
  exact S4.
Qed.

Theorem n11_22 (Phi : Prop → Prop → Prop) :
  (∃ x y, Phi x y) <-> (¬ (∀ x y, ¬ Phi x y)).
Proof.
  
Admitted.

Theorem n11_23 (Phi : Prop → Prop → Prop) :
  (∃ x y, Phi x y) <-> (∃ y x, Phi x y).
Proof.
Admitted.

Theorem n11_24 (Phi : Prop → Prop → Prop → Prop) :
  (∃ x y z, Phi x y z) <-> (∃ y x z, Phi x y z).
Proof.
Admitted.

Theorem n11_25 (Phi : Prop → Prop → Prop) :
  (¬∃ x y, Phi x y) <-> ∀ x y, ¬ Phi x y.
Proof.
Admitted.

Theorem n11_26 (Phi : Prop → Prop → Prop) :
  (∃ x, ∀ y, Phi x y) → (∀ y, ∃ x, Phi x y).
Proof.
Admitted.

(* NOTE: here the format is slightly different from original text *)
Theorem n11_27 (Phi : Prop → Prop → Prop → Prop) :
  ((∃ x y, ∃ z, Phi x y z) ↔ (∃ x, ∃ y z, Phi x y z))
  ∧
  ((∃ x, ∃ y z, Phi x y z) ↔ (∃ x y z, Phi x y z)).
Proof.
Admitted.

Theorem n11_3 (P : Prop) (Phi : Prop → Prop → Prop) :
  (P → (∀ x y, Phi x y)) ↔ (∀ x y, P → Phi x y).
Proof.
Admitted.

Theorem n11_31 (Phi Psi : Prop → Prop → Prop) :
  ((∀ x y, Phi x y) ∧ (∀ x y, Psi x y))
  ↔
  (∀ x y, Phi x y ∧ Psi x y).
Proof.
Admitted.

(* Thm *11.311: to be filled *)
Theorem n11_32 (Phi Psi : Prop → Prop → Prop) :
  (∀ x y, Phi x y → Psi x y) 
  → ((∀ x y, Phi x y) → ∀ x y, Psi x y).
Proof.
Admitted.

Theorem n11_33 (Phi Psi : Prop → Prop → Prop) :
  (∀ x y, Phi x y ↔ Psi x y) 
  → ((∀ x y, Phi x y) ↔ (∀ x y, Psi x y)).
Proof.
Admitted.

Theorem n11_34 (Phi Psi : Prop → Prop → Prop) :
  (∀ x y, Phi x y → Psi x y) 
  → ((∃ x y, Phi x y) → (∃ x y, Psi x y)).
Proof.
Admitted.

Theorem n11_341 (Phi Psi : Prop → Prop → Prop) :
  (∀ x y, Phi x y ↔ Psi x y) 
  → ((∃ x y, Phi x y) ↔ (∃ x y, Psi x y)).
Proof.
Admitted.

Theorem n11_35 (P : Prop) (Phi : Prop → Prop → Prop) :
  (∀ x y, Phi x y → P) ↔ ((∃ x y, Phi x y) → P).
Proof.
Admitted.

Theorem n11_36 (W Z : Prop) (Phi : Prop → Prop → Prop) :
  (Phi Z W) → ∃ x y, Phi x y.
Proof.
Admitted.

Theorem n11_37 (Phi Psi Chi : Prop → Prop → Prop) :
  ((∀ x y, Phi x y → Psi x y) 
  ∧ (∀ x y, Psi x y → Chi x y))
  → (∀ x y, Phi x y → Chi x y).
Proof.
Admitted.

Theorem n11_371 (Phi Psi Chi : Prop → Prop → Prop) :
  ((∀ x y, Phi x y ↔ Psi x y) 
  ∧ (∀ x y, Psi x y ↔ Chi x y))
  → (∀ x y, Phi x y ↔ Chi x y).
Proof.
Admitted.

Theorem n11_38 (Phi Psi Chi : Prop → Prop → Prop) :
  (∀ x y, Phi x y → Psi x y) →
  (∀ x y, (Phi x y ∧ Chi x y) → (Psi x y ∧ Chi x y)).
Proof.
Admitted.

Theorem n11_39 (Phi Psi Chi Theta : Prop → Prop → Prop) :
  ((∀ x y, Phi x y → Psi x y) ∧ (∀ x y, Chi x y → Theta x y))
  → ((∀ x y, Phi x y ∧ Chi x y) → (∀ x y, Psi x y ∧ Theta x y)).
Proof.
Admitted.

Theorem n11_391 (Phi Psi Chi : Prop → Prop → Prop) :
  ((∀ x y, Phi x y → Psi x y) ∧ (∀ x y, Phi x y → Chi x y))
  ↔ (∀ x y, Phi x y ↔ (Psi x y ∧ Chi x y)).
Proof.
Admitted.

Theorem n11_4 (Phi Psi Chi Theta : Prop → Prop → Prop) :
  ((∀ x y, Phi x y ↔ Psi x y) ∧ (∀ x y, Chi x y ↔ Theta x y))
  → (∀ x y, (Phi x y ∧ Chi x y) ↔ (Psi x y ∧ Theta x y)).
Proof.
Admitted.

Theorem n11_401 (Phi Psi Chi : Prop → Prop → Prop) :
  (∀ x y, Phi x y ↔ Psi x y) 
  → (∀ x y, (Phi x y ∧ Chi x y) ↔ (Psi x y ∧ Chi x y)).
Proof.
Admitted.

Theorem n11_41 (Phi Psi : Prop → Prop → Prop) :
  ((∃ x y, Phi x y) ∨ (∃ x y, Psi x y))
  ↔ (∃ x y, Phi x y ∨ Psi x y).
Proof.
Admitted.

Theorem n11_42 (Phi Psi : Prop → Prop → Prop) :
  (∃ x y, Phi x y ∧ Psi x y) 
  → ((∃ x y, Phi x y) ∧ (∃ x y, Psi x y)).
Proof.
Admitted.

Theorem n11_421 (Phi Psi : Prop → Prop → Prop) :
  ((∀ x y, Phi x y) ∨ (∀ x y, Psi x y))
  → (∀ x y, Phi x y ∨ Psi x y).
Proof.
Admitted.

Theorem n11_43 (P : Prop) (Phi : Prop → Prop → Prop) :
  (∃ x y, Phi x y → P) ↔ ((∀ x y, Phi x y) → P).
Proof.
Admitted.

Theorem n11_44 (P : Prop) (Phi : Prop → Prop → Prop) :
  (∀ x y, Phi x y ∨ P) ↔ ((∀ x y, Phi x y) ∨ P).
Proof.
Admitted.

Theorem n11_45 (P : Prop) (Phi : Prop → Prop → Prop) :
  (∃ x y, P ∧ Phi x y) ↔ (P ∧ ∃ x y, Phi x y).
Proof.
Admitted.

Theorem n11_46 (P : Prop) (Phi : Prop → Prop → Prop) :
  (∃ x y, P → Phi x y) ↔ (P → ∃ x y, Phi x y).
Proof.
Admitted.

Theorem n11_47 (P : Prop) (Phi : Prop → Prop → Prop) :
  (∀ x y, P ∧ Phi x y) ↔ (P ∧ ∀ x y, Phi x y).
Proof.
Admitted.

(* different format from original proof *)
Theorem n11_5 (Phi : Prop → Prop → Prop) :
  ((∃ x, ¬∀ y, Phi x y) ↔ ¬(∀ x y, Phi x y))
  ∧
  (¬(∀ x y, Phi x y) ↔ (∃ x y, ¬Phi x y)).
Proof.
Admitted.

Theorem n11_51 (Phi : Prop → Prop → Prop) :
  (∃ x, ∀ y, Phi x y) ↔ (¬(∀ x, ∃ y, ¬ Phi x y)).
Proof.
Admitted.

Theorem n11_52 (Phi Psi : Prop → Prop → Prop) :
  (∃ x y, Phi x y ∧ Psi x y) ↔
  (¬ ∀ x y, Phi x y → ¬ Psi x y).
Proof.
Admitted.

Theorem n11_521 (Phi Psi : Prop → Prop → Prop) :
  (¬ ∃ x y, Phi x y ∧ (¬ Psi x y))
  ↔ (¬ ∀ x y, Phi x y → ¬ Psi x y).
Proof.
Admitted.

Theorem n11_53 (Phi Psi : Prop → Prop) :
  (∀ x y, Phi x → Psi y) ↔ ((∃ x, Phi x) → ∀ y, Psi y).
Proof.
Admitted.

Theorem n11_54 (Phi Psi : Prop → Prop) :
  (∃ x y, Phi x ∧ Psi y) 
  ↔ ((∃ x, Phi x) ∧ (∃ y, Psi y)).
Proof.
Admitted.

Theorem n11_55 (Phi : Prop → Prop) (Psi : Prop → Prop → Prop) :
  (∃ x y, Phi x ∧ Psi x y) 
  ↔ (∃ x, Phi x ∧ (∃ y, Psi x y)).
Proof.
Admitted.

Theorem n11_56 (Phi Psi : Prop → Prop) :
  ((∀ x, Phi x) ∧ (∀ y, Psi y)) ↔ (∀ x y, Phi x ∧ Psi y).
Proof.
Admitted.

Theorem n11_57 (Phi : Prop → Prop) :
  (∀ x, Phi x) ↔ (∀ x y, Phi x ∧ Phi y).
Proof.
Admitted.

Theorem n11_58 (Phi : Prop → Prop) :
  (∃ x, Phi x) ↔ (∃ x y, Phi x ∧ Phi y).
Proof.
Admitted.

(* TODO: merge this notation into arbitrary parameter version *)
Open Scope single_app_impl.

Theorem n11_59 (Phi Psi : Prop → Prop) :
  (Phi x -[x]> Psi x) ↔ ((Phi x ∧ Phi y) -[x y]> (Psi x ∧ Psi y)).
Proof.
Admitted.

Theorem n11_6 (Phi : Prop → Prop → Prop) (Psi Chi : Prop → Prop) :
  (∃ x, (∃ y, Phi x y ∧ Psi y) ∧ Chi x) 
  ↔ (∃ y, (∃ x, Phi x y ∧ Chi x) ∧ Psi y).
Proof.
Admitted.

Theorem n11_61 (Phi : Prop → Prop) (Psi : Prop → Prop → Prop) :
  (∃ y, (Phi x -[x]> Psi x y)) → (Phi x -[x]> ∃ y, Psi x y).
Proof.
Admitted.

Theorem n11_62 (Phi : Prop → Prop) (Psi Chi : Prop → Prop → Prop) :
  ((Phi x ∧ Psi x y) -[x y]> Chi x y) ↔ (Phi x -[x]> (Psi x y -[y]> Chi x y)).
Proof.
Admitted.

Theorem n11_63 (Phi Psi : Prop → Prop → Prop) :
  (¬∃ x y, Phi x y) → (Phi x y -[x y]> Psi x y).
Proof.
Admitted.

Theorem n11_7 (Phi : Prop → Prop → Prop) :
  (∃ x y, Phi x y ∨ Phi y x) ↔ ∃ x y, Phi x y.
Proof.
Admitted.

Theorem n11_71 (Phi Psi Chi Theta : Prop → Prop) :
  ((∃ z, Phi z) ∧ (∃ w, Chi w))
  → (((Phi z -[z]> Psi z) ∧ (Chi w -[w]> Theta w))
      ↔ ((Phi z ∧ Chi w) -[z w]> (Psi z ∧ Theta w))).
Proof.
Admitted.

Close Scope single_app_impl.
Close Scope double_app_impl.
Close Scope double_app_equiv.
