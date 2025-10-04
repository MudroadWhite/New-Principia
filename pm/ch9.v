Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.

Definition n9_01 (Phi : Prop → Prop) :
  (¬ (∀ x : Prop, Phi x)) = (∃ x : Prop, ¬ Phi x). Admitted.

Definition n9_02 (Phi : Prop → Prop) :
  (¬ (∃ x : Prop, Phi x)) = (∀ x : Prop, ¬ Phi x). Admitted.

Definition n9_011 (Phi : Prop → Prop) : 
  (¬ (∀ x, Phi x)) = ¬ (∀ x, Phi x). Admitted.

Definition n9_021 (Phi : Prop → Prop) :
  (¬ (∃ x, Phi x)) = ¬ (∃ x, Phi x). Admitted.

Definition n9_03 (Phi : Prop → Prop) (p : Prop) :
  ((∀ x : Prop, Phi x) ∨ p) = (∀ x : Prop, Phi x ∨ p). Admitted.

Definition n9_04 (Phi : Prop → Prop) (p : Prop) :
  (p ∨ (∀ x : Prop, Phi x)) = (∀ x : Prop, p ∨ Phi x). Admitted.

Definition n9_05 (Phi : Prop → Prop) (p : Prop) :
  ((∃ x : Prop, Phi x) ∨ p) = (∃ x : Prop, Phi x ∨ p). Admitted.

Definition n9_06 (Phi : Prop → Prop) (p : Prop) : 
  (p ∨ (∃ x : Prop, Phi x)) = ∃ x : Prop, p ∨ (Phi x). Admitted.

Definition n9_07 (Phi Psi : Prop → Prop) : 
  ((∀ x : Prop, Phi x) ∨ (∃ y : Prop, Psi y))
  = ∀ x : Prop, ∃ y : Prop, Phi x ∨ Psi y. Admitted.

Definition n9_08 (Phi Psi : Prop → Prop) :
  ((∃ y, Psi y) ∨ (∀ x, Phi x)) = ∀ x, ∃ y, Psi y ∨ Phi x. Admitted.

Definition n9_1 (Phi : Prop → Prop) (X : Prop) : 
  (Phi X → ∃ z : Prop, Phi z). Admitted.

Definition n9_11 (Phi : Prop → Prop) (X Y : Prop) : 
  (Phi X ∨ Phi Y) → (∃ z : Prop, Phi z). Admitted.

(* Pp n9_12 : What is implied by a true premiss is true. *)
Definition n9_12 (X : Prop) : X. Admitted.

(* Pp n9_13 : In any assersion containing a real variable, this real variable
may be turned into an apparent variable of which all possible values are asserted
to satisfy the function in question. *)
(* This simulation seems to be very unsatisfying! Don't use without any clear 
  intention from original text *)
Definition n9_13 (Phi : Prop → Prop) (X : Prop) : Phi X = (∀ y : Prop, Phi y). Admitted.

(* TODO: 
- Formalize the idea of `is same type` 
- Identify clearly what does "significant" mean *)
Definition is_individual (x : Prop) : Prop. Admitted.
Definition is_elementary_function (F : Prop → Prop) : Prop. Admitted.
Definition is_same_type (u v : Prop) : Prop. Admitted.

Definition SameTy9_131 := is_same_type.

Definition n9_14 : ∀ (a : Prop) (Phi : Prop → Prop) (X : Prop),
  Phi X → (SameTy9_131 X a ↔ Phi a). Admitted.

(* Pp n9_15 : If for some `a` there is a proposition `Phi a`, then there is a function
  `phi x^` and vice versa. *)

Theorem n9_2 (Phi : Prop → Prop) (Y : Prop) : (∀ x : Prop, Phi x) → Phi Y.
Proof. 
  (** Step 1 **)
  pose proof (n2_1 (Phi Y)) as n2_1.
  (** Step 2 **)
  pose proof (n9_1 (fun x : Prop => ¬ Phi x ∨ Phi Y) Y) as n9_1.
  MP n2_1 n9_1.
  (** Step 3 **)
  pose proof (n9_05 (fun x : Prop => ¬ Phi x) (Phi Y)) as n9_05. cbn in n9_05.
  rewrite <- n9_05 in n9_1.
  (** Step 4 **)
  pose proof (n9_01 Phi) as n9_01.
  rewrite <- n9_01 in n9_1.
  rewrite <- Impl1_01 in n9_1. 
  apply n9_1.
Qed.

Theorem n9_21 (Phi Psi : Prop → Prop) :
  (∀ x, Phi x → Psi x) 
  → (∀ y, Phi y) 
  → ∀ z, Psi z.
Proof.
  (** Necessary tools to be used globally **)
  (* Manually set up a `↔` relation from `=` relation to utilize
  `setoid_rewrite`. This enables substitution outside of the
  `∀`s and `∃`. Can we automate this with Ltac? *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (Phi0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv 
      (P0 ∨ ∃ x : Prop, Phi0 x) (∃ x : Prop, P0 ∨ Phi0 x) 
      (n9_06 Phi0 P0))
  as n9_06a.
  set (Z := Real "z").
  (* ******** *)
  (** S1 **)
  pose proof (Id2_08 (Phi Z → Psi Z)) as S1.
  (** S2 **)
  assert (S2 : ∃ y : Prop, (Phi Z → Psi Z) → Phi y → Psi Z).
  { 
    pose proof (n9_1 (fun x => (Phi Z → Psi Z) → Phi x → Psi Z) Z) as n9_1.
    MP n9_1 S1. exact n9_1.
  }
  (** S3 **)
  assert (S3 : ∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi Z).
  { 
    pose proof (n9_1 (fun x => (∃ z0 : Prop, (Phi x → Psi x) → Phi z0 → Psi Z)) Z) as n9_1.
    MP n9_1 S2. exact n9_1.
  }
  (** S4 **)
  assert (S4 : ∀ z : Prop, ∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi z).
  {
    rewrite -> (n9_13 (fun z => 
      (∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi z)) Z) in S3.
    exact S3.
  }
  (** S5 **)
  assert (S5 : ∀ z : Prop, (∃ x : Prop, 
    (Phi x → Psi x) → (∃ y : Prop, Phi y → Psi z))).
  {
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    setoid_rewrite <- Impl1_01a in S4.
    exact S4.
  }
  assert (S6 : ((∃ x, ¬(Phi x → Psi x)) ∨ (∀ y, ∃ z, (¬ Phi z) ∨ Psi y))).
  {
    setoid_rewrite Impl1_01a in S5.
    setoid_rewrite Impl1_01a in S5 at 3.
    pose proof (n9_08 (fun z1 => (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z1)) 
        (fun x1 => ¬ (Phi x1 → Psi x1))) as n9_08.
    rewrite <- n9_08 in S5.
    exact S5.
  }
  assert (S7 : (∃ x : Prop, ¬(Phi x → Psi x)) ∨ ((∃ y : Prop, (¬ Phi y)) ∨ (∀ z : Prop, Psi z))).
  { rewrite <- n9_08 in S6. exact S6. }
  assert (S8 : (∀ x, Phi x → Psi x) → (∀ y, Phi y) → ∀ z, Psi z).
  {
    repeat rewrite <- n9_01, <- Impl1_01 in S7.
    exact S7.
  }
  exact S8.
Qed.

Theorem n9_22 (Phi Psi : Prop → Prop) :
  (∀ x, Phi x → Psi x) → (∃ x, Phi x) → (∃ x, Psi x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (P0 : Prop) (Phi0 : Prop → Prop),
    eq_to_equiv (P0 ∨ ∃ x : Prop, Phi0 x) (∃ x : Prop, P0 ∨ Phi0 x) 
    (n9_06 Phi0 P0)) as n9_06a.
  set (λ Phi0 Psi0 : (Prop → Prop), 
    eq_to_equiv 
      ((∃ y : Prop, Psi0 y) ∨ ∀ x : Prop, Phi0 x) 
      (∀ x : Prop, ∃ y : Prop, Psi0 y ∨ Phi0 x) 
      (n9_08 Phi0 Psi0)) as n9_08a.
  set (λ Phi0 Psi0 : (Prop → Prop), 
    eq_to_equiv 
      ((∀ x : Prop, Phi0 x) ∨ (∃ y : Prop, Psi0 y))
      (∀ x : Prop, ∃ y : Prop, Phi0 x ∨ Psi0 y)
      (n9_07 Phi0 Psi0)) as n9_07a.
  set (Y := Real "Y").
  (* ******** *)
  pose proof (Id2_08 (Phi Y → Psi Y)) as S1.
  assert (S2 : ∃ z, (Phi Y → Psi Y) → (Phi Y → Psi z)).
  { 
    pose proof (n9_1 (fun z => (Phi Y → Psi Y) → (Phi Y → Psi z)) Y) as n9_1.
    MP n9_1 S1. exact n9_1.
  }
  assert (S3 : ∃ x, ∃ z, (Phi x → Psi x) → (Phi Y → Psi z)).
  { 
    pose proof (n9_1 (fun x => ∃ z, (Phi x → Psi x) → (Phi Y → Psi z)) Y) as n9_1.
    MP n9_1 S2. exact n9_1.
  }
  assert (S4 : ∀ y, ∃ x, ∃ z, (Phi x → Psi x) → (Phi y → Psi z)).
  {
    rewrite -> (n9_13 (fun y => (∃ x, ∃ z, 
      (Phi x → Psi x) → (Phi y → Psi z))) Y) in S3.
    exact S3.
  }
  assert (S5 : ∀ y, ∃ x, (Phi x → Psi x) → (∃ z, (Phi y → Psi z))).
  { 
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    setoid_rewrite <- Impl1_01a in S4.
    exact S4.
  }
  assert (S6 : (∃ x, ¬ (Phi x → Psi x)) ∨ ∀ y, (∃ z, (Phi y → Psi z))).
  {
    setoid_rewrite -> Impl1_01a in S5.
    setoid_rewrite <- n9_08a in S5.
    exact S5.
  }
  assert (S7 : (∃ x, ¬ (Phi x → Psi x)) ∨ (∀ y, ¬ (Phi y)) ∨ ∃ z, Psi z).
  { 
    setoid_rewrite -> Impl1_01a in S6 at 3.
    setoid_rewrite <- n9_07a in S6.
    exact S6.
  }
  assert (S8 : (∀ x, Phi x → Psi x) → (∃ x, Phi x) → (∃ x, Psi x)).
  { 
    rewrite <- n9_01, <- Impl1_01 in S7.
    replace (∀ y : Prop, ¬ Phi y) with (¬ ¬ (∀ y : Prop, ¬ Phi y)) in S7.
    2: {
      symmetry. apply propositional_extensionality. 
      exact (n4_13 (∀ y : Prop, ¬ Phi y)).
    }
    rewrite <- n9_02, <- Impl1_01 in S7.
    replace (¬ ¬ ∃ x : Prop, Phi x) with (∃ x : Prop, Phi x) in S7.
    2: {
      apply propositional_extensionality. 
      setoid_rewrite <- n4_13.
      reflexivity.
    }
    exact S7.
  }
  exact S8.
Qed.

Theorem n9_23 (Phi : Prop → Prop) : (∀ x : Prop, Phi x) → (∀ x : Prop, Phi x).
(* Original proof uses Id, 9.13, 9.21 *)
Proof. exact (Id2_08 (∀ x : Prop, Phi x)). Qed.

Theorem n9_24 (Phi : Prop → Prop) : (∃ x : Prop, Phi x) → (∃ x : Prop, Phi x).
(* Original proof uses Id, 9.13, 9.22 *)
Proof. exact (Id2_08 (∃ x : Prop, Phi x)). Qed.

Theorem n9_25 (P : Prop) (Phi : Prop → Prop) : 
  (∀ x : Prop, P ∨ Phi x) → P ∨ (∀ x : Prop, Phi x).
Proof.
  pose proof (n9_23 (fun x => P ∨ Phi x)) as n9_23; simpl in n9_23.
  pose proof (n9_04 Phi P) as n9_04.
  rewrite <- n9_04 in n9_23 at 2.
  exact n9_23.
Qed.

Theorem n9_3 (Phi : Prop → Prop) : 
  (∀ x : Prop, Phi x) ∨ (∀ x : Prop, Phi x) → (∀ x : Prop, Phi x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  pose proof (Taut1_2 (Phi X)) as S1.
  assert (S2 : ∃ y, (Phi X ∨ Phi y) → Phi X).
  { 
    pose proof (n9_1 (fun y => (Phi X ∨ Phi y) → Phi X) X) as n9_1.
    MP n9_1 S1.
    exact n9_1. 
  }
  assert (S3 : ∀ x, ∃ y, (Phi x ∨ Phi y) → Phi x).
  {
    rewrite -> (n9_13 (fun x => ∃ y, (Phi x ∨ Phi y) → Phi x) X) in S2.
    exact S2.
  }
  assert (S4 : ∀ x, (Phi x ∨ ∀ y, Phi y) → Phi x).
  {
    setoid_rewrite -> Impl1_01a in S3.
    assert (S3_i1 : ∀ x, ¬ (Phi x ∨ ∀ y, Phi y) ∨ Phi x).
    {
      (* TODO: eliminate the intro here *)
      intro x0; pose proof (S3 x0) as S3_1.
      rewrite <- (n9_05 ((fun x y => ¬ (Phi x ∨ Phi y)) x0) (Phi x0)),
              <- (n9_01 (fun x => Phi x0 ∨ Phi x)),
              <- (n9_04 Phi (Phi x0)) in S3_1.
      exact S3_1.
    }
    setoid_rewrite <- Impl1_01a in S3_i1.
    exact S3_i1.
  }
  assert (S5 : (∀ x, (Phi x ∨ ∀ y, Phi y)) → (∀ x, Phi x)).
  (* Here the real variable `X` can be arbitrary *)
  { 
    pose proof (n9_21 (fun x => Phi x ∨ (∀ y : Prop, Phi y)) Phi) as n9_21.
    MP n9_21 S4. exact n9_21. 
  }
  assert (S6 : (∀ x : Prop, Phi x) ∨ (∀ x : Prop, Phi x) → (∀ x : Prop, Phi x)).
  { rewrite <- n9_03 in S5. exact S5. }
  exact S6.
Qed.

Theorem n9_31 (Phi : Prop → Prop) : 
  ((∃ x : Prop, Phi x) ∨ (∃ x : Prop, Phi x)) → (∃ x : Prop, Phi x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "X").
  (* ******** *)
  assert (S1 : ∀ y, Phi X ∨ Phi y → ∃ z, Phi z).
  {
    pose proof (n9_11 Phi X X) as n9_11. 
    pose proof (n9_13 (fun y => (Phi X ∨ Phi y) → ∃ z : Prop, Phi z) X) as n9_13.
    replace (Phi X ∨ Phi X → ∃ z, Phi z) 
      with (∀ y , Phi X ∨ Phi y → ∃ z, Phi z) in n9_11.
    exact n9_11.
  }
  assert (S2 : (∃ y, Phi X ∨ Phi y) → (∃ z, Phi z)).
  {
    replace (∀ y, Phi X ∨ Phi y → ∃ z : Prop, Phi z)
      with (∀ y, (¬ (Phi X ∨ Phi y) ∨ ∃ z : Prop, Phi z)) in S1.
    2: {
      apply propositional_extensionality.
      setoid_rewrite <- Impl1_01a. reflexivity.
    }
    rewrite <- n9_03, <- n9_02, <- Impl1_01 in S1.
    exact S1.
  }
  assert (S3 : ∀ x, (∃ y, Phi x ∨ Phi y) → ∃ z, Phi z).
  {
    rewrite -> (n9_13 (fun x => (∃ y, Phi x ∨ Phi y) → ∃ z, Phi z) X) in S2.
    exact S2.
  }
  assert (S4 : (∃ x, (∃ y, Phi x ∨ Phi y)) → (∃ z, Phi z)).
  {
    replace (∀ x, (∃ y, Phi x ∨ Phi y) → ∃ z, Phi z)
      with (∀ x, ¬ (∃ y, Phi x ∨ Phi y) ∨ ∃ z, Phi z) in S3.
    2: {
      apply propositional_extensionality.
      setoid_rewrite <- Impl1_01a. reflexivity.
    }
    rewrite <- n9_03, <- n9_02, <- Impl1_01 in S3.
    exact S3.
  }
  assert (S5 : ((∃ x : Prop, Phi x) ∨ (∃ y : Prop, Phi y)) → (∃ x : Prop, Phi x)).
  {
  (* This way is so weird *)
    replace (∃ x, ∃ y, Phi x ∨ Phi y) with ((∃ x, Phi x) ∨ (∃ y, Phi y))
    in S4.
    2: {
      replace (∃ x y : Prop, Phi x ∨ Phi y) with ((∃ x y : Prop, Phi y ∨ Phi x)).
      2: {
        (* We should actually use Perm1_4 here. Simplified for laziness *)
        apply propositional_extensionality.
        setoid_rewrite <- or_comm at 1.
        reflexivity.
      }
      set (λ (Phi0 : Prop → Prop) (P0 : Prop), 
        eq_to_equiv ((∃ x : Prop, Phi0 x) ∨ P0) (∃ x : Prop, Phi0 x ∨ P0) 
                    (n9_05 Phi0 P0))
      as n9_05a.
      apply propositional_extensionality.
      setoid_rewrite <- n9_05a.
      rewrite -> n9_06.
      reflexivity.
    }
    exact S4.
  }
  exact S5.
Qed.

Theorem n9_32 (Phi : Prop → Prop) (Q : Prop) : Q → (∀ x : Prop, Phi x) ∨ Q.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  pose proof (Add1_3 (Phi X) Q) as S1.
  assert (S2 : ∀ x, Q → (Phi x) ∨ Q).
  {
    pose proof (n9_13 (fun x => Q → (Phi x) ∨ Q) X) as n9_13.
    replace (Q → Phi X ∨ Q) with (∀ x, Q → (Phi x) ∨ Q) in S1.
    exact S1.
  }
  assert (S3 : Q → ∀ x, Phi x ∨ Q).
  { 
    pose proof (n9_25 (¬ Q) (fun x => Phi x ∨ Q)) as n9_25.
    replace (∀ x : Prop, Q → Phi x ∨ Q) with (∀ x : Prop, ¬ Q ∨ (Phi x ∨ Q))
      in S2.
    2: { apply propositional_extensionality; setoid_rewrite <- Impl1_01a; reflexivity. }
    MP n9_25 S2.
    rewrite <- Impl1_01 in n9_25.
    exact n9_25.
  }
  assert (S4 : Q → (∀ x : Prop, Phi x) ∨ Q).
  { 
    intro Q0. pose proof (S3 Q0) as S3_1.
    rewrite <- (n9_03 Phi Q) in S3_1.
    exact S3_1.
  }
  exact S4.
Qed.
  
Theorem n9_33 (Phi : Prop → Prop) (Q : Prop) : Q → (∃ x : Prop, Phi x) ∨ Q.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_34 (Phi : Prop → Prop) (P : Prop) : 
  (∀ x : Prop, Phi x) → P ∨ (∀ x : Prop, Phi x).
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Add1_3 P (Phi X)) as S1.
  assert (S2 : ∀ x, Phi x → P ∨ Phi x).
  { 
    pose proof (n9_13 (fun x => Phi x → P ∨ Phi x) X).
    replace (Phi X → P ∨ Phi X) with (∀ x, Phi x → P ∨ Phi x) in S1.
    exact S1.
  }
  assert (S3 : (∀ x, Phi x) → (∀ x, P ∨ Phi x)).
  { 
    pose proof (n9_21 Phi (fun x => P ∨ Phi x)) as n9_21.
    MP n9_21 S2.
    exact n9_21.
  }
  assert (S4 : (∀ x : Prop, Phi x) → P ∨ (∀ x : Prop, Phi x)).
  { rewrite <- (n9_04 Phi P) in S3. exact S3. }
  exact S4.
Qed.

Theorem n9_35 (Phi : Prop → Prop) (P : Prop) : (∃ x : Prop, Phi x) → P ∨ (∃ x : Prop, Phi x).
Proof.
  (* Proof as above *)
Admitted.

Theorem n9_36 (Phi : Prop → Prop) (P : Prop) : P ∨ (∀ x : Prop, Phi x) → (∀ x : Prop, Phi x) ∨ P.
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Perm1_4 P (Phi X)) as S1.
  assert (S2 : (∀ x, (P ∨ Phi x)) → ∀ x, (Phi x ∨ P)).
  { 
    rewrite -> (n9_13 (fun x => P ∨ Phi x → Phi x ∨ P) X) in S1.
    pose proof (n9_21 (fun x => P ∨ Phi x) (fun x => Phi x ∨ P)) as n9_21.
    MP n9_21 S1.
    exact n9_21.
  }
  assert (S3 : P ∨ (∀ x : Prop, Phi x) → (∀ x : Prop, Phi x) ∨ P).
  { rewrite <- (n9_04 Phi P), <- (n9_03 Phi P) in S2. exact S2. }
  exact S3.
Qed.

Theorem n9_361 : ∀ (Phi : Prop → Prop) (P : Prop), (∀ x : Prop, Phi x) ∨ P → P ∨ (∀ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_37 : ∀ (Phi : Prop → Prop) (P : Prop), P ∨ (∃ x : Prop, Phi x) → (∃ x : Prop, Phi x) ∨ P.
Proof.
  (* Proof as above *)
Admitted.

Theorem n9_371 : ∀ (Phi : Prop → Prop) (P : Prop), (∃ x : Prop, Phi x) ∨ P → P ∨ (∃ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_4 (Phi : Prop → Prop) (P Q : Prop) : P ∨ Q ∨ (∀ x : Prop, Phi x)
  → Q ∨ P ∨ (∀ x : Prop, Phi x).
Proof. 
  assert (S1 : (∀ x, P ∨ (Q ∨ Phi x)) → (∀ x, Q ∨ (P ∨ Phi x))).
  {
    pose proof (fun x => (Assoc1_5 P Q (Phi x))) as Assoc1_5.
    pose proof (n9_21 (fun x => P ∨ Q ∨ Phi x) (fun x => Q ∨ P ∨ Phi x)) as n9_21.
    MP n9_21 Assoc1_5.
    exact n9_21.
  }
  assert (S2 : P ∨ Q ∨ (∀ x : Prop, Phi x) → Q ∨ P ∨ (∀ x : Prop, Phi x)).
  { 
    replace (∀ x : Prop, P ∨ Q ∨ Phi x) with (∀ x : Prop, (P ∨ Q) ∨ Phi x) in S1.
    2: {
      apply propositional_extensionality; split;
      intros H x; pose proof (H x) as H0; [ apply n2_32 | apply n2_31 ]; exact H0.
    }
    replace (∀ x : Prop, Q ∨ P ∨ Phi x) with (∀ x : Prop, (Q ∨ P) ∨ Phi x) in S1.
    2: {
      apply propositional_extensionality; split;
      intros H x; pose proof (H x) as H0; [ apply n2_32 | apply n2_31 ]; exact H0.
    }
    rewrite <- (n9_04 Phi (P ∨ Q)), <- (n9_04 Phi (Q ∨ P)) in S1.
    replace ((P ∨ Q) ∨ (∀ x : Prop, Phi x)) with (P ∨ Q ∨ ∀ x : Prop, Phi x) in S1
      by (apply propositional_extensionality; split; [ apply n2_31 | apply n2_32 ]; exact H0 ).
    replace ((Q ∨ P) ∨ ∀ x : Prop, Phi x) with (Q ∨ P ∨ ∀ x : Prop, Phi x) in S1
      by (apply propositional_extensionality; split; [ apply n2_31 | apply n2_32 ]; exact H0).
    exact S1.
  }
  exact S2.
Qed.

Theorem n9_401 (Phi : Prop → Prop) (P Q : Prop) : P ∨ Q ∨ (∃ x : Prop, Phi x)
  → Q ∨ P ∨ (∃ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_41 (Phi : Prop → Prop) (P R : Prop) : P ∨ (∀ x : Prop, Phi x) ∨ R
  → (∀ x : Prop, Phi x) ∨ P ∨ R.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_411 (Phi : Prop → Prop) (P R : Prop) : P ∨ (∃ x : Prop, Phi x) ∨ R
  → (∃ x : Prop, Phi x) ∨ P ∨ R.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_42 (Phi : Prop → Prop) (Q R : Prop) : (∀ x : Prop, Phi x) ∨ Q ∨ R
  → Q ∨ (∀ x : Prop, Phi x) ∨ R.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_421 (Phi : Prop → Prop) (Q R : Prop) : (∃ x : Prop, Phi x) ∨ Q ∨ R
  → Q ∨ (∃ x : Prop, Phi x) ∨ R.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_5 (Phi : Prop → Prop) (P Q : Prop) (Y : Prop) : 
  (P → Q) → ((P ∨ ∀ x : Prop, Phi x) → (Q ∨ ∀ x : Prop, Phi x)).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : (P → Q) → ((P ∨ Phi Y) → (Q ∨ Phi Y))).
  { 
    (* *9.21 ignored *)
    pose proof (Sum1_6 (Phi Y) P Q) as Sum1_6.
    replace (Phi Y ∨ P) with (P ∨ Phi Y) in Sum1_6
      by (apply propositional_extensionality; split; apply Perm1_4).
    replace (Phi Y ∨ Q) with (Q ∨ Phi Y) in Sum1_6 
      by (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (P → Q) → ∃ x, (P ∨ Phi x) → (Q ∨ Phi Y)).
  { 
    replace (P ∨ Phi Y → Q ∨ Phi Y) with (∃ x, P ∨ Phi x → Q ∨ Phi Y) in S1.
    2: {
      pose proof (n9_1 (fun x => P ∨ Phi x → Q ∨ Phi Y) Y) as n9_1; simpl in n9_1.
      apply propositional_extensionality.
      split.
      (* I don't think this can be proven *)
      { admit. }
      { exact n9_1. }
    }
    exact S1.
  }
  assert (S3 : (P → Q) → ∀ y, ∃ x, (P ∨ Phi x) → (Q ∨ Phi y)).
  { 
    pose proof (n9_13 (fun y => ∃ x : Prop, P ∨ Phi x → Q ∨ Phi y) Y) as n9_13.
    (* *9.04 ignored - optional *)
    rewrite -> n9_13 in S2.
    exact S2.
  }
  assert (S4 : (P → Q) → (∃ x, ¬ (P ∨ Phi x)) ∨ (∀ y, Q ∨ Phi y)).
  { 
    replace (∀ y : Prop, ∃ x : Prop, P ∨ Phi x → Q ∨ Phi y)
      with (∀ y : Prop, ∃ x : Prop, ¬(P ∨ Phi x) ∨ Q ∨ Phi y) in S3
      by (apply propositional_extensionality; setoid_rewrite <- Impl1_01a; reflexivity).
    rewrite <- (n9_08 (fun y => Q ∨ Phi y) (fun x => ¬(P ∨ Phi x))) in S3.
    exact S3.
  }
  assert (S5 : (P → Q) → (∀ x, (P ∨ Phi x)) → (∀ y, Q ∨ Phi y)).
  { rewrite <- n9_01, <- Impl1_01 in S4. exact S4. }
  assert (S6 : (P → Q) → ((P ∨ ∀ x : Prop, Phi x) → (Q ∨ ∀ x : Prop, Phi x))).
  { rewrite <- (n9_04 Phi P), <- (n9_04 Phi Q) in S5. exact S5. }
  exact S6.
Admitted.

Theorem n9_501 (Phi : Prop → Prop) (P Q : Prop) : (P → Q) 
  → (P ∨ ∃ x : Prop, Phi x) → (Q ∨ ∃ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_51 (Phi : Prop → Prop) (P R : Prop) : 
  (P → ∀ x : Prop, Phi x) → P ∨ R → (∀ x : Prop, Phi x) ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (P → Phi X) → ((P ∨ R) → (Phi X ∨ R))).
  { 
    pose proof (Sum1_6 R P (Phi X)) as Sum1_6.
    replace (R ∨ P) with (P ∨ R) in Sum1_6
      by (apply propositional_extensionality; split; apply Perm1_4).
    replace (R ∨ Phi X) with (Phi X ∨ R) in Sum1_6
      by (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (∀ x, P → Phi x) → (∀ x, (P ∨ R) → (Phi x ∨ R))).
  { 
    pose proof (n9_13 (fun x => P → Phi x) X) as n9_13a.
    replace (P → Phi X) with (∀ x, P → Phi x) in S1.
    pose proof (n9_13 (fun x => (P ∨ R) → (Phi x ∨ R)) X) as n9_13b.
    replace ((P ∨ R) → (Phi X ∨ R)) with (∀ x, (P ∨ R) → (Phi x ∨ R)) in S1.
    exact S1.
  }
  assert (S3 : (P → ∀ x : Prop, Phi x) → P ∨ R → (∀ x : Prop, Phi x) ∨ R).
  { 
    setoid_rewrite -> Impl1_01a in S2 at 2.
    rewrite <- (n9_04 Phi (¬P)) in S2.
    setoid_rewrite <- Impl1_01a in S2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    replace (∀ x : Prop, ¬ (P ∨ R) ∨ Phi x ∨ R) 
      with (∀ x : Prop, (Phi x ∨ R) ∨ (¬ (P ∨ R))) in S2.
    2: { 
      apply propositional_extensionality; split; 
      intros H x; apply Perm1_4; exact (H x).
    }
    rewrite <- (n9_03 (fun x => Phi x ∨ R) (¬ (P ∨ R))) in S2.
    replace ((∀ x : Prop, Phi x ∨ R) ∨ ¬ (P ∨ R))
      with (¬ (P ∨ R) ∨ (∀ x : Prop, Phi x ∨ R)) in S2
      by (apply propositional_extensionality; split; apply Perm1_4).
    setoid_rewrite <- Impl1_01a in S2.
    rewrite <- (n9_03 Phi R) in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n9_511 (Phi : Prop → Prop) (P R : Prop) : (P → ∃ x : Prop, Phi x) 
  → P ∨ R → (∃ x : Prop, Phi x) ∨ R.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_52 (Phi : Prop → Prop) (Q R : Prop) :
  ((∀ x : Prop, Phi x) → Q) → ((∀ x : Prop, Phi x) ∨ R) → (Q ∨ R).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (Phi X → Q) → ((Phi X ∨ R) → (Q ∨ R))).
  { 
    pose proof (Sum1_6 R (Phi X) Q) as Sum1_6.
    replace (R ∨ Q) with (Q ∨ R) in Sum1_6
      by (apply propositional_extensionality; split; apply Perm1_4).
    replace (R ∨ Phi X) with (Phi X ∨ R) in Sum1_6
      by (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (∃ x, (Phi x → Q)) → (∃ x, (Phi x ∨ R) → (Q ∨ R))).
  { 
    rewrite -> (n9_13 (fun x => (Phi x → Q) → ((Phi x ∨ R) → (Q ∨ R))) X) in S1.
    pose proof (n9_22 (fun x => Phi x → Q) (fun x => Phi x ∨ R → Q ∨ R)) as n9_22.
    MP n9_22 S1.
    exact n9_22.
  }
  assert (S3 : ((∀ x, Phi x) → Q) → (∀ x, Phi x ∨ R) → (Q ∨ R)).
  { 
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    repeat rewrite <- n9_05, <- n9_01, <- Impl1_01 in S2.
    exact S2.
  }
  assert (S4 : ((∀ x, Phi x) → Q) → ((∀ x, Phi x) ∨ R) → (Q ∨ R)).
  { rewrite <- n9_03 in S3. exact S3. }
  exact S4.
Qed.

Theorem n9_521 (Phi : Prop → Prop) (Q R : Prop) :
  ((∃ x : Prop, Phi x) → Q) → (∃ x : Prop, Phi x) ∨ R → Q ∨ R.
Proof. 
  (* Proof as above *)
Admitted.

(* Thm 9.6: `∀ x, Phi x`, `¬(∀ x, Phi x)`, `∃ x, Phi x`, `¬(∃ x, Phi x)` are of the same type. From *9.131, (7) and (8)  *)

(* Thm 9.61: If `Phi x^` and `Psi x^` are elementary functions of the same type, there is a function `Phi x^ ∨ Psi x^`. *)

(* Thm 9.62 : If `Phi(x^, y^)` and `Psi z^` are elementary functions, and the x-argument to `Phi` is of the same type as the argument of `Psi`, there are functions `(∀ y, Phi(x^, y)) ∨ Psi x^`, `(∃ y, Phi (x^, y) ∨ Phi x^)` *)

(* Thm 9.63 : If `Phi(x^, y^)` and `Psi(x^, y^)` are elementary functions of the same type, there are functions `(∀ y, Phi(x^, y) ∨ ∀ z, Psi(x^, z)), etc.` *)
