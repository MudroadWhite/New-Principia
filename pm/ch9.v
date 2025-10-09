Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.

(* 
Every propositions, variables in chapter 9 are supposed to be elementary propositions,
which doesn't contain any quantifiers. That being said, in a rigorous sense, 
`P := ∀ x, F x` shouldn't be allowed, but `P := X ∨ Y` is allowed. Currently we 
didn't pose any assertions on parameters being elementary propositions, and the proofs
can be high flawed on this restriction.

The end of the chapter proved that the definition of a function P can be extended to 
sentences involving `∀`s, and moreover, multiple param functions with `∀`s within, or 
several `∀`s being concated with some binary logic operators.

The beginning of chapter 10 said that the implications in chapter 9 are called 
"material implication"s, and the results will be extended to "formal implication"s.
*)

Definition n9_01 (φ : Prop → Prop) :
  (¬ ∀ x, φ x) = ∃ x, ¬ φ x. Admitted.

Definition n9_02 (φ : Prop → Prop) :
  (¬ ∃ x, φ x) = ∀ x, ¬ φ x. Admitted.

Definition n9_011 (φ : Prop → Prop) : 
  (¬ ∀ x, φ x) = ¬ (∀ x, φ x). Admitted.

Definition n9_021 (φ : Prop → Prop) :
  (¬ ∃ x, φ x) = ¬ (∃ x, φ x). Admitted.

Definition n9_03 (φ : Prop → Prop) (p : Prop) :
  ((∀ x, φ x) ∨ p) = (∀ x, φ x ∨ p). Admitted.

Definition n9_04 (φ : Prop → Prop) (p : Prop) :
  (p ∨ (∀ x, φ x)) = (∀ x, p ∨ φ x). Admitted.

Definition n9_05 (φ : Prop → Prop) (p : Prop) :
  ((∃ x, φ x) ∨ p) = (∃ x, φ x ∨ p). Admitted.

Definition n9_06 (φ : Prop → Prop) (p : Prop) : 
  (p ∨ (∃ x, φ x)) = ∃ x, p ∨ (φ x). Admitted.

Definition n9_07 (φ ψ : Prop → Prop) : 
  ((∀ x, φ x) ∨ (∃ y, ψ y)) = ∀ x, ∃ y, φ x ∨ ψ y. Admitted.

Definition n9_08 (φ ψ : Prop → Prop) :
  ((∃ y, ψ y) ∨ (∀ x, φ x)) = ∀ x, ∃ y, ψ y ∨ φ x. Admitted.

Definition n9_1 (φ : Prop → Prop) (X : Prop) : 
  φ X → ∃ z, φ z. Admitted.

Definition n9_11 (φ : Prop → Prop) (X Y : Prop) : 
  (φ X ∨ φ Y) → ∃ z, φ z. Admitted.

(* Pp n9_12 : What is implied by a true premiss is true. *)
Definition n9_12 (X : Prop) : X. Admitted.

(* Pp n9_13 : In any assersion containing a real variable, this real variable
may be turned into an apparent variable of which all possible values are asserted
to satisfy the function in question. *)
(* This simulation seems to be very unsatisfying! Don't use without any clear 
  intention from original text *)
Definition n9_13 (φ : Prop → Prop) (X : Prop) : 
  φ X = (∀ y , φ y). Admitted.

(* TODO: 
- Formalize the idea of `is same type` 
- Identify clearly what does "significant" mean *)
Definition is_individual (x : Prop) : Prop. Admitted.
Definition is_elementary_function (F : Prop → Prop) : Prop. Admitted.
Definition is_same_type (u v : Prop) : Prop. Admitted.

Definition SameTy9_131 := is_same_type.

Definition n9_14 : ∀ (a : Prop) (φ : Prop → Prop) (X : Prop),
  φ X → (SameTy9_131 X a ↔ φ a). Admitted.

(* Pp n9_15 : If for some `a` there is a proposition `φ a`, then there is a function
  `phi x^` and vice versa. *)

Theorem n9_2 (φ : Prop → Prop) (Y : Prop) : (∀ x , φ x) → φ Y.
Proof. 
  (** Step 1 **)
  pose proof (n2_1 (φ Y)) as n2_1.
  (** Step 2 **)
  pose proof (n9_1 (fun x => ¬ φ x ∨ φ Y) Y) as n9_1.
  MP n9_1 n2_1.
  (** Step 3 **)
  rewrite <- (n9_05 (fun x => ¬ φ x) (φ Y)) in n9_1.
  (** Step 4 **)
  rewrite <- (n9_01 φ) in n9_1.
  rewrite <- Impl1_01 in n9_1. 
  apply n9_1.
Qed.

Theorem n9_21 (φ ψ : Prop → Prop) :
  (∀ x, φ x → ψ x) → (∀ y, φ y) → ∀ z, ψ z.
Proof.
  (** Necessary tools to be used globally **)
  (* Manually set up a `↔` variant from `=` relation so that we can
  `setoid_rewrite`. This enables substitution where `∀`s and `∃` are
  involved. Can we automate this with Ltac? *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv 
      (P0 ∨ ∃ x, φ0 x) (∃ x, P0 ∨ φ0 x) 
      (n9_06 φ0 P0))
  as n9_06a.
  set (Z := Real "z").
  (* ******** *)
  (** S1 **)
  pose proof (Id2_08 (φ Z → ψ Z)) as S1.
  (** S2 **)
  assert (S2 : ∃ y, (φ Z → ψ Z) → φ y → ψ Z).
  { 
    pose proof (n9_1 (fun x => (φ Z → ψ Z) → φ x → ψ Z) Z) as n9_1.
    MP n9_1 S1. exact n9_1.
  }
  (** S3 **)
  assert (S3 : ∃ x y, (φ x → ψ x) → φ y → ψ Z).
  { 
    pose proof (n9_1 (fun x => (∃ z0, (φ x → ψ x) → φ z0 → ψ Z)) Z) as n9_1.
    MP n9_1 S2. exact n9_1.
  }
  (** S4 **)
  assert (S4 : ∀ z, ∃ x y, (φ x → ψ x) → φ y → ψ z).
  {
    rewrite -> (n9_13 (fun z => 
      (∃ x y, (φ x → ψ x) → φ y → ψ z)) Z) in S3.
    exact S3.
  }
  (** S5 **)
  assert (S5 : ∀ z, (∃ x, (φ x → ψ x) → (∃ y, φ y → ψ z))).
  {
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    setoid_rewrite <- Impl1_01a in S4.
    exact S4.
  }
  assert (S6 : ((∃ x, ¬(φ x → ψ x)) ∨ (∀ y, ∃ z, (¬ φ z) ∨ ψ y))).
  {
    setoid_rewrite Impl1_01a in S5.
    setoid_rewrite Impl1_01a in S5 at 3.
    rewrite <- (n9_08 (fun z1 => (∃ y0, (¬ φ y0) ∨ ψ z1)) 
      (fun x1 => ¬ (φ x1 → ψ x1))) in S5.
    exact S5.
  }
  assert (S7 : (∃ x, ¬(φ x → ψ x)) ∨ ((∃ y, (¬ φ y)) ∨ (∀ z, ψ z))).
  { rewrite <- n9_08 in S6. exact S6. }
  assert (S8 : (∀ x, φ x → ψ x) → (∀ y, φ y) → ∀ z, ψ z).
  {
    repeat rewrite <- n9_01, <- Impl1_01 in S7.
    exact S7.
  }
  exact S8.
Qed.

Theorem n9_22 (φ ψ : Prop → Prop) :
  (∀ x, φ x → ψ x) → (∃ x, φ x) → (∃ x, ψ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (P0 : Prop) (φ0 : Prop → Prop),
    eq_to_equiv (P0 ∨ ∃ x, φ0 x) (∃ x, P0 ∨ φ0 x) 
    (n9_06 φ0 P0)) as n9_06a.
  set (λ φ0 ψ0 : (Prop → Prop), 
    eq_to_equiv 
      ((∃ y, ψ0 y) ∨ ∀ x, φ0 x) 
      (∀ x, ∃ y, ψ0 y ∨ φ0 x) 
      (n9_08 φ0 ψ0)) as n9_08a.
  set (λ φ0 ψ0 : (Prop → Prop), 
    eq_to_equiv 
      ((∀ x, φ0 x) ∨ (∃ y, ψ0 y))
      (∀ x, ∃ y, φ0 x ∨ ψ0 y)
      (n9_07 φ0 ψ0)) as n9_07a.
  set (Y := Real "Y").
  (* ******** *)
  pose proof (Id2_08 (φ Y → ψ Y)) as S1.
  assert (S2 : ∃ z, (φ Y → ψ Y) → (φ Y → ψ z)).
  { 
    pose proof (n9_1 (fun z => (φ Y → ψ Y) → (φ Y → ψ z)) Y) as n9_1.
    MP n9_1 S1. exact n9_1.
  }
  assert (S3 : ∃ x, ∃ z, (φ x → ψ x) → (φ Y → ψ z)).
  { 
    pose proof (n9_1 (fun x => ∃ z, (φ x → ψ x) → (φ Y → ψ z)) Y) as n9_1.
    MP n9_1 S2. exact n9_1.
  }
  assert (S4 : ∀ y, ∃ x, ∃ z, (φ x → ψ x) → (φ y → ψ z)).
  {
    rewrite -> (n9_13 (fun y => (∃ x, ∃ z, 
      (φ x → ψ x) → (φ y → ψ z))) Y) in S3.
    exact S3.
  }
  assert (S5 : ∀ y, ∃ x, (φ x → ψ x) → (∃ z, (φ y → ψ z))).
  { 
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    setoid_rewrite <- Impl1_01a in S4.
    exact S4.
  }
  assert (S6 : (∃ x, ¬ (φ x → ψ x)) ∨ ∀ y, (∃ z, (φ y → ψ z))).
  {
    setoid_rewrite -> Impl1_01a in S5.
    setoid_rewrite <- n9_08a in S5.
    exact S5.
  }
  assert (S7 : (∃ x, ¬ (φ x → ψ x)) ∨ (∀ y, ¬ (φ y)) ∨ ∃ z, ψ z).
  { 
    setoid_rewrite -> Impl1_01a in S6 at 3.
    setoid_rewrite <- n9_07a in S6.
    exact S6.
  }
  assert (S8 : (∀ x, φ x → ψ x) → (∃ x, φ x) → (∃ x, ψ x)).
  { 
    rewrite <- n9_01, <- Impl1_01 in S7.
    replace (∀ y, ¬ φ y) with (¬ ¬ (∀ y, ¬ φ y)) in S7.
    2: {
      symmetry. apply propositional_extensionality. 
      exact (n4_13 (∀ y, ¬ φ y)).
    }
    rewrite <- n9_02, <- Impl1_01 in S7.
    replace (¬ ¬ ∃ x, φ x) with (∃ x, φ x) in S7.
    2: {
      apply propositional_extensionality. 
      now rewrite <- n4_13.
    }
    exact S7.
  }
  exact S8.
Qed.

Theorem n9_23 (φ : Prop → Prop) : (∀ x, φ x) → (∀ x, φ x).
(* Original proof uses Id, 9.13, 9.21 *)
Proof. exact (Id2_08 (∀ x, φ x)). Qed.

Theorem n9_24 (φ : Prop → Prop) : (∃ x, φ x) → (∃ x, φ x).
(* Original proof uses Id, 9.13, 9.22 *)
Proof. exact (Id2_08 (∃ x, φ x)). Qed.

Theorem n9_25 (P : Prop) (φ : Prop → Prop) : 
  (∀ x, P ∨ φ x) → P ∨ (∀ x, φ x).
Proof.
  pose proof (n9_23 (fun x => P ∨ φ x)) as n9_23; simpl in n9_23.
  rewrite <- (n9_04 φ P) in n9_23 at 2.
  exact n9_23.
Qed.

Theorem n9_3 (φ : Prop → Prop) : 
  (∀ x, φ x) ∨ (∀ x, φ x) → (∀ x, φ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  pose proof (Taut1_2 (φ X)) as S1.
  assert (S2 : ∃ y, (φ X ∨ φ y) → φ X).
  { 
    pose proof (n9_1 (fun y => (φ X ∨ φ y) → φ X) X) as n9_1.
    MP n9_1 S1.
    exact n9_1. 
  }
  assert (S3 : ∀ x, ∃ y, (φ x ∨ φ y) → φ x).
  {
    rewrite -> (n9_13 (fun x => ∃ y, (φ x ∨ φ y) → φ x) X) in S2.
    exact S2.
  }
  assert (S4 : ∀ x, (φ x ∨ ∀ y, φ y) → φ x).
  {
    setoid_rewrite -> Impl1_01a in S3.
    assert (S3_i1 : ∀ x, ¬ (φ x ∨ ∀ y, φ y) ∨ φ x).
    {
      (* TODO: eliminate the intro here *)
      intro x0; pose proof (S3 x0) as S3_1.
      rewrite <- (n9_05 ((fun x y => ¬ (φ x ∨ φ y)) x0) (φ x0)),
              <- (n9_01 (fun x => φ x0 ∨ φ x)),
              <- (n9_04 φ (φ x0)) in S3_1.
      exact S3_1.
    }
    setoid_rewrite <- Impl1_01a in S3_i1.
    exact S3_i1.
  }
  assert (S5 : (∀ x, (φ x ∨ ∀ y, φ y)) → (∀ x, φ x)).
  (* Here the real variable `X` can be arbitrary *)
  { 
    pose proof (n9_21 (fun x => φ x ∨ (∀ y, φ y)) φ) as n9_21.
    MP n9_21 S4. exact n9_21. 
  }
  assert (S6 : (∀ x, φ x) ∨ (∀ x, φ x) → (∀ x, φ x)).
  { rewrite <- n9_03 in S5. exact S5. }
  exact S6.
Qed.

Theorem n9_31 (φ : Prop → Prop) : ((∃ x, φ x) ∨ (∃ x, φ x)) → (∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "X").
  (* ******** *)
  assert (S1 : ∀ y, φ X ∨ φ y → ∃ z, φ z).
  {
    pose proof (n9_11 φ X X) as n9_11. 
    pose proof (n9_13 (fun y => (φ X ∨ φ y) → ∃ z, φ z) X) as n9_13.
    replace (φ X ∨ φ X → ∃ z, φ z) 
      with (∀ y , φ X ∨ φ y → ∃ z, φ z) in n9_11.
    exact n9_11.
  }
  assert (S2 : (∃ y, φ X ∨ φ y) → (∃ z, φ z)).
  {
    setoid_rewrite -> Impl1_01a in S1.
    rewrite <- n9_03, <- n9_02, <- Impl1_01 in S1.
    exact S1.
  }
  assert (S3 : ∀ x, (∃ y, φ x ∨ φ y) → ∃ z, φ z).
  {
    rewrite -> (n9_13 (fun x => (∃ y, φ x ∨ φ y) → ∃ z, φ z) X) in S2.
    exact S2.
  }
  assert (S4 : (∃ x, (∃ y, φ x ∨ φ y)) → (∃ z, φ z)).
  {
    setoid_rewrite -> Impl1_01a in S3.
    rewrite <- n9_03, <- n9_02, <- Impl1_01 in S3.
    exact S3.
  }
  assert (S5 : ((∃ x, φ x) ∨ (∃ y, φ y)) → (∃ x, φ x)).
  {
    (* n9_22?! *)
    (* Can we use Syll with Perm1_4 here? *)
    pose (fun x y => Perm1_4 (φ x) (φ y)) as f_Perm1_4.
    replace (∃ x y, φ x ∨ φ y) with ((∃ x y, φ y ∨ φ x)) in S4.
    2: {
      apply propositional_extensionality.
      now setoid_rewrite <- or_comm at 1.
    }
    replace (∃ x, ∃ y, φ y ∨ φ x) with ((∃ x, φ x) ∨ (∃ y, φ y)) in S4.
    2: {
      set (λ (φ0 : Prop → Prop) (P0 : Prop), 
        eq_to_equiv ((∃ x, φ0 x) ∨ P0) (∃ x, φ0 x ∨ P0) (n9_05 φ0 P0))
        as n9_05a.
      apply propositional_extensionality.
      setoid_rewrite <- n9_05a.
      now rewrite -> n9_06.
    }
    exact S4.
  }
  exact S5.
Qed.

Theorem n9_32 (φ : Prop → Prop) (Q : Prop) : Q → (∀ x, φ x) ∨ Q.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv ((∀ x, φ0 x) ∨ P0) (∀ x, φ0 x ∨ P0) 
          (n9_03 φ0 P0))
      as n9_03a.
  set (X := Real "x").
  (* ******** *)
  pose proof (Add1_3 (φ X) Q) as S1.
  assert (S2 : ∀ x, Q → (φ x) ∨ Q).
  {
    pose proof (n9_13 (fun x => Q → (φ x) ∨ Q) X) as n9_13.
    replace (Q → φ X ∨ Q) with (∀ x, Q → (φ x) ∨ Q) in S1.
    exact S1.
  }
  assert (S3 : Q → ∀ x, φ x ∨ Q).
  { 
    pose proof (n9_25 (¬ Q) (fun x => φ x ∨ Q)) as n9_25.
    setoid_rewrite -> Impl1_01a in S2.
    MP n9_25 S2.
    rewrite <- Impl1_01 in n9_25.
    exact n9_25.
  }
  assert (S4 : Q → (∀ x, φ x) ∨ Q).
  { 
    setoid_rewrite <- (n9_03a φ Q) in S3.
    exact S3.
  }
  exact S4.
Qed.
  
Theorem n9_33 (φ : Prop → Prop) (Q : Prop) : Q → (∃ x, φ x) ∨ Q.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv ((∀ x, φ0 x) ∨ P0) 
                (∀ x, φ0 x ∨ P0) 
    (n9_03 φ0 P0))
    as n9_03a.
  set (X := Real "x").
  (* ******** *)
  pose proof (Add1_3 (φ X) Q) as S1.
  assert (S2 : ∃ x, Q → (φ x) ∨ Q).
  {
    pose proof (n9_1 (fun x => Q → (φ x) ∨ Q) X) as n9_1.
    MP n9_1 S1.
    exact n9_1.
  }
  assert (S3 : Q → ∃ x, (φ x) ∨ Q).
  { 
    setoid_rewrite -> Impl1_01a in S2.
    rewrite <- (n9_06 (fun x => (φ x) ∨ Q) (¬ Q)) in S2.
    rewrite <- Impl1_01 in S2.
    exact S2.
  }
  assert (S4 : Q → (∃ x, (φ x)) ∨ Q).
  { rewrite <- n9_05 in S3. exact S3. }
  exact S4.
Qed.

Theorem n9_34 (φ : Prop → Prop) (P : Prop) : (∀ x, φ x) → P ∨ (∀ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Add1_3 P (φ X)) as S1.
  assert (S2 : ∀ x, φ x → P ∨ φ x).
  { 
    pose proof (n9_13 (fun x => φ x → P ∨ φ x) X).
    replace (φ X → P ∨ φ X) with (∀ x, φ x → P ∨ φ x) in S1.
    exact S1.
  }
  assert (S3 : (∀ x, φ x) → (∀ x, P ∨ φ x)).
  {
    pose proof (n9_21 φ (fun x => P ∨ φ x)) as n9_21.
    MP n9_21 S2.
    exact n9_21.
  }
  assert (S4 : (∀ x, φ x) → P ∨ (∀ x, φ x)).
  { rewrite <- (n9_04 φ P) in S3. exact S3. }
  exact S4.
Qed.

Theorem n9_35 (φ : Prop → Prop) (P : Prop) : 
  (∃ x, φ x) → P ∨ (∃ x, φ x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Add1_3 P (φ X)) as S1.
  assert (S2 : ∀ x, φ x → P ∨ φ x).
  { 
    pose proof (n9_13 (fun x => φ x → P ∨ φ x) X).
    replace (φ X → P ∨ φ X) with (∀ x, φ x → P ∨ φ x) in S1.
    exact S1.
  }
  assert (S3 : (∃ x, φ x) → (∃ x, P ∨ φ x)).
  {
    pose proof (n9_22 (fun x => φ x) (fun x => P ∨ φ x)) as n9_22.
    MP n9_22 S2.
    exact n9_22.
  }
  assert (S6 : (∃ x, φ x) → P ∨ (∃ x, φ x)).
  {
    rewrite -> Impl1_01, <- n9_06, <- Impl1_01 in S3.
    exact S3.
  }
  exact S6.
Qed.

Theorem n9_36 (φ : Prop → Prop) (P : Prop) : P ∨ (∀ x, φ x) → (∀ x, φ x) ∨ P.
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Perm1_4 P (φ X)) as S1.
  assert (S2 : (∀ x, (P ∨ φ x)) → ∀ x, (φ x ∨ P)).
  { 
    rewrite -> (n9_13 (fun x => P ∨ φ x → φ x ∨ P) X) in S1.
    pose proof (n9_21 (fun x => P ∨ φ x) (fun x => φ x ∨ P)) as n9_21.
    MP n9_21 S1.
    exact n9_21.
  }
  assert (S3 : P ∨ (∀ x, φ x) → (∀ x, φ x) ∨ P).
  { rewrite <- (n9_04 φ P), <- (n9_03 φ P) in S2. exact S2. }
  exact S3.
Qed.

Theorem n9_361 (φ : Prop → Prop) (P : Prop) : (∀ x, φ x) ∨ P → P ∨ (∀ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Perm1_4 (φ X) P) as S1.
  assert (S2 : (∀ x, φ x ∨ P) → ∀ x, P ∨ φ x).
  {
    rewrite -> (n9_13 (fun x => (φ x ∨ P) → (P ∨ φ x)) X) in S1.
    pose proof (n9_21 (fun x => φ x ∨ P) (fun x => P ∨ φ x)) as n9_21.
    MP n9_21 S1.
    exact n9_21.
  }
  assert (S3 : (∀ x, φ x) ∨ P → P ∨ (∀ x, φ x)).
  { rewrite <- n9_03, <- n9_04 in S2. exact S2. }
  exact S3.
Qed.

Theorem n9_37 (φ : Prop → Prop) (P : Prop) : P ∨ (∃ x, φ x) → (∃ x, φ x) ∨ P.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Perm1_4 P (φ X)) as S1.
  assert (S2 : (∃ x, (P ∨ φ x)) → ∃ x, (φ x ∨ P)).
  {
    rewrite -> (n9_13 (fun x => P ∨ φ x → φ x ∨ P) X) in S1.
    pose proof (n9_22 (fun x => P ∨ φ x) (fun x => φ x ∨ P)) as n9_22.
    MP n9_22 S1.
    exact n9_22.
  }
  assert (S3 : P ∨ (∃ x, φ x) → (∃ x, φ x) ∨ P).
  { rewrite <- n9_06, <- n9_05 in S2. exact S2. }
  exact S3.
Qed.

Theorem n9_371 (φ : Prop → Prop) (P : Prop) : (∃ x, φ x) ∨ P → P ∨ (∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (Perm1_4 (φ X) P) as S1.
  assert (S2 : (∃ x, φ x ∨ P) → ∃ x, P ∨ φ x).
  {
    rewrite -> (n9_13 (fun x => (φ x ∨ P) → (P ∨ φ x)) X) in S1.
    pose proof (n9_22 (fun x => φ x ∨ P) (fun x => P ∨ φ x)) as n9_22.
    MP n9_22 S1.
    exact n9_22.
  }
  assert (S3 : (∃ x, φ x) ∨ P → P ∨ (∃ x, φ x)).
  { rewrite <- n9_06, <- n9_05 in S2. exact S2. }
  exact S3.
Qed.

Theorem n9_4 (φ : Prop → Prop) (P Q : Prop) : 
  P ∨ Q ∨ (∀ x, φ x) → Q ∨ P ∨ (∀ x, φ x).
Proof. 
  assert (S1 : (∀ x, P ∨ (Q ∨ φ x)) → (∀ x, Q ∨ (P ∨ φ x))).
  {
    pose proof (fun x => (Assoc1_5 P Q (φ x))) as Assoc1_5.
    pose proof (n9_21 (fun x => P ∨ Q ∨ φ x) (fun x => Q ∨ P ∨ φ x)) as n9_21.
    MP n9_21 Assoc1_5.
    exact n9_21.
  }
  assert (S2 : P ∨ Q ∨ (∀ x, φ x) → Q ∨ P ∨ (∀ x, φ x)).
  { 
    replace (∀ x, P ∨ Q ∨ φ x) with (∀ x, (P ∨ Q) ∨ φ x) in S1.
    replace (∀ x, Q ∨ P ∨ φ x) with (∀ x, (Q ∨ P) ∨ φ x) in S1.
    2, 3: (
      apply propositional_extensionality; split;
      intros H x; pose proof (H x) as H0; [ apply n2_32 | apply n2_31 ]; exact H0
    ).
    rewrite <- (n9_04 φ (P ∨ Q)), <- (n9_04 φ (Q ∨ P)) in S1.
    (* Here is a demonstration where we use `Syll` instead of `replace`.
      In the future we might still stick to `replace` for simplicity.
      All `replace` tactics can be eventually rewritten as `Syll`s with 
      `MP`s, since`Syll` works like a binary search on the sub term and 
      performs the replacements.
      We have the `replace` alternative commented out for comparison.
    *)
    assert (Sy1 : P ∨ Q ∨ (∀ x, φ x) → Q ∨ P ∨ ∀ x, φ x).
    {
      pose proof (n2_32 Q P (∀ x, φ x)) as n2_32.
      Syll S1 n2_32 S1_1.
      clear S1 n2_32.
      pose proof (n2_31 P Q (∀ x, φ x)) as n2_31.
      Syll S1_1 n2_31 S1_2.
      exact S1_2.
    }
    (* 
    replace ((P ∨ Q) ∨ (∀ x, φ x)) with (P ∨ Q ∨ ∀ x, φ x) in S1.
    replace ((Q ∨ P) ∨ ∀ x, φ x) with (Q ∨ P ∨ ∀ x, φ x) in S1.
    2, 3: (
      apply propositional_extensionality; split; [ apply n2_31 | apply n2_32 ]; exact H0
    ). 
    *)
    exact Sy1.
  }
  exact S2.
Qed.

Theorem n9_401 (φ : Prop → Prop) (P Q : Prop) : 
  P ∨ Q ∨ (∃ x, φ x) → Q ∨ P ∨ (∃ x, φ x).
Proof. 
  assert (S1 : (∃ x, P ∨ (Q ∨ φ x)) → (∃ x, Q ∨ (P ∨ φ x))).
  {
    pose proof (fun x => (Assoc1_5 P Q (φ x))) as Assoc1_5.
    pose proof (n9_22 (fun x => P ∨ Q ∨ φ x) (fun x => Q ∨ P ∨ φ x)) as n9_22.
    MP n9_22 Assoc1_5.
    exact n9_22.
  }
  assert (S2 : P ∨ Q ∨ (∃ x, φ x) → Q ∨ P ∨ (∃ x, φ x)).
  { repeat rewrite <- n9_06 in S1. exact S1. }
  exact S2.
Qed.

Theorem n9_41 (φ : Prop → Prop) (P R : Prop) : 
  P ∨ (∀ x, φ x) ∨ R → (∀ x, φ x) ∨ P ∨ R.
Proof. 
  assert (S1 : (∀ x, P ∨ (φ x ∨ R)) → ∀ x, φ x ∨ (P ∨ R)).
  {
    pose proof (fun x => (Assoc1_5 P (φ x) R)) as Assoc1_5.
    pose proof (n9_21 (fun x => P ∨ (φ x ∨ R)) (fun x => φ x ∨ (P ∨ R))) as n9_21.
    MP n9_21 Assoc1_5.
    exact n9_21.
  }
  assert (S2 : P ∨ (∀ x, φ x) ∨ R → (∀ x, φ x) ∨ P ∨ R).
  {
    rewrite <- n9_04 in S1.
    repeat rewrite <- n9_03 in S1.
    exact S1.
  }
  exact S2.
Qed.

Theorem n9_411 (φ : Prop → Prop) (P R : Prop) : 
  P ∨ (∃ x, φ x) ∨ R → (∃ x, φ x) ∨ P ∨ R.
Proof. 
  assert (S1 : (∃ x, P ∨ (φ x ∨ R)) → ∃ x, φ x ∨ (P ∨ R)).
  {
    pose proof (fun x => (Assoc1_5 P (φ x) R)) as Assoc1_5.
    pose proof (n9_22 (fun x => P ∨ (φ x ∨ R)) (fun x => φ x ∨ (P ∨ R))) as n9_22.
    MP n9_22 Assoc1_5.
    exact n9_22.
  }
  assert (S2 : P ∨ (∃ x, φ x) ∨ R → (∃ x, φ x) ∨ P ∨ R).
  {
    rewrite <- n9_06 in S1.
    repeat rewrite <- n9_05 in S1.
    exact S1.
  }
  exact S2.
Qed.

Theorem n9_42 (φ : Prop → Prop) (Q R : Prop) : 
  (∀ x, φ x) ∨ Q ∨ R → Q ∨ (∀ x, φ x) ∨ R.
Proof. 
  assert (S1 : (∀ x, φ x ∨ (Q ∨ R)) → ∀ x, Q ∨ (φ x ∨ R)).
  {
    pose proof (fun x => (Assoc1_5 (φ x) Q R)) as Assoc1_5.
    pose proof (n9_21 (fun x => φ x ∨ (Q ∨ R)) (fun x => Q ∨ (φ x ∨ R))) as n9_21.
    MP n9_21 Assoc1_5.
    exact n9_21.
  }
  assert (S2 : (∀ x, φ x) ∨ Q ∨ R → Q ∨ (∀ x, φ x) ∨ R).
  {
    rewrite <- n9_04 in S1.
    repeat rewrite <- n9_03 in S1.
    exact S1.
  }
  exact S2.
Qed.

Theorem n9_421 (φ : Prop → Prop) (Q R : Prop) : 
  (∃ x, φ x) ∨ Q ∨ R → Q ∨ (∃ x, φ x) ∨ R.
Proof. 
  assert (S1 : (∃ x, φ x ∨ (Q ∨ R)) → ∃ x, Q ∨ (φ x ∨ R)).
  {
    pose proof (fun x => (Assoc1_5 (φ x) Q R)) as Assoc1_5.
    pose proof (n9_22 (fun x => φ x ∨ (Q ∨ R)) (fun x => Q ∨ (φ x ∨ R))) as n9_22.
    MP n9_22 Assoc1_5.
    exact n9_22.
  }
  assert (S2 : (∃ x, φ x) ∨ Q ∨ R → Q ∨ (∃ x, φ x) ∨ R).
  {
    rewrite <- n9_06 in S1.
    repeat rewrite <- n9_05 in S1.
    exact S1.
  }
  exact S2.
Qed.

Theorem n9_5 (φ : Prop → Prop) (P Q : Prop) : 
  (P → Q) → ((P ∨ ∀ x, φ x) → (Q ∨ ∀ x, φ x)).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (P → Q) → ((P ∨ φ Y) → (Q ∨ φ Y))).
  { 
    (* *9.21 ignored *)
    pose proof (Sum1_6 (φ Y) P Q) as Sum1_6.
    (* TODO: rewrite with `Syll` *)
    replace (φ Y ∨ P) with (P ∨ φ Y) in Sum1_6.
    replace (φ Y ∨ Q) with (Q ∨ φ Y) in Sum1_6.
      2, 3: (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (P → Q) → ∃ x, (P ∨ φ x) → (Q ∨ φ Y)).
  {
    pose proof (n9_1 (fun x => P ∨ φ x → Q ∨ φ Y) Y) as n9_1.
    Syll S1 n9_1 S1_1.
    exact S1_1.
  }
  assert (S3 : (P → Q) → ∀ y, ∃ x, (P ∨ φ x) → (Q ∨ φ y)).
  { 
    (* *9.04 ignored - optional *)
    rewrite -> (n9_13 (fun y => ∃ x, P ∨ φ x → Q ∨ φ y) Y) in S2.
    exact S2.
  }
  assert (S4 : (P → Q) → (∃ x, ¬ (P ∨ φ x)) ∨ (∀ y, Q ∨ φ y)).
  { 
    setoid_rewrite -> Impl1_01a in S3 at 3.
    rewrite <- (n9_08 (fun y => Q ∨ φ y) (fun x => ¬(P ∨ φ x))) in S3.
    exact S3.
  }
  assert (S5 : (P → Q) → (∀ x, (P ∨ φ x)) → (∀ y, Q ∨ φ y)).
  { rewrite <- n9_01, <- Impl1_01 in S4. exact S4. }
  assert (S6 : (P → Q) → ((P ∨ ∀ x, φ x) → (Q ∨ ∀ x, φ x))).
  { rewrite <- (n9_04 φ P), <- (n9_04 φ Q) in S5. exact S5. }
  exact S6.
Qed.

Theorem n9_501 (φ : Prop → Prop) (P Q : Prop) : 
  (P → Q) → (P ∨ ∃ x, φ x) → (Q ∨ ∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (P → Q) → ((P ∨ φ Y) → (Q ∨ φ Y))).
  { 
    (* *9.21 ignored *)
    pose proof (Sum1_6 (φ Y) P Q) as Sum1_6.
    replace (φ Y ∨ P) with (P ∨ φ Y) in Sum1_6.
    replace (φ Y ∨ Q) with (Q ∨ φ Y) in Sum1_6.
      2, 3: (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (P → Q) → ∃ y, (P ∨ φ Y) → (Q ∨ φ y)).
  {
    pose proof (n9_1 (fun y => P ∨ φ Y → Q ∨ φ y) Y) as n9_1.
    Syll S1 n9_1 S1_1.
    exact S1_1.
  }
  assert (S3 : (P → Q) → ∀ x, ∃ y, (P ∨ φ x) → (Q ∨ φ y)).
  { 
    rewrite -> (n9_13 (fun x => ∃ y, P ∨ φ x → Q ∨ φ y) Y) in S2.
    exact S2.
  }
  assert (S4 : (P → Q) → (∀ x, ¬ (P ∨ φ x)) ∨ (∃ y, Q ∨ φ y)).
  {
    setoid_rewrite -> Impl1_01a in S3 at 3.
    rewrite <- (n9_07 (fun x => ¬ (P ∨ φ x)) (fun y => Q ∨ φ y)) in S3.
    exact S3.
  }
  assert (S5 : (P → Q) → (∃ x, P ∨ φ x) → (∃ y, Q ∨ φ y)).
  { 
    replace (∀ x, ¬ (P ∨ φ x)) with (¬ ¬ ∀ x, ¬ (P ∨ φ x)) in S4
      by (apply propositional_extensionality; now rewrite <- n4_13).
    setoid_rewrite <- Impl1_01a in S4.
    rewrite <- n9_02 in S4.
    replace (¬ ¬ (∃ x, P ∨ φ x)) with (∃ x, P ∨ φ x) in S4
      by (apply propositional_extensionality; now rewrite <- n4_13).
    exact S4.
  }
  assert (S6 : (P → Q) → (P ∨ ∃ x, φ x) → (Q ∨ ∃ y, φ y)).
  { repeat rewrite <- n9_06 in S5. exact S5. }
  exact S6.
Qed.

Theorem n9_51 (φ : Prop → Prop) (P R : Prop) : 
  (P → ∀ x, φ x) → P ∨ R → (∀ x, φ x) ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (P → φ X) → ((P ∨ R) → (φ X ∨ R))).
  { 
    pose proof (Sum1_6 R P (φ X)) as Sum1_6.
    replace (R ∨ P) with (P ∨ R) in Sum1_6.
    replace (R ∨ φ X) with (φ X ∨ R) in Sum1_6.
      2, 3: (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (∀ x, P → φ x) → (∀ x, (P ∨ R) → (φ x ∨ R))).
  { 
    pose proof (n9_13 (fun x => P → φ x) X) as n9_13a.
    replace (P → φ X) with (∀ x, P → φ x) in S1.
    pose proof (n9_13 (fun x => (P ∨ R) → (φ x ∨ R)) X) as n9_13b.
    replace ((P ∨ R) → (φ X ∨ R)) with (∀ x, (P ∨ R) → (φ x ∨ R)) in S1.
    exact S1.
  }
  assert (S3 : (P → ∀ x, φ x) → P ∨ R → (∀ x, φ x) ∨ R).
  { 
    setoid_rewrite -> Impl1_01a in S2 at 2.
    rewrite <- (n9_04 φ (¬P)) in S2.
    setoid_rewrite <- Impl1_01a in S2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    replace (∀ x, ¬ (P ∨ R) ∨ φ x ∨ R) 
      with (∀ x, (φ x ∨ R) ∨ (¬ (P ∨ R))) in S2.
    2: { 
      apply propositional_extensionality; split; 
      intros H x; apply Perm1_4; exact (H x).
    }
    rewrite <- (n9_03 (fun x => φ x ∨ R) (¬ (P ∨ R))) in S2.
    replace ((∀ x, φ x ∨ R) ∨ ¬ (P ∨ R))
      with (¬ (P ∨ R) ∨ (∀ x, φ x ∨ R)) in S2
      by (apply propositional_extensionality; split; apply Perm1_4).
    setoid_rewrite <- Impl1_01a in S2.
    rewrite <- (n9_03 φ R) in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n9_511 (φ : Prop → Prop) (P R : Prop) : 
  (P → ∃ x, φ x) → P ∨ R → (∃ x, φ x) ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (P → φ X) → ((P ∨ R) → (φ X ∨ R))).
  { 
    pose proof (Sum1_6 R P (φ X)) as Sum1_6.
    replace (R ∨ P) with (P ∨ R) in Sum1_6.
    replace (R ∨ φ X) with (φ X ∨ R) in Sum1_6.
      2, 3: (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (∃ x, P → φ x) → (∃ x, (P ∨ R) → (φ x ∨ R))).
  {
    assert (Sy1 : (P → φ X) → (∃ x, (P ∨ R) → (φ x ∨ R))).
    {
      pose proof (n9_1 (fun x => P ∨ R → φ x ∨ R) X) as n9_1.
      Syll S1 n9_1 Sy1.
      exact Sy1.  
    }
    pose proof (n9_13 (fun y => (P → φ y) → (∃ x, (P ∨ R) → (φ x ∨ R))) X)
      as n9_13.
    rewrite -> n9_13 in Sy1.
    setoid_rewrite -> Impl1_01a in Sy1.
    rewrite <- n9_03, <- n9_02, <- Impl1_01 in Sy1.
    exact Sy1.
  }
  assert (S3 : (P → ∃ x, φ x) → P ∨ R → (∃ x, φ x) ∨ R).
  {
    (* We won't stick to `Syll` here... *)
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    rewrite <- n9_06 in S2.
    rewrite <- n9_06 in S2.
    rewrite <- n9_05 in S2.
    setoid_rewrite <- Impl1_01a in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n9_52 (φ : Prop → Prop) (Q R : Prop) :
  ((∀ x, φ x) → Q) → ((∀ x, φ x) ∨ R) → (Q ∨ R).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (φ X → Q) → ((φ X ∨ R) → (Q ∨ R))).
  { 
    pose proof (Sum1_6 R (φ X) Q) as Sum1_6.
    replace (R ∨ Q) with (Q ∨ R) in Sum1_6.
    replace (R ∨ φ X) with (φ X ∨ R) in Sum1_6.
      2, 3: (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (∃ x, (φ x → Q)) → (∃ x, (φ x ∨ R) → (Q ∨ R))).
  { 
    rewrite -> (n9_13 (fun x => (φ x → Q) → ((φ x ∨ R) → (Q ∨ R))) X) in S1.
    pose proof (n9_22 (fun x => φ x → Q) (fun x => φ x ∨ R → Q ∨ R)) as n9_22.
    MP n9_22 S1.
    exact n9_22.
  }
  assert (S3 : ((∀ x, φ x) → Q) → (∀ x, φ x ∨ R) → (Q ∨ R)).
  { 
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    repeat rewrite <- n9_05, <- n9_01, <- Impl1_01 in S2.
    exact S2.
  }
  assert (S4 : ((∀ x, φ x) → Q) → ((∀ x, φ x) ∨ R) → (Q ∨ R)).
  { rewrite <- n9_03 in S3. exact S3. }
  exact S4.
Qed.

Theorem n9_521 (φ : Prop → Prop) (Q R : Prop) :
  ((∃ x, φ x) → Q) → (∃ x, φ x) ∨ R → Q ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (φ X → Q) → ((φ X ∨ R) → (Q ∨ R))).
  { 
    pose proof (Sum1_6 R (φ X) Q) as Sum1_6.
    replace (R ∨ Q) with (Q ∨ R) in Sum1_6.
    replace (R ∨ φ X) with (φ X ∨ R) in Sum1_6.
      2, 3: (apply propositional_extensionality; split; apply Perm1_4).
    exact Sum1_6.
  }
  assert (S2 : (∀ x, (φ x → Q)) → (∀ x, (φ x ∨ R) → (Q ∨ R))).
  { 
    rewrite -> (n9_13 (fun x => (φ x → Q) → ((φ x ∨ R) → (Q ∨ R))) X) in S1.
    pose proof (n9_21 (fun x => φ x → Q) (fun x => φ x ∨ R → Q ∨ R)) as n9_21.
    MP n9_21 S1.
    exact n9_21.
  }
  assert (S3 : ((∃ x, φ x) → Q) → (∃ x, φ x) ∨ R → Q ∨ R).
  {
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    repeat rewrite <- n9_03 in S2.
    repeat rewrite <- n9_02 in S2.
    repeat rewrite <- Impl1_01 in S2.
    rewrite <- n9_05 in S2.
    exact S2.
  }
  exact S3.
Qed.

(* Thm 9.6: `∀ x, φ x`, `¬(∀ x, φ x)`, `∃ x, φ x`, `¬(∃ x, φ x)` are of the same type. From *9.131, (7) and (8)  *)

(* Thm 9.61: If `φ x^` and `ψ x^` are elementary functions of the same type, there is a function `φ x^ ∨ ψ x^`. *)

(* Thm 9.62 : If `φ(x^, y^)` and `ψ z^` are elementary functions, and the x-argument to `φ` is of the same type as the argument of `ψ`, there are functions `(∀ y, φ(x^, y)) ∨ ψ x^`, `(∃ y, φ (x^, y) ∨ φ x^)` *)

(* Thm 9.63 : If `φ(x^, y^)` and `ψ(x^, y^)` are elementary functions of the same type, there are functions `(∀ y, φ(x^, y) ∨ ∀ z, ψ(x^, z)), etc.` *)
