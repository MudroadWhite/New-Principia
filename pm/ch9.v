Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.

Definition n9_01 (Phi : Prop -> Prop) :
  (¬ (∀ x : Prop, Phi x)) = (∃ x : Prop, ¬ Phi x). Admitted.

Definition n9_02 (Phi : Prop -> Prop) :
  (¬ (∃ x : Prop, Phi x)) = (∀ x : Prop, ¬ Phi x). Admitted.

Definition n9_011 (x : Prop) (Phi : Prop -> Prop) : 
  (¬ (∀ x, Phi x)) = ¬ (∀ x, Phi x). Admitted.

Definition n9_021 (x : Prop) (Phi : Prop -> Prop) :
  (¬ (∃ x, Phi x)) = ¬ (∃ x, Phi x). Admitted.

Definition n9_03 (Phi : Prop -> Prop) (p : Prop) :
  ((∀ x : Prop, Phi x) ∨ p) = (∀ x : Prop, Phi x ∨ p). Admitted.

Definition n9_04 (Phi : Prop -> Prop) (p : Prop) :
  (p ∨ (∀ x : Prop, Phi x)) = (∀ x : Prop, p ∨ Phi x). Admitted.

Definition n9_05 (Phi : Prop -> Prop) (p : Prop) :
  ((∃ x : Prop, Phi x) ∨ p) = (∃ x : Prop, Phi x ∨ p). Admitted.

Definition n9_06 (Phi : Prop -> Prop) (p : Prop) : 
  (p ∨ (∃ x : Prop, Phi x)) = ∃ x : Prop, p ∨ (Phi x). Admitted.

Definition n9_07 : ∀ (Phi Psi : Prop → Prop),
  ((∀ x : Prop, Phi x) ∨ (∃ y : Prop, Psi y))
  = ∀ x : Prop, ∃ y : Prop, Phi x ∨ Psi y. Admitted.

Definition n9_08 (Phi Psi : Prop → Prop) :
  ((∃ y, Psi y) ∨ (∀ x, Phi x)) = ∀ x, ∃ y, Psi y ∨ Phi x. Admitted.

Definition n9_1 (Phi : Prop → Prop) (x : Prop) : 
  (Phi x → ∃ z : Prop, Phi z). Admitted.

Definition n9_11 (Phi : Prop → Prop) (x y : Prop) : 
  (Phi x ∨ Phi y) → (∃ z : Prop, Phi z). Admitted.

(* Pp n9_12 : What is implied by a true premiss is true. 
I don't know how to translate this so far
*)
Definition n9_12 : Prop. Admitted.

(* Pp n9_13 : In any assersion containing a real variable, this real variable
may be turned into an apparent variable of which all possible values are asserted
to satisfy the function in question. *)
(* 
- `y` in `Phi y` is a real variable
- `y` in `∀ y, Phi y` is an apparent variable
- This simulation seems to be very unsatisfying! Don't use without any clear 
  intention from original text
*)
Definition n9_13 (Phi : Prop -> Prop) (X : Prop) : Phi X = (∀ y : Prop, Phi y). Admitted.

(* TODO: 
- Formalize the idea of `is same type` 
- Identify clearly what does "significant" mean *)
Definition is_individual (x : Prop) : Prop. Admitted.
Definition is_elementary_function (F : Prop -> Prop) : Prop. Admitted.
Definition is_same_type (u v : Prop) : Prop. Admitted.

Definition SameTy9_131 := is_same_type.

Definition n9_14 : ∀ (x a : Prop) (Phi : Prop -> Prop),
  Phi x -> (SameTy9_131 x a <-> Phi a). Admitted.

(* Pp n9_15 : If for some `a` there is a proposition `Phi a`, then there is a function
  `phi x^` and vice versa. *)

Theorem n9_2 (y : Prop) : ∀ (Phi : Prop → Prop), (∀ x : Prop, Phi x) → Phi y.
  Proof. intros.
  (** Step 1 **)
  specialize n2_1 with (Phi y). intros n2_1a.
  (** Step 2 **)
  specialize n9_1 with (fun x : Prop => ¬ Phi x ∨ Phi y) y. intros n9_1a.
  simpl in n9_1a.
  MP n2_1a n9_1a.
  (** Step 3 **)
  pose (n9_05 (fun x : Prop => ¬ Phi x) (Phi y)) as n9_05a. cbn in n9_05a.
  rewrite <- n9_05a in n9_1a.
  (** Step 4 **)
  specialize n9_01 with Phi. intros n9_01a.
  rewrite <- n9_01a in n9_1a.
  rewrite <- Impl1_01 in n9_1a. apply n9_1a.
  apply H.
Qed.

Theorem n9_21 (Z : Prop) (Phi Psi : Prop → Prop) :
  (∀ x, Phi x → Psi x) 
  → (∀ y, Phi y) 
  → ∀ z, Psi z.
Proof.
  (** Necessary tools to be used globally **)
  (* Manually set up a `<->` relation from `=` relation to utilize
  `setoid_rewrite`. This enables substitution outside of the
  `∀`s and `exists`.
  Can we automate this with Ltac? *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (Phi0 : Prop -> Prop) (P0 : Prop), 
    eq_to_equiv 
      (P0 ∨ ∃ x : Prop, Phi0 x) (∃ x : Prop, P0 ∨ Phi0 x) 
      (n9_06 Phi0 P0))
  as n9_06a.
  (** S1 **)
  pose proof (Id2_08 (Phi Z → Psi Z)) as S1.
  (** S2 **)
  assert (S2 : ∃ y : Prop, (Phi Z → Psi Z) → Phi y → Psi Z).
  {
    remember (fun x => (Phi Z → Psi Z) → Phi x → Psi Z) as f_S1 eqn:eqf_S1.
    pose (n9_1 f_S1 Z) as n9_1.
    rewrite -> eqf_S1 in n9_1. rewrite -> eqf_S1.
    exact (n9_1 S1).
  }
  (** S3 **)
  assert (S3 : ∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi Z).
  {
    remember (fun x => (∃ z0 : Prop, (Phi x → Psi x) → Phi z0 → Psi Z))
      as f_S2 eqn:eqf_S2.
    pose (n9_1 f_S2 Z) as n9_1.
    rewrite -> eqf_S2 in n9_1. rewrite -> eqf_S2.
    exact (n9_1 S2).
  }
  (** S4 **)
  assert (S4 : ∀ z : Prop, ∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi z).
  {
    set (f_S3 := fun z => (∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi z)).
    change (∃ x y, (Phi x → Psi x) → Phi y → Psi Z) with (f_S3 Z) in S3.
    change (∃ x y, (Phi x → Psi x) → Phi y → Psi Z) with (f_S3 z).
    rewrite -> (n9_13 f_S3 Z) in S3.
    exact S3.
  }
  (** S5 **)
  assert (S5 : ∀ z : Prop, (∃ x : Prop, 
    (Phi x → Psi x) → (∃ y : Prop, Phi y → Psi z))).
  {
    (* 
    From here on the proof becomes very unsatisfying. Since it's difficult to use 
    other tools, we have to destruct the propositions to procceed. I don't think 
    this is the right way to proceed on, but it's current the only way working
    *)
    assert (S4_i1 : ∀ z : Prop, ∃ x y : Prop, 
      ¬(Phi x → Psi x) ∨ (Phi y → Psi z)).
    { setoid_rewrite Impl1_01a in S4. exact S4. }
    intro z0. pose (S4_i1 z0) as S4_i2.
    remember (fun y0 => Phi y0 → Psi z0) as f_S4 eqn:eqf_S4.
    setoid_rewrite <- n9_06a in S4_i2.
    rewrite -> eqf_S4.
    destruct S4_i2 as [z1 S4_i3]. exists z1.
    pose (n2_53 (¬ (Phi z1 → Psi z1)) (∃ x : Prop, Phi x → Psi z0) S4_i3) as n2_53.
    exact (fun y1 => n2_53 (n2_12 (Phi z1 → Psi z1) y1)).
  }
  assert (S6 : ((∃ x, ¬(Phi x → Psi x)) ∨ (∀ y, ∃ z, (¬ Phi z) ∨ Psi y))).
  {
    assert (S5_1 : ∀ z0 : Prop, ∃ x0 : Prop, 
      (¬ (Phi x0 → Psi x0) ∨ (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z0))). 
    {
      setoid_rewrite Impl1_01a in S5.
      setoid_rewrite Impl1_01a in S5 at 3.
      exact S5.
    }
    remember (fun x1 => ¬ (Phi x1 → Psi x1)) as f_S5_1 eqn:eqf_S5_1.
    remember (fun z1 => (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z1)) as f_S5_2 eqn:eqf_S5_2.
    pose (n9_08 f_S5_2 f_S5_1) as n9_08.
    rewrite -> eqf_S5_1.
    rewrite -> eqf_S5_1 in n9_08.
    rewrite -> eqf_S5_2 in n9_08.
    rewrite -> n9_08.
    exact S5_1.
  }
  assert (S7 : (∃ x : Prop, ¬(Phi x → Psi x)) ∨ ((∃ y : Prop, (¬ Phi y)) ∨ (∀ z : Prop, Psi z))).
  {
    remember (fun y => ¬ (Phi y)) as f_S6_1 eqn:eqf_S6_1.
    rewrite -> n9_08.
    rewrite -> eqf_S6_1.
    exact S6.
  }
  assert (S8 : (∀ x, Phi x → Psi x) → (∀ y, Phi y) → ∀ z, Psi z).
  {
    repeat rewrite <- n9_01 in S7.
    repeat rewrite <- Impl1_01 in S7.
    exact S7.
  }
  exact S8.
Qed.

Theorem n9_22 (Y : Prop) (Phi Psi : Prop -> Prop) :
  (∀ x, Phi x -> Psi x) -> (∃ x, Phi x) -> (∃ x, Psi x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (P0 : Prop) (Phi0 : Prop -> Prop),
    eq_to_equiv (P0 ∨ ∃ x : Prop, Phi0 x) (∃ x : Prop, P0 ∨ Phi0 x) 
    (n9_06 Phi0 P0)) as n9_06a.
  set (λ Phi0 Psi0 : (Prop -> Prop), 
    eq_to_equiv 
      ((∃ y : Prop, Psi0 y) ∨ ∀ x : Prop, Phi0 x) 
      (∀ x : Prop, ∃ y : Prop, Psi0 y ∨ Phi0 x) 
      (n9_08 Phi0 Psi0)) as n9_08a.
  set (λ Phi0 Psi0 : (Prop -> Prop), 
    eq_to_equiv 
      ((∀ x : Prop, Phi0 x) ∨ (∃ y : Prop, Psi0 y))
      (∀ x : Prop, ∃ y : Prop, Phi0 x ∨ Psi0 y)
      (n9_07 Phi0 Psi0)) as n9_07a.
  (* ******** *)
  pose (Id2_08 (Phi Y -> Psi Y)) as S1.
  assert (S2 : exists z, (Phi Y -> Psi Y) -> (Phi Y -> Psi z)).
  { 
    remember (fun z => (Phi Y -> Psi Y) -> (Phi Y -> Psi z))
      as f_S1 eqn:eqf_S1.
    pose (n9_1 f_S1 Y) as n9_1.
    rewrite -> eqf_S1 in n9_1.
    rewrite -> eqf_S1.
    exact (n9_1 S1).
  }
  assert (S3 : exists x, exists z, (Phi x -> Psi x) -> (Phi Y -> Psi z)).
  { 
    remember (fun x => exists z, (Phi x -> Psi x) -> (Phi Y -> Psi z))
      as f_S2 eqn:eqf_S2.
    pose (n9_1 f_S2 Y) as n9_1.
    rewrite -> eqf_S2 in n9_1.
    rewrite -> eqf_S2.
    exact (n9_1 S2).
  }
  assert (S4 : ∀ y, exists x, exists z, (Phi x -> Psi x) -> (Phi y -> Psi z)).
  {
    set (f_S3 := (fun y => (exists x, exists z, 
      (Phi x -> Psi x) -> (Phi y -> Psi z)))).
    change ((exists x, exists z, (Phi x -> Psi x) -> (Phi Y -> Psi z)))
      with (f_S3 Y) in S3.
    change (∀ y0 : Prop, ∃ x z : Prop, (Phi x → Psi x) → Phi y0 → Psi z)
      with (∀ y0 : Prop, f_S3 y0).
    rewrite -> (n9_13 f_S3 Y) in S3.
    exact S3.
  }
  assert (S5 : ∀ y, exists x, (Phi x -> Psi x) -> (exists z, (Phi y -> Psi z))).
  { 
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    setoid_rewrite <- Impl1_01a in S4.
    exact S4.
  }
  assert (S6 : (exists x, ¬ (Phi x -> Psi x)) ∨ ∀ y, (exists z, (Phi y -> Psi z))).
  {
    setoid_rewrite -> Impl1_01a in S5.
    setoid_rewrite <- n9_08a in S5.
    exact S5.
  }
  assert (S7 : (exists x, ¬ (Phi x -> Psi x)) ∨ (∀ y, ¬ (Phi y)) ∨ exists z, Psi z).
  { 
    setoid_rewrite -> Impl1_01a in S6 at 3.
    setoid_rewrite <- n9_07a in S6.
    exact S6.
  }
  assert (S8 : (∀ x, Phi x -> Psi x) -> (∃ x, Phi x) -> (∃ x, Psi x)).
  { 
    assert (S7_i1 : (∀ x : Prop, Phi x → Psi x)
      -> (¬¬(∀ y : Prop, ¬ Phi y)) ∨ ∃ z : Prop, Psi z).
    {
      rewrite <- n9_01 in S7.
      rewrite <- Impl1_01 in S7.
      replace (∀ y : Prop, ¬ Phi y) with (¬ ¬ (∀ y : Prop, ¬ Phi y)) in S7.
      2: {
        symmetry. apply propositional_extensionality. 
        exact (n4_13 (∀ y : Prop, ¬ Phi y)).
      }
      exact S7.
    }
    rewrite <- n9_02 in S7_i1.
    rewrite <- Impl1_01 in S7_i1.
    replace (¬ ¬ ∃ x : Prop, Phi x) with (∃ x : Prop, Phi x) in S7_i1.
    2: {
      apply propositional_extensionality. 
      setoid_rewrite <- n4_13.
      reflexivity.
    }
    exact S7_i1.
  }
  exact S8.
Qed.

Theorem n9_23 (Phi : Prop -> Prop) : (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x).
(* Original proof uses Id, 9.13, 9.21 *)
Proof. exact (Id2_08 (∀ x : Prop, Phi x)). Qed.

Theorem n9_24 (Phi : Prop -> Prop) : (∃ x : Prop, Phi x) -> (∃ x : Prop, Phi x).
(* Original proof uses Id, 9.13, 9.22 *)
Proof. exact (Id2_08 (∃ x : Prop, Phi x)). Qed.

Theorem n9_25 (p : Prop) (Phi : Prop -> Prop) : 
  (∀ x : Prop, p ∨ Phi x) -> p ∨ (∀ x : Prop, Phi x).
Proof.
  (* TODO: rewrite the proof! start posing the initial proposition with n9_23. *)
  pose (n9_04 Phi p) as n9_04.
  intro H.
  rewrite <- n9_04 in H.
  exact H.
Qed.

Theorem n9_3 (X : Prop) (Phi : Prop -> Prop) : 
  (∀ x : Prop, Phi x) ∨ (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose (Taut1_2 (Phi X)) as S1.
  assert (S2 : exists y, (Phi X ∨ Phi y) -> Phi X).
  { 
    remember (fun y => (Phi X ∨ Phi y) -> Phi X) as f_S1 eqn:eqf_S1.
    pose (n9_1 f_S1 X) as n9_1a.
    rewrite -> eqf_S1.
    rewrite -> eqf_S1 in n9_1a.
    exact (n9_1a S1).
  }
  assert (S3 : ∀ x, exists y, (Phi x ∨ Phi y) -> Phi x).
  {
    remember (fun x => exists y, (Phi x ∨ Phi y) -> Phi x) as f_S2 eqn:eqf_S2.
    pose (n9_13 f_S2 X) as n9_13.
    rewrite -> eqf_S2 in n9_13.
    rewrite -> n9_13 in S2.
    exact S2.
  }
  assert (S4 : ∀ x, (Phi x ∨ ∀ y, Phi y) -> Phi x).
  {
    setoid_rewrite -> Impl1_01a in S3.
    assert (S3_i1 : ∀ x, ¬ (Phi x ∨ ∀ y, Phi y) ∨ Phi x).
    {
      remember (fun x y => ¬ (Phi x ∨ Phi y)) as f_S3 eqn:eqf_S3.
      pose (f_equal (fun (P : Prop → Prop -> Prop) => 
        (∀ x, exists y, (P x y) ∨ Phi x)) eqf_S3) as eqf_S3_xy.
      simpl in eqf_S3_xy.
      (* TODO: create setoid_rewrite instances? *)
      rewrite <- eqf_S3_xy in S3.
      intro x0.
      pose (S3 x0) as S3_1.
      rewrite <- (n9_05 (f_S3 x0) (Phi x0)) in S3_1.
      rewrite -> eqf_S3 in S3_1.
      rewrite <- (n9_01 (fun x => Phi x0 ∨ Phi x)) in S3_1.
      rewrite <- (n9_04 Phi (Phi x0)) in S3_1.
      exact S3_1.
    }
    setoid_rewrite <- Impl1_01a in S3_i1.
    exact S3_i1.
  }
  assert (S5 : (∀ x, (Phi x ∨ ∀ y, Phi y)) -> (∀ x, Phi x)).
  (* Here the apparent variable `X` can be arbitrary *)
  { exact (n9_21 X (fun x => Phi x ∨ (∀ y : Prop, Phi y)) Phi S4). }
  assert (S6 : (∀ x : Prop, Phi x) ∨ (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x)).
  { rewrite <- n9_03 in S5. exact S5. }
  exact S6.
Qed.

(* I think thw proof to this proposition is totally wrong, but all 
russell wants to do is just introducing in an `exists`. TODO: find 
another way to do this correctly in the future *)
Theorem n9_31 (X : Prop) (Phi : Prop -> Prop) : 
  ((∃ x : Prop, Phi x) ∨ (∃ x : Prop, Phi x)) -> (∃ x : Prop, Phi x).
Proof. 
  assert (S1 : ∀ y, Phi X ∨ Phi y -> exists z, Phi z).
  {
    pose (n9_11 Phi X X) as n9_11. 
    pose (n9_13 (fun y => (Phi X ∨ Phi y) → ∃ z : Prop, Phi z) X) as n9_13.
    (* Coq will automatically find `n9_13` here to match up. Can we just utilize
    this to create an Ltac specifically for `n9_13`?!...... *)
    replace (Phi X ∨ Phi X -> exists z, Phi z) 
      with (∀ y , Phi X ∨ Phi y -> exists z, Phi z) in n9_11.
    exact n9_11.
  }
  assert (S2 : (exists y, Phi X ∨ Phi y) -> (exists z, Phi z)).
  {
    replace (∀ y : Prop, Phi X ∨ Phi y  → ∃ z : Prop, Phi z) 
      with (∀ y : Prop, Phi y \/ Phi X  → ∃ z : Prop, Phi z)
      in S1.
    2: { (* NOTE: the right way is use setoid_rewrite on `Perm1_4`. Here being lazy *)
      apply propositional_extensionality.
      setoid_rewrite <- or_comm at 1.
      reflexivity.
    }
    replace (∀ y : Prop, (Phi y ∨ Phi X  → ∃ z : Prop, Phi z))
      with ((∀ y : Prop, Phi y) ∨ Phi X  → ∃ z : Prop, Phi z)
      in S1.
    2: { admit. }
    replace (∀ y : Prop, Phi y) with (∀ y : Prop, ¬ ¬ (Phi y)) in S1.
    2: { admit. }
    remember (fun x => ¬ Phi x) as f_S1 eqn:eqf_S1.
    (* replace (∀ y : Prop, Phi X ∨ Phi y → ∃ z : Prop, Phi z)
      with (∀ y : Prop, Phi X ∨ ¬ ¬(Phi y) → ∃ z : Prop, Phi z)
      in S1.
    2: {
      symmetry. apply propositional_extensionality.
      setoid_rewrite -> n4_13 at 7. reflexivity.
    } *)
    replace (∀ x : Prop, ¬ ¬ Phi x) with (∀ x : Prop, ¬ (f_S1 x)) in S1
      by (rewrite -> eqf_S1; reflexivity).
    replace (∀ x : Prop, ¬ f_S1 x) with (¬ (∃ x : Prop, f_S1 x)) in S1
      by exact (n9_02 f_S1).
    rewrite -> eqf_S1 in S1.
    replace (¬ (∃ x : Prop, f_S1 x)) with (∃ x : Prop, f_S1 x).
    admit. admit.
  }
Admitted.

Theorem n9_32 (Phi : Prop -> Prop) (Q X : Prop) : Q -> (∀ x : Prop, Phi x) ∨ Q.
Proof. 
  (* TOOLS *)
  (* set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a. *)
  (* ******** *)
  pose proof (Add1_3 (Phi X) Q) as S1.
  assert (S2 : forall x, Q -> (Phi x) \/ Q).
  {
    pose (n9_13 (fun x => Q -> (Phi x) \/ Q) X) as n9_13.
    replace (Q → Phi X ∨ Q) with (forall x, Q -> (Phi x) \/ Q) in S1.
    exact S1.
  }
  assert (S3 : Q -> forall x, Phi x \/ Q).
  { 
    pose proof (n9_25 (~ Q) (fun x => Phi x \/ Q)) as n9_25.
    simpl in n9_25.
    replace (∀ x : Prop, Q → Phi x ∨ Q) with (∀ x : Prop, ~ Q \/ (Phi x ∨ Q))
      in S2.
    2: {
      (* TODO: use f_equal here to generate the right equation? *)
      Print f_equal.
      admit.
    }
    pose (n9_25 S2) as S2_1.
    rewrite <- Impl1_01 in S2_1.
    exact S2_1.
  }
  assert (S4 : Q -> (∀ x : Prop, Phi x) ∨ Q).
  { 
    intro Q0. pose (S3 Q0) as S3_1.
    rewrite <- (n9_03 Phi Q) in S3_1.
    exact S3_1.
  }
  exact S4.
Admitted.
  
Theorem n9_33 (Phi : Prop -> Prop) (Q : Prop) : Q -> (∃ x : Prop, Phi x) ∨ Q.
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_34 (Phi : Prop -> Prop) (X P : Prop) : 
  (∀ x : Prop, Phi x) -> P ∨ (∀ x : Prop, Phi x).
Proof. 
  pose proof (Add1_3 P (Phi X)) as S1.
  assert (S2 : forall x, Phi x -> P \/ Phi x).
  { 
    pose proof (n9_13 (fun x => Phi x -> P \/ Phi x) X).
    replace (Phi X → P ∨ Phi X) with (forall x, Phi x -> P \/ Phi x)
      in S1.
    exact S1.
  }
  assert (S3 : (forall x, Phi x) -> (forall x, P \/ Phi x)).
  { exact (n9_21 X Phi (fun x => P \/ Phi x) S2). }
  assert (S4 : (∀ x : Prop, Phi x) -> P ∨ (∀ x : Prop, Phi x)).
  {
    pose proof (n9_04 Phi P) as n9_04. 
    rewrite <- n9_04 in S3.
    exact S3.
  }
  exact S4.
Qed.

Theorem n9_35 (Phi : Prop -> Prop) (P : Prop) : (∃ x : Prop, Phi x) -> P ∨ (∃ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_36 (Phi : Prop -> Prop) (X P : Prop) : P ∨ (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x) ∨ P.
Proof. 
  pose proof (Perm1_4 P (Phi X)) as S1.
  assert (S2 : (forall x, (P \/ Phi x)) -> forall x, (Phi x \/ P)).
  { 
    pose proof (n9_13 (fun x => P ∨ Phi x → Phi x ∨ P) X) as n9_13a.
    rewrite -> n9_13a in S1.
    pose proof (n9_21 X (fun x => P \/ Phi x) (fun x => Phi x \/ P)) as n9_21.
    exact (n9_21 S1).
  }
  assert (S3 : P ∨ (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x) ∨ P).
  { 
    pose proof (n9_04 Phi P) as n9_04.
    rewrite <- n9_04 in S2.
    pose proof (n9_03 Phi P) as n9_03.
    rewrite <- n9_03 in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n9_361 : ∀ (Phi : Prop -> Prop) (P : Prop), (∀ x : Prop, Phi x) ∨ P -> P ∨ (∀ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_37 : ∀ (Phi : Prop -> Prop) (P : Prop), P ∨ (∃ x : Prop, Phi x) -> (∃ x : Prop, Phi x) ∨ P.
Proof.
  (* Proof as above *)
Admitted.

Theorem n9_371 : ∀ (Phi : Prop -> Prop) (P : Prop), (∃ x : Prop, Phi x) ∨ P -> P ∨ (∃ x : Prop, Phi x).
Proof. 
  (* Proof as above *)
Admitted.

Theorem n9_4 : ∀ (Phi : Prop -> Prop) (P Q : Prop), P ∨ Q ∨ (∀ x : Prop, Phi x)
  -> Q ∨ P ∨ (∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_401 : ∀ (Phi : Prop -> Prop) (P Q : Prop), P ∨ Q ∨ (∃ x : Prop, Phi x)
  -> Q ∨ P ∨ (∃ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_41 : ∀ (Phi : Prop -> Prop) (P R : Prop), P ∨ (∀ x : Prop, Phi x) ∨ R
  -> (∀ x : Prop, Phi x) ∨ P ∨ R.
Proof. Admitted.

Theorem n9_411 : ∀ (Phi : Prop -> Prop) (P R : Prop), P ∨ (∃ x : Prop, Phi x) ∨ R
  -> (∃ x : Prop, Phi x) ∨ P ∨ R.
Proof. Admitted.

Theorem n9_42 : ∀ (Phi : Prop -> Prop) (Q R : Prop), (∀ x : Prop, Phi x) ∨ Q ∨ R
  -> Q ∨ (∀ x : Prop, Phi x) ∨ R.
Proof. Admitted.

Theorem n9_421 : ∀ (Phi : Prop -> Prop) (Q R : Prop), (∃ x : Prop, Phi x) ∨ Q ∨ R
  -> Q ∨ (∃ x : Prop, Phi x) ∨ R.
Proof. Admitted.

(* TODO: Accuracy in understanding? *)
Theorem n9_5 : ∀ (Phi : Prop -> Prop) (P Q : Prop), (P -> Q) 
  -> (P ∨ ∀ x : Prop, Phi x) -> (Q ∨ ∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_501 : ∀ (Phi : Prop -> Prop) (P Q : Prop), (P -> Q) 
  -> (P ∨ ∃ x : Prop, Phi x) -> (Q ∨ ∃ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_51 : ∀ (Phi : Prop -> Prop) (P R : Prop), 
  (P -> ∀ x : Prop, Phi x) -> P ∨ R -> (∀ x : Prop, Phi x) ∨ R.
Proof. Admitted.

Theorem n_9_511 : ∀ (Phi : Prop -> Prop) (P R : Prop), 
  (P -> ∃ x : Prop, Phi x) -> P ∨ R -> (∃ x : Prop, Phi x) ∨ R.
Proof. Admitted.

(* TODO: Accuracy in understanding? *)
Theorem n_9_52 : ∀ (Phi : Prop -> Prop) (Q R : Prop), 
  ((∀ x : Prop, Phi x) -> Q) -> (∀ x : Prop, Phi x) ∨ R -> Q ∨ R.
Proof. Admitted.

Theorem n_9_521 : ∀ (Phi : Prop -> Prop) (Q R : Prop), 
  ((∃ x : Prop, Phi x) -> Q) -> (∃ x : Prop, Phi x) ∨ R -> Q ∨ R.
Proof. Admitted.

(* Thm 9.6, 9.61 - 9.63: pure text propositions *)
