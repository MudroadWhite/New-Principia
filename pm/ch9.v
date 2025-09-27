Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.

Axiom n9_01 : ∀ F : Prop → Prop,
  (¬(∀ x : Prop, F x)) = (∃ x : Prop, ¬ F x).

Axiom n9_02 : ∀ F : Prop → Prop,
  ¬(∃ x : Prop, F x) = (∀ x : Prop, ¬ F x).

Definition n9_011 (x : Prop) (Phi : Prop -> Prop) : 
  ¬ (∀ x, Phi x) = ¬ (∀ x, Phi x). Admitted.

Definition n9_021 (x : Prop) (Phi : Prop -> Prop) :
  ¬ (∃ x, Phi x) = ¬ (∃ x, Phi x). Admitted.

Axiom n9_03 : ∀ F : Prop → Prop, ∀ P : Prop,
  ((∀ x : Prop, F x) ∨ P) = (∀ x : Prop, F x ∨ P).

Axiom n9_04 : ∀ F : Prop → Prop, ∀ P : Prop,
  (P ∨ (∀ x : Prop, F x)) = (∀ x : Prop, P ∨ F x).

Axiom n9_05 : ∀ (F : Prop → Prop) (P : Prop),
  ((∃ x : Prop, F x) ∨ P) = (∃ x : Prop, F x ∨ P).

Definition n9_06 (p : Prop) (Phi : Prop → Prop) : 
  (p ∨ (∃ x : Prop, Phi x)) = ∃ x : Prop, p ∨ Phi x. Admitted.

Definition n9_07 : ∀ (Phi Psi : Prop → Prop),
  (∀ x : Prop, Phi x) ∨ (∃ y : Prop, Psi y)
  = ∀ x : Prop, ∃ y : Prop, Phi x ∨ Psi y. Admitted.

Definition n9_08 (Phi Psi : Prop → Prop) :
  ((∃ y, Psi y) ∨ (∀ x, Phi x)) = ∀ x, ∃ y, Psi y ∨ Phi x. Admitted.

Definition n9_1 (Phi : Prop → Prop) (x : Prop) : 
  (Phi x → ∃ z : Prop, Phi z). Admitted.

Axiom n9_11 : ∀ x y : Prop, ∀ F : Prop → Prop, ((F x ∨ F y) → (∃z : Prop, F z)).

(* Pp n9_12 : What is implied by a true premiss is true. *)

(* Pp n9_13 : In any assersion containing a real variable, this real variable
may be turned into an apparent variable of which all possible values are asserted
to satisfy the function in question. *)
Axiom n9_13 : ∀ x : Prop, ∀ F : Prop → Prop, F x
  → (∀ y : Prop, F y).

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
  specialize n9_1 with (fun x : Prop => ~ Phi x ∨ Phi y) y. intros n9_1a.
  simpl in n9_1a.
  MP n2_1a n9_1a.
  (** Step 3 **)
  pose (n9_05 (fun x : Prop => ~ Phi x) (Phi y)) as n9_05a. cbn in n9_05a.
  rewrite <- n9_05a in n9_1a.
  (** Step 4 **)
  specialize n9_01 with Phi. intros n9_01a.
  rewrite <- n9_01a in n9_1a.
  rewrite <- Impl1_01 in n9_1a. apply n9_1a.
  apply H.
Qed.

(* NOTE: `z` here seems to be something needed to consider in the future: there's a 
difference between `z` and `∀ z, z`. We will have to check how to express this
according to the original article
*)
Theorem n9_21 (Z : Prop) (Phi Psi : Prop → Prop) :
  (∀ x, Phi x → Psi x) 
  → (∀ y, Phi y) 
  → ∀ z, Psi z.
Proof.
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
    change (∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi Z) with (f_S3 Z) in S3.
    change (∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi Z) with (f_S3 z).
    exact (n9_13 Z f_S3 S3).
  }
  (** S5 **)
  assert (S5 : ∀ z : Prop, (∃ x : Prop, 
    (Phi x → Psi x) → (∃ y : Prop, Phi y → Psi z))).
  {
    (* 
    From here on the proof becomes very unsatisfying. Usually we should define the 
    function over all the `exists`, but instead we peel them off to define a function 
    without the `exists`. I don't think this is the right way to proceed on, but
    it's current the only way working
    *)
    assert (S4_i1 : ∀ z : Prop, ∃ x y : Prop, 
      ¬(Phi x → Psi x) ∨ (Phi y → Psi z)).
    {
      (* Peeling the proposition *)
      intro z0. pose (S4 z0) as S4_1.
      destruct S4_1 as [z1 S4_2]. exists z1.
      destruct S4_2 as [z2 S4_3]. exists z2.
      rewrite -> Impl1_01 in S4_3.
      exact S4_3.
    }
    intro z0. pose (S4_i1 z0) as S4_i2.
    remember (fun y0 => Phi y0 → Psi z0) as f_S4 eqn:eqf_S4.
    destruct S4_i2 as [z1 S4_i3]. exists z1.
    pose (n9_06 (¬(Phi z1 → Psi z1)) f_S4) as n9_06.
    (* Here we use `f_equal` to avoid another peeling down *)
    pose (f_equal (fun (P : Prop → Prop) => 
      (exists y1, ¬ (Phi z1 → Psi z1) ∨ (P y1))) eqf_S4) as eqf_S4_y1.
    rewrite <- eqf_S4_y1 in S4_i3.
    rewrite <- n9_06 in S4_i3.
    rewrite -> eqf_S4 in S4_i3.
    pose (n2_53 (¬ (Phi z1 → Psi z1)) (∃ x : Prop, Phi x → Psi z0) S4_i3) as n2_53.
    pose (n2_12 (Phi z1 → Psi z1)) as n2_12.
    rewrite -> eqf_S4.
    exact (fun y1 => n2_53 (n2_12 y1)).
  }
  assert (S6 : ((∃ x, ¬(Phi x → Psi x)) ∨ (∀ y, ∃ z, (¬ Phi z) ∨ Psi y))).
  {
    assert (S5_1 : ∀ z0 : Prop, ∃ x0 : Prop, 
      (~ (Phi x0 → Psi x0) ∨ (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z0))
    ). 
    {
      intro z0. pose (S5 z0) as S5_i1.
      destruct S5_i1 as [z1 S5_i2]. exists z1.
      pose (Impl1_01 (Phi z1 → Psi z1) (∃ y : Prop, Phi y → Psi z0))
        as Impl1_01_1.
      rewrite -> Impl1_01_1 in S5_i2.
      destruct S5_i2.
      { left. exact H. }
      { right.
        destruct H as [y H1]. exists y.
        pose (Impl1_01 (Phi y) (Psi z0)) as Impl_1_01_2.
        rewrite -> Impl_1_01_2 in H1.
        exact H1. }
    }
    remember (fun x1 => ¬ (Phi x1 → Psi x1)) as f_S5_1 eqn:eqf_S5_1.
    remember (fun z1 => (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z1)) as f_S5_2 eqn:eqf_S5_2.
    pose (n9_08 f_S5_2 f_S5_1) as n9_08.
    rewrite -> eqf_S5_1.
    rewrite -> eqf_S5_1 in n9_08.
    (* Notice the different behavior between f1 and f2. Seems like every functions
    involving `∃` will have some problems *)
    rewrite -> eqf_S5_2 in n9_08.
    rewrite -> n9_08.
    exact S5_1.
  }
  assert (S7 : (∃ x : Prop, ¬(Phi x → Psi x)) ∨ ((∃ y : Prop, (¬ Phi y)) ∨ (∀ z : Prop, Psi z))).
  {
    (* f_S6_1 and f_S6_2 has different behaviors on S6.
    The commented code below shouldnt be deleted *)
    remember (fun y => ¬ (Phi y)) as f_S6_1 eqn:eqf_S6_1.
    remember (fun z => Psi z) as f_S6_2 eqn:eqf_S6_2.
    (* assert (eqH : ((∃ y, f_S6_1 y) ∨ (∀ z0 : Prop, f_S6_2 z0)) =
          ∀ z0, ∃ y, f_S6_1 y ∨ f_S6_2 z0). { exact (n9_08 f_S6_2 f_S6_1). } *)
    (* rewrite -> eqf_S6_1 in S6. *)
    rewrite -> n9_08. (* Alternatively, we can provide an exact instance for n9_08
    to form an exact equation, as comment above. But since 2 functions don't behave
    in the same way, this exact equation still needs some tunings *)
    rewrite -> eqf_S6_1.
    exact S6.
  }
  assert (S8 : (∀ x, Phi x → Psi x) → (∀ y, Phi y) → ∀ z, Psi z).
  {
    (* Here I want to be lazy and don't want to stick to total forward reasoning with 
    concrete instances specified. "Left as an exercise" *)
    rewrite <- n9_01 in S7.
    rewrite <- n9_01 in S7.
    rewrite <- Impl1_01 in S7.
    rewrite <- Impl1_01 in S7.
    exact S7.
  }
  exact S8.
Qed.

Theorem n9_22 (Y : Prop) (Phi Psi : Prop -> Prop) :
  (∀ x, Phi x -> Psi x) -> (∃ x, Phi x) -> (∃ x, Psi x).
Proof. 
  assert (S1 : (Phi Y -> Psi Y) -> (Phi Y -> Psi Y)).
  { exact (Id2_08 (Phi Y -> Psi Y)). }
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
  assert (S4 : forall y, exists x, exists z, (Phi x -> Psi x) -> (Phi y -> Psi z)).
  {
    set (f_S3 := (fun y => (exists x, exists z, 
      (Phi x -> Psi x) -> (Phi y -> Psi z)))).
    change ((exists x, exists z, (Phi x -> Psi x) -> (Phi Y -> Psi z)))
      with (f_S3 Y) in S3.
    change (∀ y0 : Prop, ∃ x z : Prop, (Phi x → Psi x) → Phi y0 → Psi z)
      with (∀ y0 : Prop, f_S3 y0).
    exact (n9_13 Y f_S3 S3).
  }
  assert (S5 : forall y, exists x, (Phi x -> Psi x) -> (exists z, (Phi y -> Psi z))).
  { 
  (* S4': exists z ,(Phi x → Psi x) → Phi y → Psi z *)
  (* S5': (Phi x -> Psi x) -> (exists z, (Phi y -> Psi z)) *)
  (* n9_06:
    ∀ (p : Prop) (Phi : Prop → Prop),
      (p ∨ ∃ x : Prop, Phi x) = ∃ x : Prop, p ∨ Phi x
  *)
    assert (S4_i1 : forall y, exists x, exists z, 
      ~ (Phi x -> Psi x) \/ (Phi y -> Psi z)).
    {
    (* When the proposition involves an equation, peeling the proposition seems to
    be inevitable
    Otherwise, we're supposed to lift the proposition `P` into a proposition of
    `forall x, exists y, ..., P x y ` *)
      intro y0.
      pose (S4 y0) as S4_1.
      destruct S4_1 as [x S4_2]. exists x.
      destruct S4_2 as [z S4_3]. exists z.
      rewrite -> Impl1_01 in S4_3.
      exact S4_3.
    }
    (* 
    remember (fun y x => (exists z : Prop,
      ~ (Phi x -> Psi x) → (Phi y -> Psi z))) as f_S4 eqn:eqf_S4.
    *)
    intro y0. pose (S4_i1 y0) as S4_i2.
    remember (fun x z => ¬ (Phi x → Psi x) ∨ (Phi y0 → Psi z)) as f_S4
      eqn:eqf_S4.
    pose (f_equal (fun (P : Prop -> Prop -> Prop) => P y0) eqf_S4) as eqf_S4_y0.
    simpl in eqf_S4_y0.
    set (f_S4 := (fun y x => (exists z : Prop,
      ~ (Phi x -> Psi x) → (Phi y -> Psi z)))).
    

    (* TODO: use f_equal  *)
    change (∀ y : Prop, ∃ x z : Prop,
      ¬ (Phi x → Psi x) ∨ (Phi y → Psi z))
    with
      (∀ y : Prop, ∃ x z : Prop, f_S4 y x) in S4_i1.
    Print n9_06.


    change (forall y : Prop, exists (x z : Prop), (Phi x → Psi x) → Phi y → Psi z)
      with (forall y : Prop, exists x, f_S4 y x) in S4.
    
    pose (n9_06 z f_S4) as n9_06.
  admit. 
  }
  assert (S6 : (exists x, ~ (Phi x -> Psi x)) ∨ forall y, (exists z, (Phi y -> Psi z))).
  { admit. }
  assert (S7 : (exists x, ~ (Phi x -> Psi x)) ∨ 
    forall y, ~ (Phi y) ∨ exists z, Psi z).
  { admit. }
  assert (S8 : (∀ x, Phi x -> Psi x) -> (∃ x, Phi x) -> (∃ x, Psi x)).
  { admit. }
  exact S8.
Admitted.
  

Theorem n9_23 : ∀ (Phi : Prop -> Prop), (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_24 : ∀ (Phi : Prop -> Prop), (∃ x : Prop, Phi x) -> (∃ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_25 : ∀ (Phi : Prop -> Prop) (P : Prop), (∀ x : Prop, P ∨ Phi x) -> P ∨ (∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_3 : ∀ (Phi : Prop -> Prop), (∀ x : Prop, Phi x) ∨ (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_31 : ∀ (Phi : Prop -> Prop), (∃ x : Prop, Phi x) ∨ (∃ x : Prop, Phi x) -> (∃ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_32 : ∀ (Phi : Prop -> Prop) (Q : Prop), Q -> (∀ x : Prop, Phi x) ∨ Q.
Proof. Admitted.

Theorem n9_33 : ∀ (Phi : Prop -> Prop) (Q : Prop), Q -> (∃ x : Prop, Phi x) ∨ Q.
Proof. Admitted.

Theorem n9_34 : ∀ (Phi : Prop -> Prop) (P : Prop), (∀ x : Prop, Phi x) -> P ∨ (∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_35 : ∀ (Phi : Prop -> Prop) (P : Prop), (∃ x : Prop, Phi x) -> P ∨ (∃ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_36 : ∀ (Phi : Prop -> Prop) (P : Prop), P ∨ (∀ x : Prop, Phi x) -> (∀ x : Prop, Phi x) ∨ P.
Proof. Admitted.

Theorem n9_361 : ∀ (Phi : Prop -> Prop) (P : Prop), (∀ x : Prop, Phi x) ∨ P -> P ∨ (∀ x : Prop, Phi x).
Proof. Admitted.

Theorem n9_37 : ∀ (Phi : Prop -> Prop) (P : Prop), P ∨ (∃ x : Prop, Phi x) -> (∃ x : Prop, Phi x) ∨ P.
Proof. Admitted.

Theorem n9_371 : ∀ (Phi : Prop -> Prop) (P : Prop), (∃ x : Prop, Phi x) ∨ P -> P ∨ (∃ x : Prop, Phi x).
Proof. Admitted.

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
