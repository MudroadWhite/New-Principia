Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch9.

(* The goal of chapter 10 is extend the propositions from `p → q` 
to `∀ x, p x→ q x`. In order to do this, we mostly don't use the 
definitions in chapter 9 and develop a new way to interpret `∃` 
instead.
*)

Declare Scope single_app_impl.
Declare Scope single_app_equiv.

Notation " A -[ x : P ]> B " := (∀ (x : P), A → B)
  (at level 85, x name, right associativity,
  format " '[' A '/' '[ ' -[ x : P ]> ']' '/' B ']' ")
  : single_app_impl.

Open Scope single_app_impl.
Open Scope single_app_equiv.

Notation " A -[ x ]> B " := (( A -[ x : Prop ]> B ))
  (at level 80, x name, right associativity,
  format " A '/' '[ ' -[ x ]> ']' '/' B ")
  : single_app_impl.

Notation " A <[- x : P -]> B " := (∀ (x : P), A ↔ B)
  (at level 85, x name, right associativity,
  format " '[' A '/' '[ ' <[- x : P -]> ']' '/' B ']' ")
  : single_app_equiv.

Notation " A <[- x -]> B " := (A <[- x : Prop -]> B)
  (at level 80, x name, right associativity,
  format " A '/' '[ ' <[- x -]> ']' '/' B ")
  : single_app_equiv.

Definition n10_01 (φ : Prop → Prop) : 
  (∃ x, φ x) = ¬ (∀ x, ¬ φ x). Admitted.

Definition n10_02 (φ ψ : Prop → Prop) : 
  φ x -[ x ]> ψ x = ∀ x, φ x → ψ x. Admitted.

Definition n10_03 (φ ψ : Prop → Prop) : 
  φ x <[- x -]> ψ x = ∀ x, (φ x ↔ ψ x). Admitted.

Theorem n10_1 (φ : Prop → Prop) (Y : Prop) : (∀ x, φ x) → φ Y.
Proof.  exact (n9_2 φ Y). Qed.

(* Thm 10.11: If φ y is true whatever possible argument y may be, then ∀, φ x is true. [*9.13] *)
Theorem n10_11 (Y : Prop) (φ : Prop → Prop) : φ Y → ∀ x, φ x.
Proof.
Admitted.

Theorem n10_12 (φ : Prop → Prop) (P : Prop) : 
  (∀ x, P ∨ φ x) → P ∨ ∀ x, φ x.
Proof.  exact (n9_25 P φ). Qed.

(* Thm 10.121: If φ x is significant, then if a is of the same type as x, φ a is significant, and vice versa. [*9.14] *)

(* Thm 10.122: If for some a, there is a proposition φ a, then there is a function φ x^, and vice versa. [*9.15] *)

(* Thm 10.13: If φ x^ and ψ x^ takes arguments of the same type, and we have |- φ x and |- ψ x, we shall have |- φ x ∧ ψ x . *)
(* NOTE: we didn't enforce `is_same_type` so far. Currently I decide to just leave it manually specified *)
Theorem n10_13 (φ ψ : Prop → Prop) (X : Prop) :
  φ X → ψ X → (φ X ∧ ψ X).
Proof.
Admitted.

Theorem n10_14 (φ ψ : Prop → Prop) (Y : Prop) : 
  (∀ x, φ x) ∧ (∀ x, ψ x)
  → φ Y ∧ ψ Y.
Proof.
  pose proof (n10_1 φ Y) as S1.
  pose proof (n10_1 ψ Y) as S2.
  assert (S3 : ((∀ x, φ x) → φ Y) ∧ ((∀ x, ψ x) → ψ Y)).
  {
    pose proof (n10_13 (fun x => (∀ x, φ x) → φ Y) 
        (fun x => (∀ x, ψ x) → ψ Y) Y) as n10_13.
    MP n10_13 S1.
    MP n10_13 S2.
    exact n10_13. 
  }
  assert (S4 : ((∀ x, φ x) ∧ (∀ x, ψ x)) → (φ Y ∧ ψ Y)).
  {
    pose proof (n3_47 (∀ x, φ x) (∀ x, ψ x)
                (φ Y) (ψ Y)) as n3_47.
    MP n3_47 S3.
    exact n3_47.
  }
  exact S4.
Qed.

Theorem n10_2 (φ : Prop → Prop) (P : Prop) :
  (∀ x, P ∨ φ x) ↔ P ∨ (∀ x, φ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (P ∨ ∀ x, φ x) → P ∨ φ Y).
  {
    pose proof (n10_1 φ Y) as n10_1.
    pose proof (Sum1_6 P (∀ x, φ x) (φ Y)) as Sum1_6.
    MP Sum1_6 n10_1.
    exact Sum1_6.
  }
  assert (S2 : ∀ y, (P ∨ (∀ x, φ x) → P ∨ φ y)).
  {
    pose proof (n10_11 Y (fun y => (P ∨ ∀ x, φ x) → P ∨ φ y)) as n10_11.
    MP n10_11 S1.
    exact n10_11.
  }
  assert (S3 : (P ∨ (∀ x, φ x)) → (∀ y, P ∨ φ y)).
  {
    setoid_rewrite -> Impl1_01a in S2.
    pose proof (n10_12 (fun y => P ∨ φ y) (¬ (P ∨ ∀ x, φ x))) as n10_12.
    MP n10_12 S2.
    setoid_rewrite <- Impl1_01a in n10_12.
    exact n10_12.
  }
  assert (S4 : (∀ y, (P ∨ φ y)) → P ∨ (∀ x, φ x)).
  { exact (n10_12 φ P). }
  assert (S5 : (∀ x, P ∨ φ x) ↔ P ∨ (∀ x, φ x)).
  (* TODO: use `Equiv` for rigor *)
  { split; [exact S4 | exact S3]. }
  exact S5.
Qed.

Theorem n10_21 (φ : Prop → Prop) (P : Prop) :
  (∀ x, P → φ x) ↔ (P → (∀ x, φ x)).
Proof. 
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  pose proof (n10_2 φ (¬P)) as n10_2.
  repeat setoid_rewrite <- Impl1_01a in n10_2.
  exact n10_2.
Qed.

Theorem n10_22 (φ ψ : Prop → Prop) :
  (∀ x, φ x ∧ ψ x) ↔ (∀ x, φ x) ∧ (∀ x, ψ x).
Proof. 
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, φ x ∧ ψ x) → φ Y ∧ ψ Y).
  { exact (n10_1 (fun x => φ x ∧ ψ x) Y). }
  assert (S2 : (∀ x, φ x ∧ ψ x) → φ Y).
  { 
    pose proof (Simp3_26 (φ Y) (ψ Y)) as Simp3_26.
    Syll Simp3_26 S1 S2.
    exact S2.
  }
  assert (S3 : (∀ y, (∀ x, φ x ∧ ψ x) → φ y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, φ x ∧ ψ x) → φ y)) as n10_11.
    MP n10_11 S2.
    exact n10_11.
  }
  assert (S4 : (∀ x, φ x ∧ ψ x) → ∀ y, φ y).
  {
    destruct (n10_21 φ (∀ x, φ x ∧ ψ x)) as [n10_21l n10_21r].
    MP n10_21l S3.
    exact n10_21l.
  }
  assert (S5 : (∀ x, φ x ∧ ψ x) → ψ Y).
  {
    pose proof (Simp3_27 (φ Y) (ψ Y)) as Simp3_27.
    Syll Simp3_27 S1 S5.
    exact S5.
  }
  assert (S6 : (∀ y, (∀ x, φ x ∧ ψ x) → ψ y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, φ x ∧ ψ x) → ψ y)) as n10_11.
    MP n10_11 S5.
    exact n10_11.
  }
  assert (S7 : (∀ x, φ x ∧ ψ x) → ∀ y, ψ y).
  {
    destruct (n10_21 ψ (∀ x, φ x ∧ ψ x)) as [n10_21l n10_21r].
    MP n10_21l S6.
    exact n10_21l.
  }
  assert (S8 : (∀ x, φ x ∧ ψ x) → ((∀ y, φ y) ∧ ∀ z, ψ z)).
  {
    pose proof (Comp3_43 (∀ x, φ x ∧ ψ x) (∀ y, φ y) (∀ z, ψ z)) as Comp3_43.
    assert (C1 : ((∀ x, φ x ∧ ψ x) → ∀ y, φ y)
      ∧ ((∀ x, φ x ∧ ψ x) → ∀ y, ψ y)).
    { clear S1 S2 S3 S5 S6 Comp3_43. now Conj S4 S7 C1. }
    MP Comp3_43 C1.
    exact Comp3_43.
  }
  assert (S9 : ∀ y, (∀ x, φ x) ∧ (∀ x, ψ x) → (φ y ∧ ψ y)).
  {
    pose proof (n10_14 φ ψ Y) as n10_14.
    pose proof (n10_11 Y (fun y => 
      (∀ x, φ x) ∧ (∀ x, ψ x) → (φ y ∧ ψ y))) as n10_11.
    MP n10_11 n10_14.
    exact n10_11.
  }
  assert (S10 : (∀ x, φ x) ∧ (∀ x, ψ x) → ∀ y, (φ y ∧ ψ y)).
  {
    pose proof n10_21 as n10_21.
    pose proof (n10_21 (fun y => (φ y ∧ ψ y)) 
      ((∀ x, φ x) ∧ (∀ x, ψ x))) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l S9.
    exact n10_21l.
  }
  assert (S11 : (∀ x, φ x ∧ ψ x) ↔ (∀ x, φ x) ∧ (∀ x, ψ x)).
  {
    assert (C1 : ((∀ x, φ x ∧ ψ x) → ((∀ y, φ y) ∧ ∀ z, ψ z))
      ∧ ((∀ x, φ x) ∧ (∀ x, ψ x) → ∀ y, (φ y ∧ ψ y))).
    {
      clear S1 S2 S3 S4 S5 S6 S7 S9.
      now Conj S8 S10 C1.
    }
    Equiv C1.
    exact C1.
  }
  exact S11.
Qed.

(* Thm *10.221: omitted *)

Theorem n10_23 (φ : Prop → Prop) (P : Prop) :
  (∀ x, φ x → P) ↔ ((∃ x, φ x) → P).
Proof.
  assert (S1 : (∀ x, ¬ φ x ∨ P) ↔ ((∀ x, ¬ φ x) ∨ P)).
  {
    pose proof (n4_2 (∀ x, ¬ φ x ∨ P)) as n4_2.
    rewrite <- n9_03 in n4_2 at 2.
    exact n4_2.
  }
  assert (S2 : (∀ x, (¬ φ x) ∨ P) ↔ ((∃ x, φ x) → P)).
  {
    rewrite <- n9_02 in S1.
    rewrite <- Impl1_01 in S1.
    exact S1.
  }
  assert (S3 : (∀ x, φ x → P) ↔ ((∃ x, φ x) → P)).
  {
    set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
      as Impl1_01a.
    setoid_rewrite <- Impl1_01a in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n10_23_alt (φ : Prop → Prop) (P : Prop) :
  (∀ x, φ x → P) ↔ ((∃ x, φ x) → P).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((∃ x, φ x) → P) ↔ ((¬ P) → (∀ x, ¬ φ x))).
  {
    pose proof (Transp2_16 (∃ x, φ x) P) as Transp2_16.
    rewrite -> n10_01 in Transp2_16 at 2.
    (* This can be able to be broken down into nests of `Syll`s. See S9
      Here for simplicity we use `n2_14` at the very end of the proof *)
    replace (¬ ¬ ∀ x, ¬ φ x) with (∀ x, ¬ φ x)
      in Transp2_16.
    pose proof (Transp2_17 (∃ x, φ x) P) as Transp2_17.
    rewrite -> n10_01 in Transp2_17 at 1.
    replace (¬ ¬ ∀ x, ¬ φ x) with (∀ x, ¬ φ x)
      in Transp2_17.
    assert (C1 : (((∃ x, φ x) → P) → (¬ P → ∀ x, ¬ φ x))
      ∧ ((¬ P → ∀ x, ¬ φ x) → ((∃ x, φ x) → P))).
    { now Conj Transp2_16 Transp2_17 C1. }
    Equiv C1.
    exact C1.
    all: (
      apply propositional_extensionality;
      split; [ apply n2_12 | apply (n2_14 (∀ x, ¬ φ x)) ]
    ).
  }
  assert (S2 : ((∃ x, φ x) → P) ↔ (∀ x, ¬ P → ¬ φ x)).
  {
    (* For simplicity *)
    replace (¬ P → ∀ x, ¬ φ x) with (∀ x, ¬ P → ¬ φ x)
      in S1 by (apply propositional_extensionality; apply n10_21).
    exact S1.
  }
  (* WTF???? *)
  assert (S3 : ((∃ x, φ x) → P) → ((¬ P) → ¬ φ X)).
  {
    pose proof (n10_1 (fun x => (¬ P) → ¬ φ x) X) as n10_1.
    destruct S2 as [S2_l S2_r].
    Syll S2_l n10_1 S3.
    exact S3.
  }
  assert (S4 : ((∃ x, φ x) → P) → (φ X → P)).
  {
    pose proof (Transp2_17 (φ X) P) as Transp2_17.
    Syll S3 Transp2_17 S4.
    exact S4.
  }
  (* The variable naming here is so wild *)
  assert (S5 : ∀ x0, ((∃ x, φ x) → P) → (φ x0 → P)).
  {
    pose proof (n10_11 X (fun x0 => ((∃ x, φ x) → P) → (φ x0 → P))) 
      as n10_11.
    MP n10_11 S4.
    exact n10_11.
  }
  assert (S6 : ((∃ x, φ x) → P) → ∀ x, (φ x → P)).
  {
    pose proof (n10_21 (fun x0 => (φ x0 → P)) ((∃ x, φ x) → P))
      as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l S5.
    exact n10_21l.
  }
  assert (S7 : (∀ x, (φ x → P)) → (φ X → P)).
  { exact (n10_1 (fun x => φ x → P) X). }
  assert (S8 : (∀ x, (φ x → P)) → ((¬ P) → ¬ φ X)).
  {
    pose proof (Transp2_16 (φ X) P) as Transp2_16.
    Syll S7 Transp2_16 S8.
    exact S8.
  }
  assert (S9 : (∀ x, (φ x → P)) → (∀ x, (¬ P) → ¬ φ x)).
  {
    pose proof (n10_11 X (fun x => ¬ φ x)) as n10_11.
    assert (S8_1 : ((¬ P) → ¬ φ X) → ((¬ P) → ∀ x, (¬ φ x))).
    (* A demonstration of recursive `Syll`
    maybe there's even better and more natural way to handle this *)
    {
      intro.
      Syll H n10_11 H0.
      exact H0.
    }
    Syll S8 S8_1 S8_2.
    pose proof (n10_21 (fun x => ¬ φ x) (¬ P)) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    clear S1 S2 S3 S4 S5 S6 S7 n10_11 n10_21l S8 S8_1.
    Syll S8_2 n10_21r S9.
    exact S9.
  }
  assert (S10 : (∀ x, (φ x → P)) → (∃ x, φ x) → P).
  {
    destruct S2 as [S2_l S2_r].
    clear S1 S3 S4 S5 S6 S7 S8 S2_l.
    Syll S9 S2_r S10.
    exact S10.
  }
  assert (S11 : (∀ x, φ x → P) ↔ ((∃ x, φ x) → P)).
  {
    assert (C1 : ((∀ x, (φ x → P)) → (∃ x, φ x) → P)
      ∧ (((∃ x, φ x) → P) → ∀ x, (φ x → P))).
    {
      clear S1 S2 S3 S4 S5 S7 S8 S9.
      move S10 after S6.
      now Conj S10 S6 C1.
    }
    Equiv C1.
    exact C1.
  }
  exact S11.
Qed.

Theorem n10_24 (φ : Prop → Prop) (Y : Prop) :
  φ Y → ∃ x, φ x.
Proof.
  assert (S1 : (∀ x, ¬ φ x) → ¬ φ Y).
  { exact (n10_1 (fun x => ¬ φ x) Y). }
  assert (S2 : φ Y → (¬ ∀ x, ¬ φ x)).
  {
    pose proof (Transp2_03 (∀ x, ¬ φ x) (φ Y)) as Transp2_03.
    MP Transp2_03 S1.
    exact Transp2_03.
  }
  assert (S3 : φ Y → ∃ x, φ x).
  {
    rewrite <- n10_01 in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n10_25 (φ : Prop → Prop) : (∀ x, φ x) → (∃ x, φ x).
Proof.
  set (Y := Real "y").
  pose proof (n10_1 φ Y) as n10_1.
  pose proof (n10_24 φ Y) as n10_24.
  Syll n10_1 n10_24 S1.
  exact S1.
Qed.

Theorem n10_251 (φ : Prop → Prop) : (∀ x, ¬φ x) → ¬(∀ x, φ x).
Proof.
  pose proof (n10_25 φ) as n10_25.
  pose proof (Transp2_16 (∀ x, φ x) (∃ x, φ x)) 
    as Transp2_16.
  MP Transp2_16 n10_25.
  rewrite -> n10_01 in Transp2_16.
  pose proof (n2_12 ((∀ x, ¬ φ x))) as n2_12.
  Syll n2_12 Transp2_16 S1.
  exact S1.
Qed.

Theorem n10_252 (φ : Prop → Prop) : ¬(∃ x, φ x) ↔ (∀ x, ¬ φ x).
Proof.
  pose proof (n4_2 (∀ x, ¬ φ x)) as n4_2.
  rewrite <- n9_02 in n4_2 at 1.
  exact n4_2.
Qed.

Theorem n10_253 (φ : Prop → Prop) : ¬(∀ x, φ x) → (∃ x, ¬φ x).
Proof.
  pose proof (n4_2 (¬ ∀ x, φ x)) as n4_2.
  rewrite -> n9_01 in n4_2 at 2.
  destruct n4_2 as [n4_2l n4_2r].
  exact n4_2l.
Qed.

Theorem n10_252_alt (φ : Prop → Prop) : ¬(∃ x, φ x) ↔ (∀ x, ¬ φ x).
Proof.
  pose proof (n4_13 (∀ x, ¬ φ x)) as n4_13.
  rewrite <- n10_01 in n4_13 at 1.
  symmetry in n4_13.
  exact n4_13.
Qed.

Theorem n10_253_alt (φ : Prop → Prop) : (¬(∀ x, φ x)) ↔ (∃ x, ¬φ x).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (∀ x, φ x) → φ Y).
  { exact (n10_1 φ Y). }
  assert (S2 : (∀ x, φ x) → ¬ ¬ φ Y).
  {
    pose proof (n2_12 (φ Y)) as n2_12.
    Syll S1 n2_12 S2.
    exact S2.
  }
  assert (S3 : (∀ x, φ x) → ∀ y, ¬ ¬ φ y).
  {
    (* n10_21 is unused *)
    pose proof (n10_11 Y (fun y => ¬¬ φ y)) as n10_11.
    Syll S2 n10_21 S3.
    exact S3.
  }
  assert (S4 : (¬(∀ y, ¬ ¬ φ y)) → ¬(∀ x, φ x)).
  {
    pose proof (Transp2_16 (∀ x, φ x) (∀ y, ¬ ¬ φ y)) as Transp2_16.
    MP Transp2_16 S3.
    exact Transp2_16.
  }
  assert (S5 : (∃ y, ¬ φ y) → ¬(∀ x, φ x)).
  {
    rewrite <- n10_01 in S4.
    exact S4.
  }
  assert (S6 : (∀ y, ¬ ¬ φ y) → ¬ ¬ φ X).
  {
    exact (n10_1 (fun x => ¬ ¬ φ x) X).
  }
  assert (S7 : (∀ y, ¬ ¬ φ y) → φ X).
  {
    pose proof (n2_14 (φ X)) as n2_14.
    Syll S6 n2_14 S7.
    exact S7.
  }
  assert (S8 : (∀ y, ¬ ¬ φ y) → (∀ x, φ x)).
  {
    (* n10_21 is ignored *)
    pose proof (n10_11 X φ) as n10_11.
    Syll S7 n10_11 S8.
    exact S8.
  }
  assert (S9 : (¬(∀ x, φ x)) → ¬(∀ y, ¬ ¬ φ y)).
  {
    pose proof (Transp2_16  (∀ y, ¬ ¬ φ y) (∀ x, φ x)) as Transp2_16.
    MP Transp2_16 S8.
    exact Transp2_16.
  }
  assert (S10 : (¬(∀ x, φ x)) → ∃ y, ¬(φ y)).
  {
    rewrite <- n10_01 in S9.
    exact S9.
  }
  assert (S11 : (¬(∀ x, φ x)) ↔ ∃ x, ¬ φ x).
  {
    assert (C1 : ((¬(∀ x, φ x)) → ∃ x, ¬ φ x)
      ∧ ((∃ x, ¬ φ x) → ¬(∀ x, φ x))).
    {
      clear S1 S2 S3 S4 S6 S7 S8 S9.
      move S10 after S5.
      now Conj S10 S5 C1.
    }
    Equiv C1.
    exact C1.
  }
  exact S11.
Qed.

(* Barbara's syllogism 1st form *)
Theorem n10_26 (φ ψ : Prop → Prop) (X : Prop) : 
  ((∀ z, φ z → ψ z) ∧ φ X) → ψ X.
Proof.
  pose proof (n10_1 (fun z => φ z → ψ z) X) as n10_1.
  pose proof (Imp3_31 (∀ z, φ z → ψ z) (φ X) (ψ X)) as Imp3_31.
  MP Imp3_31 n10_1.
  exact Imp3_31.
Qed.

Theorem n10_27 (φ ψ : Prop → Prop) : 
  (∀ z, φ z → ψ z) → ((∀ z, φ z) → (∀ z, ψ z)).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : ((∀ z, φ z → ψ z) ∧ (∀ z, φ z)) → ((φ Y → ψ Y) ∧ φ Y)).
  { exact (n10_14 (fun z => φ z → ψ z) φ Y). }
  assert (S2 : ((∀ z, φ z → ψ z) ∧ (∀ z, φ z)) → ψ Y).
  {
    pose proof (Ass3_35 (φ Y) (ψ Y)) as Ass3_35.
    pose proof (n3_22 (φ Y → ψ Y) (φ Y)) as n3_22.
    Syll n3_22 Ass3_35 S2.
    clear n3_22.
    Syll S1 S2 S2_1.
    exact S2_1.
  }
  assert (S3 : ∀ y, ((∀ z, φ z → ψ z) ∧ (∀ z, φ z)) → ψ y).
  {
    (* Original text uses n10_1 and I think its a typo *)
    pose proof (n10_11 Y (fun y => (((∀ z, φ z → ψ z) ∧ (∀ z, φ z)) 
        → ψ y))) as n10_11.
    MP n10_11 S2.
    exact n10_11.
  }
  assert (S4 : ((∀ z, φ z → ψ z) ∧ (∀ z, φ z)) → ∀ y, ψ y).
  {
    pose proof (n10_21 ψ ((∀ z, φ z → ψ z) ∧ (∀ z, φ z))) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l S3.
    exact n10_21l.
  }
  assert (S5 : (∀ z, φ z → ψ z) → ((∀ z, φ z) → (∀ z, ψ z))). 
  {
    pose proof (Exp3_3 (∀ z, φ z → ψ z) (∀ z, φ z) (∀ y, ψ y))
       as Exp3_3.
    MP Exp3_3 S4.
    exact Exp3_3.
  }
  exact S5.
Qed.

Theorem n10_271 (φ ψ : Prop → Prop) : 
  (∀ z, φ z ↔ ψ z) → ((∀ z, φ z) ↔ (∀ z, ψ z)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  (* ******** *)
  (* Whenever a proof involves `Hp`, this proof becomes a little special. 
    It seems that all deductions are given the context to only deduce with
    `Hp` being introduced, as followed... *)
  pose proof (n10_22 (fun z => φ z → ψ z) (fun z => ψ z → φ z)) 
    as n10_22.
  simpl in n10_22.
  setoid_rewrite <- Equiv4_01a in n10_22.
  destruct n10_22 as [n10_22l n10_22r].
  clear n10_22r.
  assert (S1 : (∀ z, φ z ↔ ψ z) → (∀ z, φ z → ψ z)).
  {
    pose proof (Simp3_26 (∀ x, φ x → ψ x) (∀ x, ψ x → φ x)) 
      as Simp3_26.
    Syll n10_22l Simp3_26 S1.
    exact S1.
  }
  assert (S2 : (∀ z, φ z ↔ ψ z) → ((∀ z, φ z) → (∀ z, ψ z))).
  {
    (* `Hp` always have to be after the line where `Hp` is declared. All
      theorems involved are suppose proof proofd to be match directly on the conclusion 
      part of the proposition, with `Hp` removed from the goal.
      This isn't something breaking the rule, as we can always proceed with 
      `Syll`s. But I think a slight intro of `Hp` adds a tiny spice aligned 
      with original proof, without harming it too much *)
    intro Hp.
    pose proof (n10_27 φ ψ) as n10_27.
    pose proof (S1 Hp) as S1_1.
    MP n10_27 S1_1.
    exact n10_27.
  }
  assert (S3 : (∀ z, φ z ↔ ψ z) → (∀ z, ψ z → φ z)).
  {
    pose proof (Simp3_27 (∀ x, φ x → ψ x) (∀ x, ψ x → φ x)) 
      as Simp3_27.
    Syll n10_22l Simp3_27 S3.
    exact S3.
  }
  assert (S4 : (∀ z, φ z ↔ ψ z) → ((∀ z, ψ z) → (∀ z, φ z))).
  {
    intro Hp.
    pose proof (n10_27 ψ φ) as n10_27.
    pose proof (S3 Hp) as S3_1.
    MP n10_27 S3_1.
    exact n10_27.
  }
  assert (S5 : (∀ z, φ z ↔ ψ z) → ((∀ z, φ z) ↔ (∀ z, ψ z))).
  {
    assert (C1 : ((∀ z, φ z ↔ ψ z) → ((∀ z, φ z) → (∀ z, ψ z)))
      ∧ ((∀ z, φ z ↔ ψ z) → ((∀ z, ψ z) → (∀ z, φ z)))).
    { clear n10_22l S1 S3. now Conj S2 S4 C1. }
    pose proof (Comp3_43 (∀ z, φ z ↔ ψ z)
      ((∀ z, φ z) → (∀ z, ψ z))
      ((∀ z, ψ z) → (∀ z, φ z))
    ) as Comp3_43.
    MP Comp3_43 C1.
    rewrite <- Equiv4_01 in Comp3_43.
    exact Comp3_43.
  }
  exact S5.
Qed.

Theorem n10_28 (φ ψ : Prop → Prop) :
  (∀ x, φ x → ψ x) → ((∃ x, φ x) → (∃ x, ψ x)).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, φ x → ψ x) → (φ Y → ψ Y)).
  { exact (n10_1 (fun x => φ x → ψ x) Y). }
  assert (S2 : (∀ x, φ x → ψ x) → ((¬ψ Y) → (¬φ Y))).
  {
    pose proof (Transp2_16 (φ Y) (ψ Y)) as Transp2_16.
    Syll S1 Transp2_16 S2.
    exact S2.
  }
  assert (S3 : (∀ x, φ x → ψ x) → ∀ y, (¬ψ y) → (¬φ y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, φ x → ψ x) 
      → ((¬ψ y) → (¬φ y)))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_21 (fun y => (¬ψ y) → (¬φ y)) ((∀ x, φ x → ψ x)))
      as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l n10_11.
    exact n10_21l.
  }
  assert (S4 : (∀ x, φ x → ψ x) → ((∀ y, ¬ ψ y) → (∀ y, ¬ φ y))).
  {
    pose proof (n10_27 (fun y => ¬ ψ y) (fun y => ¬ φ y)) as n10_27.
    Syll S3 n10_27 S4.
    exact S4.
  }
  assert (S5 : (∀ x, φ x → ψ x) → ((∃ y, φ y) → (∃ y, ψ y))).
  {
    pose proof (Transp2_16 (∀ y, ¬ ψ y) (∀ y, ¬ φ y)) as Transp2_16.
    Syll S4 Transp2_16 S5.
    repeat rewrite <- n10_01 in S5.
    exact S5.
  }
  exact S5.
Qed.

(* Perhaps the most horrible concentration of proof I have ever seen *)
Theorem n10_281 (φ ψ : Prop → Prop) :
  (∀ x, φ x ↔ ψ x) → ((∃ x, φ x) ↔ (∃ x, ψ x)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  (* ******** *)
  pose proof (n10_22 (fun x => φ x → ψ x) (fun x => ψ x → φ x))
    as n10_22.
  destruct n10_22 as [n10_22l n10_22r].
  setoid_rewrite <- Equiv4_01a in n10_22l.
  assert (Sa : (∀ x, φ x ↔ ψ x) → 
    (∃ x, φ x) → (∃ x, ψ x)).
  {
    pose proof (Simp3_26 (∀ x, φ x → ψ x) (∀ x, ψ x → φ x))
      as Simp3_26.
    Syll n10_22l Simp3_26 n10_22l1.
    pose proof (n10_28 φ ψ) as n10_28a.
    Syll n10_22l1 n10_28a Sa.
    exact Sa.
  }
  assert (Sb : (∀ x, φ x ↔ ψ x) → 
    (∃ x, ψ x) → (∃ x, φ x)).
  {
    pose proof (Simp3_27 (∀ x, φ x → ψ x) (∀ x, ψ x → φ x))
      as Simp3_27.
    Syll n10_22l Simp3_27 n10_22l2.
    pose proof (n10_28 ψ φ) as n10_28b.
    Syll n10_22l2 n10_28b Sb.
    exact Sb.
  }
  pose proof (Comp3_43 (∀ x, φ x ↔ ψ x)
    ((∃ x, φ x) → (∃ x, ψ x))
    ((∃ x, ψ x) → (∃ x, φ x))
  ) as Comp3_43.
  assert (C1 : ((∀ x, φ x ↔ ψ x) → (∃ x, φ x) → (∃ x, ψ x))
    ∧ ((∀ x, φ x ↔ ψ x) → (∃ x, ψ x) → (∃ x, φ x))).
  {
    clear Equiv4_01a n10_22l n10_22r Comp3_43.
    now Conj Sa Sb C1.
  }
  MP Comp3_43 C1.
  Syll n10_22l Comp3_43 Sc.
  setoid_rewrite <- Equiv4_01a in Sc.
  Syll n10_22l Sc Sd.
  exact Sd.
Qed.

Theorem n10_29 (φ ψ χ : Prop → Prop) :
  ((∀ x, φ x → ψ x) ∧ (∀ x, φ x → χ x)) ↔ (∀ x, φ x → (ψ x ∧ χ x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((∀ x, φ x → ψ x) ∧ (∀ x, φ x → χ x)) 
    ↔ (∀ x, (φ x → ψ x) ∧ (φ x → χ x))).
  {
    pose proof (n10_22 (fun x => φ x → ψ x) 
      (fun x => φ x → χ x)) as n10_22.
    simpl in n10_22.
    symmetry in n10_22.
    exact n10_22.
  }
  assert (S2 : ((φ X → ψ X) ∧ (φ X → χ X)) 
    ↔ (φ X → (ψ X ∧ χ X))).
  { exact (n4_76 (φ X) (ψ X) (χ X)). }
  assert (S3 : ∀ x, ((φ x → ψ x) ∧ (φ x → χ x)) 
    ↔ (φ x → (ψ x ∧ χ x))).
  {
    pose proof (n10_11 X (fun x => ((φ x → ψ x) ∧ (φ x → χ x)) 
      ↔ (φ x → (ψ x ∧ χ x)))) as n10_11.
    MP n10_11 S3.
    exact n10_11.
  }
  assert (S4 : (∀ x, (φ x → ψ x) ∧ (φ x → χ x))
    ↔ (∀ x, φ x → (ψ x ∧ χ x))).
  {
    pose proof (n10_271
      (fun x => (φ x → ψ x) ∧ (φ x → χ x))
      (fun x => φ x → (ψ x ∧ χ x))
    ) as n10_271.
    MP n10_271 S3.
    exact n10_271.
  }
  assert (S5 : ((∀ x, φ x → ψ x) ∧ (∀ x, φ x → χ x)) ↔ (∀ x, φ x → (ψ x ∧ χ x))).
  {
    assert (C1 : 
      (((∀ x, φ x → ψ x) ∧ (∀ x, φ x → χ x)) 
        ↔ (∀ x, (φ x → ψ x) ∧ (φ x → χ x)))
      ∧ ((∀ x, (φ x → ψ x) ∧ (φ x → χ x))
         ↔ (∀ x, φ x → (ψ x ∧ χ x)))).
    { clear S2 S3. now Conj S1 S4 C1. }
    pose proof (n4_22
      ((∀ x, φ x → ψ x) ∧ (∀ x, φ x → χ x))
      (∀ x, (φ x → ψ x) ∧ (φ x → χ x))
      (∀ x, φ x → (ψ x ∧ χ x))
    ) as n4_22.
    MP n4_22 C1.
    exact n4_22.
  }
  exact S5.
Qed.

(* Barbara's syllogism 2nd form *)

Theorem n10_3 (φ ψ χ : Prop → Prop) :
  ((∀ x, φ x → ψ x) ∧ (∀ x, ψ x → χ x)) → ∀ x, φ x → χ x.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (n10_22 (fun x => φ x → ψ x) (fun x => ψ x → χ x)) 
    as n10_22a.
  assert (S1 : ((∀ x, φ x → ψ x) ∧ (∀ x, ψ x → χ x))
    → ∀ x, (φ x → ψ x) ∧ (ψ x → χ x)).
  {
    (* n10_221 ignored *)
    destruct n10_22a as [n10_22l n10_22r].
    exact n10_22r.
  }
  assert (S2 : ((∀ x, φ x → ψ x) ∧ (∀ x, ψ x → χ x))
    → ∀ x, (φ x → χ x)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    (* Original proof here has abbreviated a lot of proofs being explained separately *)
    (* Note how the original proof here introduces a real variable *)
    assert (Sy1 : (φ X → ψ X) ∧ (ψ X → χ X) → (φ X → χ X)).
    {
      pose proof (Syll2_06 (φ X) (ψ X) (χ X)) as Syll2_06.
      pose proof (Imp3_31 (φ X → ψ X) (ψ X → χ X) 
        (φ X → χ X)) as Imp3_31.
      MP Imp3_31 Syll2_06.
      exact Imp3_31.
    }
    assert (Sy2 : ∀ x, (φ x → ψ x) ∧ (ψ x → χ x) → (φ x → χ x)).
    {
      pose proof (n10_11 X (fun x => (φ x → ψ x) 
        ∧ (ψ x → χ x) → (φ x → χ x))) as n10_11.
      MP n10_11 Sy1.
      exact n10_11.
    }
    assert (Sy3 : (∀ x, (φ x → ψ x) ∧ (ψ x → χ x)) 
      → (∀ y, φ y → χ y)).
    {
      pose proof (n10_27 (fun x => (φ x → ψ x) ∧ (ψ x → χ x))
        (fun x => (φ x → χ x))) as n10_27.
      MP n10_27 Sy2.
      exact n10_27.
    }
    MP Sy3 S1_1.
    exact Sy3.
  }
  exact S2.
Qed.

Theorem n10_301 (φ ψ χ : Prop → Prop) :
  (∀ x, φ x ↔ ψ x) ∧ (∀ x, ψ x ↔ χ x) → ∀ x, φ x ↔ χ x.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (n10_22 (fun x => φ x ↔ ψ x) (fun x => ψ x ↔ χ x))
    as S1.
  simpl in S1.
  assert (S2 : (∀ x, φ x ↔ ψ x) ∧ (∀ x, ψ x ↔ χ x) → ∀ x, φ x ↔ χ x).
  {
    pose proof (n4_22 (φ X) (ψ X) (χ X)) as n4_22.
    pose proof (n10_11 X
      (fun x => ((φ x ↔ ψ x) ∧ (ψ x ↔ χ x)) 
        → (φ x ↔ χ x))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27
      (fun x => (φ x ↔ ψ x) ∧ (ψ x ↔ χ x))
      (fun x => (φ x ↔ χ x))) as n10_27.
    MP n10_27 n10_11.
    pose proof (n10_22 (fun x => (φ x ↔ ψ x))
      (fun x => (ψ x ↔ χ x))) as n10_22.
    simpl in n10_22.
    destruct n10_22 as [n10_22l n10_22r].
    clear S1 n4_22 n10_11 n10_22l.
    Syll n10_22r n10_27 S2.
    exact S2.
  }
  exact S2.
Qed.

Theorem n10_31 (φ ψ χ : Prop → Prop) :
  (∀ x, φ x → ψ x) → (∀ x, (φ x ∧ χ x) → (ψ x ∧ χ x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ∀ x, (φ x → ψ x) 
    → (φ x ∧ χ x) → (ψ x ∧ χ x)).
  {
    pose proof (Fact3_45 (φ X) (ψ X) (χ X)) as Fact3_45.
    pose proof (n10_11 X (fun x => (φ x → ψ x) 
      → (φ x ∧ χ x) → (ψ x ∧ χ x))) as n10_11.
    MP n10_11 Fact3_45.
    exact n10_11.
  }
  assert (S2 : (∀ x, φ x → ψ x) → (∀ x, (φ x ∧ χ x) → (ψ x ∧ χ x))).
  {
    pose proof (n10_27 (fun x => φ x → ψ x)
      (fun x => (φ x ∧ χ x) → (ψ x ∧ χ x))) as n10_27.
    MP n10_27 S1.
    exact n10_27.
  }
  exact S2.
Qed.

Theorem n10_311 (φ ψ χ : Prop → Prop) :
  (∀ x, φ x ↔ ψ x) → (∀ x, (φ x ∧ χ x) ↔ (ψ x ∧ χ x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ∀ x, (φ x ↔ ψ x) → ((φ x ∧ χ x) ↔ (ψ x ∧ χ x))).
  {
    pose proof (n4_36 (φ X) (ψ X) (χ X)) as n4_36.
    pose proof (n10_11 X (fun x => (φ x ↔ ψ x) 
      → ((φ x ∧ χ x) ↔ (ψ x ∧ χ x)))) as n10_11.
    MP n10_11 n4_36.
    exact n10_11.
  }
  assert (S2 : (∀ x, φ x ↔ ψ x) → (∀ x, (φ x ∧ χ x) ↔ (ψ x ∧ χ x))).
  {
    pose proof (n10_27 (fun x => φ x ↔ ψ x)
      (fun x => (φ x ∧ χ x) ↔ (ψ x ∧ χ x))) as n10_27.
    MP S1 n10_27.
    exact n10_27.
  }
  exact S2.
Qed.

Theorem n10_32 (φ ψ : Prop → Prop) :
  (φ x <[- x -]> ψ x) ↔ (ψ x <[- x -]> φ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)))
    as Equiv4_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((φ x) <[- x -]> (ψ x)) ↔ 
    ((φ x -[ x ]> ψ x) ∧ (ψ x -[ x ]> φ x))).
  {
    pose proof (n10_22
      (fun x => (φ x → ψ x))
      (fun x => (ψ x → φ x))) as n10_22.
    simpl in n10_22.
    setoid_rewrite <- Equiv4_01a in n10_22.
    2: { apply Equiv4_01. }
    exact n10_22.
  }
  assert (S2 : ((φ x) <[-x-]> (ψ x)) ↔ 
    ((ψ x -[x]> φ x) ∧ (φ x -[x]> ψ x))).
  {
    pose proof (n4_3 ((φ x) -[x]> (ψ x)) ((ψ x) -[x]> (φ x))) 
      as n4_3.
    assert (C1 : ((φ x <[- x -]> ψ x) ↔ 
      ((φ x -[x]> ψ x) ∧ (ψ x -[x]> φ x)))
      ∧
      ((φ x -[x]> ψ x) ∧ ψ x -[x]> φ x ↔ 
      (ψ x -[x]> φ x) ∧ φ x -[x]> ψ x)).
    { now Conj S1 n4_3 C1. }
    pose proof (n4_22
      ((φ x) <[- x -]> (ψ x))
      (((φ x) -[x]> (ψ x)) ∧ ((ψ x) -[x]> (φ x)))
      (((ψ x) -[x]> (φ x)) ∧ ((φ x) -[x]> (ψ x)))
    ) as n4_22.
    MP n4_22 C1.
    exact n4_22.
  }
  assert (S3 : ((φ x) <[- x -]> (ψ x)) ↔ 
    ((ψ x) <[- x -]> (φ x))).
  {
    pose proof (n10_22 
      (fun x => (ψ x → φ x))
      (fun x => (φ x → ψ x))) as n10_22. 
    symmetry in n10_22.
    simpl in n10_22.
    assert (C1 : ((φ x <[- x -]> ψ x) 
        ↔ ((ψ x -[x]> φ x) ∧ (φ x -[x]> ψ x)))
      ∧
      (((ψ x -[x]> φ x) ∧ (φ x -[x]> ψ x)) 
        ↔ ∀ x, (ψ x → φ x) ∧ (φ x → ψ x))).
    { now Conj S2 n10_22 C1. }
    pose proof (n4_22
      (φ x <[- x -]> ψ x)
      ((ψ x -[x]> φ x) ∧ (φ x -[x]> ψ x))
      (∀ x, (ψ x → φ x) ∧ (φ x → ψ x))
    ) as n4_22.
    MP n4_22 C1.
    setoid_rewrite <- Equiv4_01a in n4_22.
    2: { apply Equiv4_01. }
    exact n4_22.
  }
  exact S3.
Qed.

Theorem n10_321 (φ ψ χ : Prop → Prop) :
  ((φ x <[- x -]> ψ x) ∧ (φ x <[- x -]> χ x)) 
  → (ψ x <[- x -]> χ x).
Proof.
  assert (S1 : ((φ x <[- x -]> ψ x) ∧ (φ x <[- x -]> χ x))
    → ((ψ x <[- x -]> φ x) ∧ (φ x <[- x -]> χ x))).
  {
    pose proof (n10_32 φ ψ) as n10_32.
    destruct n10_32 as [n10_32l n10_32r].
    pose proof (Fact3_45 (φ x<[-x-]>ψ x) (ψ x<[-x-]>φ x)
      (φ x <[- x -]> χ x))as Fact3_45.
    clear n10_32r.
    MP Fact3_45 n10_32l.
    exact Fact3_45.
  }
  assert (S2 : ((φ x <[- x -]> ψ x) ∧ (φ x <[- x -]> χ x)) 
    → (ψ x <[- x -]> χ x)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    pose proof (n10_301 ψ φ χ) as n10_301.
    MP n10_301 S1_1.
    exact n10_301.
  }
  exact S2.
Qed.

Theorem n10_322 (φ ψ χ : Prop → Prop) :
  ((ψ x <[- x -]> φ x) ∧ (χ x <[- x -]> φ x)) 
  → (ψ x <[- x -]> χ x).
Proof.
  assert (S1 : ((ψ x <[- x -]> φ x) ∧ (χ x <[- x -]> φ x))
    → ((ψ x <[- x -]> φ x) ∧ (φ x <[- x -]> χ x))).
  {
    intro Hp.
    pose proof (n10_32 χ φ) as n10_32.
    (* Here we simplify the proof and omit related theorems. We directly use 
    `rewrite` for a `↔` relation, while strictly speaking it's only allowed
    for `=` relations. *)
    rewrite -> n10_32 in Hp.
    exact Hp.
  }
  assert (S2 : ((ψ x <[- x -]> φ x) ∧ (χ x <[- x -]> φ x))
    → (ψ x <[- x -]> χ x)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    pose proof (n10_301 ψ φ χ) as n10_301.
    MP n10_301 S1_1.
    exact n10_301.
  }
  exact S2.
Qed.

Theorem n10_33 (φ : Prop → Prop) (P : Prop) :
  (∀ x, φ x ∧ P) ↔ ((∀ x, φ x) ∧ P).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, φ x ∧ P) → (φ Y ∧ P)).
  {
    pose proof (n10_1 (fun x => φ x ∧ P) Y) as n10_1.
    exact n10_1.
  }
  assert (S2 : (∀ x, φ x ∧ P) → P).
  {
    pose proof (Simp3_27 (φ Y) P) as Simp3_27.
    Syll S1 Simp3_27 S2.
    exact S2.
  }
  assert (S3 : (∀ x, φ x ∧ P) → φ Y).
  { 
    pose proof (Simp3_26 (φ Y) P) as Simp3_26.
    Syll S1 Simp3_26 S3.
    exact S3.
  }
  assert (S4 : (∀ x, φ x ∧ P) → (∀ y, φ y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, φ x ∧ P) → φ y)) as n10_11.
    MP n10_11 S3.
    pose proof (n10_21 φ (∀ x, φ x ∧ P)) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    clear n10_21r.
    MP n10_21l n10_11.
    exact n10_21l.
  }
  assert (S5 : (∀ x, φ x ∧ P) → (∀ y, φ y) ∧ P).
  {
    (* Original text here seems unsatisfying in a sense of rigor *)
    assert (C1 : ((∀ x, φ x ∧ P) → ∀ y, φ y)
      ∧ ((∀ x, φ x ∧ P) → P)).
    {
      clear S1 S3.
      move S2 after S4.
      now Conj S4 S2 C1.
    }
    pose proof (n4_76 (∀ x, φ x ∧ P) (∀ y, φ y) P) as n4_76.
    destruct n4_76 as [n4_76l n4_76r].
    clear n4_76r.
    MP n4_76l C1.
    exact n4_76l.
  }
  assert (S6 : (∀ y, φ y) → φ X).
  { now apply n10_1. }
  assert (S7 : ((∀ y, φ y) ∧ P) → (φ X ∧ P)).
  {
    pose proof (Fact3_45 (∀ y, φ y) (φ X) P) as Fact3_45.
    now MP Fact3_45 S6.
  }
  (* Is it that we don't have alpha equivalence in this logic system?! *)
  assert (S8 : ((∀ y, φ y) ∧ P) → ∀ x, φ x ∧ P).
  {
    pose proof n10_11 as n10_11.
    pose proof n10_21 as n10_21.
    pose proof (n10_11 X (fun x => (∀ y, φ y) ∧ P 
      → φ x ∧ P)) as n10_11.
    MP n10_11 S7.
    pose proof (n10_21 (fun x => φ x ∧ P) ((∀ y, φ y) ∧ P)) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    clear n10_21r.
    now MP n10_21l n10_11.
  }
  assert (S9 : (∀ x, φ x ∧ P) ↔ ((∀ x, φ x) ∧ P)).
  {
    clear S1 S2 S3 S4 S6 S7.
    move S5 after S8.
    Conj S8 S5 S9.
    now Equiv S9.
  }
  exact S9.
Qed.

Theorem n10_34 (φ : Prop → Prop) (P : Prop) :
  (∃ x, φ x → P) ↔ ((∀ x, φ x) → P).
Proof.
  assert (S1 : (∃ x, φ x → P) ↔ ¬(∀ x, ¬(φ x → P))).
  {
    pose proof (n4_2 (∃ x, φ x → P)) as n4_2.
    now rewrite -> n10_01 in n4_2 at 2.
  }
  assert (S2 : (∃ x, φ x → P) ↔ ¬(∀ x, φ x ∧ ¬P)).
  {
    (* n10_271 ignored - idk how should it be used *)
    now setoid_rewrite -> n4_61 in S1.
  }
  assert (S3 : (∃ x, φ x → P) ↔ ¬((∀ x, φ x) ∧ ¬P)).
  {
    (* In rigorous sense we should somehow use transitivity on equiv relation,
     or MP then compose proof back  *)
    now rewrite -> n10_33 in S2.
  }
  assert (S4 : (∃ x, φ x → P) ↔ (¬∀ x, φ x) ∨ P).
  { now setoid_rewrite -> n4_53 in S3. }
  assert (S5 : (∃ x, φ x → P) ↔ ((∀ x, φ x ) → P)).
  { now setoid_rewrite <- n4_6 in S4. }
  exact S5.
Qed.

Theorem n10_35 (φ : Prop → Prop) (P : Prop) :
  (∃ x, P ∧ φ x) ↔ P ∧ (∃ x, φ x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (P ∧ φ X) → P).
  { exact (Simp3_26 P (φ X)). }
  assert (S2 : ∀ x, (P ∧ φ x) → P).
  {
    pose proof (n10_11 X (fun x => ((P ∧ φ x) → P))) as n10_11.
    now MP n10_11 S1.
  }
  assert (S3 : (∃ x, (P ∧ φ x)) → P).
  {
    (* pose proof n10_23 as n10_23. *)
    pose proof (n10_23 (fun x => P ∧ φ x) P) as n10_23.
    simpl in n10_23.
    (* omit the MP we should use *)
    now rewrite -> n10_23 in S2.
  }
  assert (S4 : (P ∧ φ X) → (φ X)).
  { exact (Simp3_27 P (φ X)). }
  assert (S5 : ∀ x, (P ∧ φ x) → φ x).
  {
    pose proof (n10_11 X (fun x => ((P ∧ φ x) → φ x))) as n10_11.
    now MP n10_11 S4.
  }
  assert (S6 : (∃ x, P ∧ φ x) → (∃ x, φ x)).
  {
    pose proof (n10_28 (fun x => P ∧ φ x) φ) as n10_28.
    now MP n10_28 S5.
  }
  assert (S7 : P → (φ X → (P ∧ φ X))).
  { exact (n3_2 P (φ X)). }
  assert (S8 : P → (∀ x, φ x → (P ∧ φ x))).
  {
    pose proof (n10_11 X (fun x => φ x → (P ∧ φ x))) as n10_11.
    simpl in n10_11.
    Syll n10_11 S7 S8.
    (* n10_21 ignored - the difference isn't significant *)
    exact S8.
  }
  assert (S9 : P → ((∃ x, φ x) → (∃ x, P ∧ φ x))).
  {
    pose proof (n10_28 φ (fun x => P ∧ φ x)) as n10_28.
    now Syll n10_28 S8 S9.
  }
  assert (S10 : (∃ x, P ∧ φ x) ↔ P ∧ (∃ x, φ x)).
  {
    clear S1 S2 S4 S5 S7 S8.
    pose proof (Imp3_31 P ((∃ x, φ x)) (∃ x, P ∧ φ x))
      as Imp3_31.
    MP Imp3_31 S9.
    assert (C1 : ((∃ x, P ∧ φ x) → P) 
      ∧ ((∃ x, P ∧ φ x) → ∃ x, φ x)).
    { now Conj S3 S6 C1. }
    pose proof (Comp3_43 (∃ x, P ∧ φ x) P (∃ x, φ x))
      as Comp3_43.
    MP Comp3_43 C1.
    assert (C2 : ((∃ x, P ∧ φ x) → P ∧ ∃ x, φ x)
      ∧ (P ∧ (∃ x, φ x) → ∃ x, P ∧ φ x)).
    { now Conj Comp3_43 Imp3_31 C2. }
    now Equiv C2.
  }
  exact S10.
Qed.

Theorem n10_36 (φ : Prop → Prop) (P : Prop) :
  (∃ x, φ x ∨ P) ↔ (∃ x, φ x) ∨ P.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (φ X ∨ P) ↔ ((¬φ X) → P)).
  {
    pose proof (n4_64 (φ X) P) as n4_64.
    now symmetry in n4_64.
  }
  assert (S2 : ∀ x, (φ x ∨ P) ↔ ((¬φ x) → P)).
  {
    pose proof (n10_11 X (fun x => (φ x ∨ P) ↔ ((¬φ x) → P))) 
      as n10_11.
    now MP n10_11 S1.
  }
  assert (S3 : (∃ x, φ x ∨ P) ↔ (∃ x, (¬φ x) → P)).
  {
    pose proof (n10_281 (fun x => φ x ∨ P) (fun x => (¬φ x) → P)) 
      as n10_281.
    now MP n10_281 S2.
  }
  assert (S4 : (∃ x, φ x ∨ P) ↔ ((∀ x, ¬φ x) → P)).
  {
    (* Same as previous attempts, here we directly use `rewrite` rather than
    going on all the decomposing and recomposing *)
    now rewrite -> n10_34 in S3.
  }
  assert (S5 : (∃ x, φ x ∨ P) ↔ ((∃ x, φ x) ∨ P)).
  {
    rewrite -> n4_6 in S4.
    rewrite <- n10_01 in S4.
    exact S4.
  }
  exact S5.
Qed.

Theorem n10_37 (φ : Prop → Prop) (P : Prop) :
  (∃ x, P → φ x) ↔ (P → ∃ x, φ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n10_36 φ (¬P)) as n10_36.
  rewrite -> n4_31 in n10_36.
  rewrite <- Impl1_01 in n10_36.
  replace (∃ x, φ x ∨ ¬ P) with 
    (∃ x, ¬ P ∨ φ x) in n10_36.
  2: {
    apply propositional_extensionality.
    split; now setoid_rewrite -> n4_31 at 1.
  }
  now setoid_rewrite <- Impl1_01a in n10_36.
Qed.

Theorem n10_39 (φ ψ χ θ : Prop → Prop) :
  ((φ x -[ x ]> χ x) ∧ (ψ x -[ x ]> θ x)) 
  → (φ x ∧ ψ x) -[ x ]> (χ x ∧ θ x).
Proof.
  assert (S1 : ((φ x -[ x ]> χ x) ∧ (ψ x -[ x ]> θ x))
    → (∀ x, (φ x → χ x) ∧ (ψ x → θ x))).
  {
    pose proof (n10_22 (fun x => φ x → χ x) (fun x => ψ x → θ x))
      as n10_22.
    symmetry in n10_22.
    now destruct n10_22.
  }
  assert (S2 : ((φ x -[ x ]> χ x) ∧ (ψ x -[ x ]> θ x))
    → (∀ x, (φ x ∧ ψ x) → (χ x ∧ θ x))).
  {
    intro Hp.
    (* TODO: figure out if `intro x` can be done according to original proof *)
    intro x.
    pose proof (S1 Hp x) as S1_1.
    pose proof (n3_47 (φ x) (ψ x) (χ x) (θ x)) as n3_47.
    MP n3_47 S1_1.
    (* pose proof n10_27 as n10_27. *)
    exact n3_47.
  }
  exact S2.
Qed.

Theorem n10_4 (φ ψ χ θ : Prop → Prop) :
  ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
  → (φ x ∧ ψ x) <[- x -]> (χ x ∧ θ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0)) as Equiv4_01a.
  (* ******** *)
  pose proof (n10_22 (fun x => φ x → χ x) 
    (fun x => χ x → φ x)) as n10_22a.
  setoid_rewrite <- Equiv4_01a in n10_22a.
  destruct n10_22a as [n10_22al n10_22ar]. clear n10_22ar.
  pose proof (n10_22 (fun x => ψ x → θ x)
    (fun x => θ x → ψ x)) as n10_22b.
  setoid_rewrite <- Equiv4_01a in n10_22b.
  destruct n10_22b as [n10_22bl n10_22br]. clear n10_22br.
  (* This step has omitted a lot of things *)
  assert (S1 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → ((φ x -[ x ]> χ x) ∧ (ψ x -[ x ]> θ x))).
  {
    pose proof (Simp3_26 (φ x -[x]> χ x) (χ x -[x]> φ x))
      as Simp3_26a.
    Syll n10_22al Simp3_26a n10_22al_1.
    pose proof (Simp3_26 (ψ x -[x]> θ x) (θ x -[x]> ψ x))
      as Simp3_26b.
    Syll n10_22bl Simp3_26b n10_22bl_1.
    clear n10_22al n10_22bl Simp3_26a Simp3_26b.
    assert (C1 : (φ x<[-x-]>χ x  →  φ x-[x]>χ x)
      ∧ (ψ x<[-x-]>θ x  →  ψ x-[x]>θ x)).
    { now Conj n10_22al_1 n10_22bl_1 C1. }
    pose proof (n3_47 
      (φ x <[-x-]> χ x) (ψ x <[-x-]> θ x)
      (φ x -[x]> χ x) (ψ x -[x]> θ x))
      as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (φ x ∧ ψ x) -[x]> (χ x ∧ θ x)).
  {
    pose proof (n10_39 φ ψ χ θ) as n10_39.
    now Syll n10_39 S1 S2.
  }
  assert (S3 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (χ x ∧ θ x) -[x]> (φ x ∧ ψ x)).
  {
    pose proof (Simp3_27 (φ x-[x]>χ x) (χ x -[x]> φ x))
      as Simp3_27a.
    Syll n10_22al Simp3_27a n10_22al_1.
    pose proof (Simp3_27 (ψ x-[x]>θ x) (θ x-[x]>ψ x))
      as Simp3_27b.
    Syll n10_22bl Simp3_27b n10_22bl_1.
    clear n10_22al n10_22bl Simp3_27a Simp3_27b.
    assert (C1 : (φ x<[-x-]>χ x  →  χ x-[x]>φ x )
      ∧ (ψ x<[-x-]>θ x  →  θ x-[x]>ψ x )).
    { now Conj n10_22al_1 n10_22bl_1 C1. }
    pose proof (n3_47
      (φ x<[-x-]>χ x) (ψ x<[-x-]>θ x)
      (χ x-[x]>φ x ) (θ x-[x]>ψ x)
    ) as n3_47.
    MP n3_47 C1.
    pose proof (n10_39 χ θ φ ψ) as n10_39.
    now Syll n3_47 n10_39 S3.
  }
  assert (S4 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (((φ x ∧ ψ x) -[x]> (χ x ∧ θ x))
        ∧ ((χ x ∧ θ x) -[x]> (φ x ∧ ψ x)))).
  {
    assert (C1 : 
      ((φ x <[-x-]> χ x) ∧ ψ x <[-x-]> θ x 
        → (φ x ∧ ψ x)-[x]>χ x ∧ θ x)
      ∧
      ((φ x <[-x-]> χ x ) ∧ ψ x <[-x-]> θ x 
        → (χ x ∧ θ x)-[x]>φ x ∧ ψ x)).
    { now Conj S1 S3 C1. }
    pose proof (Comp3_43
      ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
      ((φ x ∧ ψ x) -[x]> (χ x ∧ θ x))
      ((χ x ∧ θ x) -[x]> (φ x ∧ ψ x)))
      as Comp3_43.
    now MP Comp3_43 C1.
  }
  assert (S5 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (φ x ∧ ψ x) <[- x -]> (χ x ∧ θ x)).
  {
    intro Hp.
    pose proof (S4 Hp) as S4_1.
    rewrite <- n10_22 in S4_1.
    setoid_rewrite <- Equiv4_01a in S4_1.
    exact S4_1.
  }
  exact S5.
Qed.

Theorem n10_41 (φ ψ : Prop → Prop) :
  (∀ x, φ x) ∨ (∀ x, ψ x) → (∀ x, φ x ∨ ψ x).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, φ x) → φ Y).
  { now apply n10_1. }
  assert (S2 : (∀ x, φ x) → (φ Y ∨  ψ Y)).
  {
    pose proof (n2_2 (φ Y) (ψ Y)) as n2_2.
    now Syll S1 n2_2 S2.
  }
  assert (S3 : (∀ x, ψ x) → ψ Y).
  { now apply n10_1. }
  assert (S4 : (∀ x, ψ x) → (φ Y ∨  ψ Y)).
  {
    pose proof (Add1_3 (φ Y) (ψ Y)) as Add1_3.
    now Syll S2 Add1_3 S3.
  }
  assert (S5 : ((∀ x, φ x) → (φ Y ∨  ψ Y))
    ∧ ((∀ x, ψ x) → (φ Y ∨  ψ Y))).
  {
    pose proof (n10_13 (fun y => (∀ x, φ x) → (φ y ∨  ψ y))
      (fun y => (∀ x, ψ x) → (φ y ∨  ψ y)) Y) as n10_13.
    MP n10_13 S2.
    MP n10_13 S4.
    exact n10_13.
  }
  assert (S6 : ((∀ x, φ x) ∨  (∀ x, ψ x)) 
    → (φ Y ∨  ψ Y)).
  {
    pose proof (n3_44 (φ Y ∨ ψ Y) (∀ x, φ x)
      (∀ x, ψ x)) as n3_44.
    now MP n3_44 S5.
  }
  assert (S7 : ((∀ x, φ x) ∨  (∀ x, ψ x)) 
    → (∀ y, φ y ∨  ψ y)).
  {
    pose proof (n10_11 Y
      (fun y => ((∀ x, φ x) ∨  (∀ x, ψ x)) 
        → (φ y ∨  ψ y))) as n10_11.
    MP n10_11 S6.
    pose proof (n10_21 (fun y => φ y ∨  ψ y)
      ((∀ x, φ x) ∨  (∀ x, ψ x))) as n10_21.
    (* We don't use `MP` here and directly rewrite *)
    now rewrite -> n10_21 in n10_11.
  }
  exact S7.
Qed.

Theorem n10_411 (φ ψ χ θ : Prop → Prop) :
  ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
  → (φ x ∨ ψ x) <[- x -]> (χ x ∨ θ x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → ((φ X ↔ χ X) ∧ (ψ X ↔ θ X))).
  {
    exact (n10_14 (fun x => φ x ↔ χ x) 
      (fun x => ψ x ↔ θ x) X).
  }
  assert (S2 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → ((φ X ∨  ψ X) ↔ (χ X ∨  θ X))).
  {
    pose proof (n4_39 (φ X) (ψ X) (χ X) (θ X)) as n4_39.
    now Syll n4_39 S1 S2.
  }
  assert (S3 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (φ x ∨ ψ x) <[- x -]> (χ x ∨ θ x)).
  {
    pose proof (n10_11 X
      (fun x0 =>
        ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
          → ((φ x0 ∨  ψ x0) ↔ (χ x0 ∨  θ x0)))) 
      as n10_11.
    MP S2 n10_11.
    pose proof (n10_21
      (fun x0 => ((φ x0 ∨  ψ x0) ↔ (χ x0 ∨  θ x0)))
      ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    ) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  exact S3.
Qed.

Theorem n10_412 (φ ψ : Prop → Prop) :
  (φ x <[- x -]> ψ x) ↔ (¬ φ x <[- x -]> ¬ ψ x).
Proof.
  set (X := Real "x").
  pose proof (Transp4_11 (φ X) (ψ X)) as Transp4_11.
  pose proof (n10_11 X (fun x =>
    (φ x ↔ ψ x) ↔ (¬ φ x ↔ ¬ ψ x))) as n10_11.
  MP n10_11 Transp4_11.
  pose proof (n10_271 (fun x => φ x ↔ ψ x) 
    (fun x => ¬ φ x ↔ ¬ ψ x)) as n10_271.
  now MP n10_11 n10_271.
Qed.

Theorem n10_413 (φ ψ χ θ : Prop → Prop) :
  ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
  → (φ x → ψ x) <[- x -]> (χ x → θ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
  → ((¬φ x) ∨  ψ x) <[- x -]> ((¬χ x) ∨  θ x)).
  {
    pose proof (n10_411 (fun x => ¬ φ x) ψ 
      (fun x => ¬ χ x) θ) as n10_411.
    simpl in n10_411.
    pose proof (n10_412 φ χ) as n10_412.
    now rewrite <- n10_412 in n10_411.
  }
  assert (S2 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (φ x → ψ x) <[- x -]> (χ x → θ x)).
  { now setoid_rewrite <- Impl1_01a in S1. }
  exact S2.
Qed.

Theorem n10_414 (φ ψ χ θ : Prop → Prop) :
  ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
  → (φ x ↔ ψ x) <[- x -]> (χ x ↔ θ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0)) as Equiv4_01a.
  (* ******** *)
  assert (S1 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → ((ψ x → φ x) <[- x -]> (θ x → χ x))).
  {
    pose proof (n10_413 ψ φ θ χ) as n10_413.
    (* as always, ignore some chores *)
    now rewrite -> n4_3 in n10_413 at 1.
  }
  assert (S2 : ((φ x <[- x -]> χ x) ∧ ((ψ x <[- x -]> θ x)))
    → (φ x ↔ ψ x) <[- x -]> (χ x ↔ θ x)).
  {
    pose proof (n10_413 φ ψ χ θ) as n10_413.
    assert (C1 :
      (( φ x<[-x-]>χ x ) ∧  ψ x<[-x-]>θ x  →  
        (ψ x → φ x)<[-x-]>(θ x → χ x))
      ∧
      (( φ x<[-x-]>χ x ) ∧  ψ x<[-x-]>θ x  →  
        (φ x → ψ x)<[-x-]>(χ x → θ x) )).
    { now Conj S1 n10_413 C1. }
    pose proof (n10_4
      (fun x => ψ x → φ x)
      (fun x => φ x → ψ x)
      (fun x => θ x → χ x)
      (fun x => χ x → θ x)
      ) as n10_4.
    pose proof (n4_76
      (( φ x<[-x-]>χ x ) ∧  ψ x<[-x-]>θ x)
      ((ψ x → φ x)<[-x-]>(θ x → χ x))
      ((φ x → ψ x)<[-x-]>(χ x → θ x))
      ) as n4_76.
    rewrite -> n4_76 in C1.
    clear S1 n10_413 n4_76.
    Syll C1 n10_4 S1_1.
    setoid_rewrite <- Equiv4_01a in S1_1.
    (* Change the orders in conclusion *)
    setoid_rewrite -> n4_21 in S1_1 at 4.
    setoid_rewrite -> n4_21 in S1_1 at 5.
    exact S1_1.
  }
  exact S2.
Qed.

Theorem n10_42 (φ ψ : Prop → Prop) :
  (∃ x, φ x) ∨ (∃ x, ψ x) ↔ (∃ x, φ x ∨ ψ x).
Proof.
  assert (S1 : ((∀ x, ¬ φ x) ∧ (∀ x, ¬ ψ x))
    ↔ (∀ x, (¬ φ x) ∧ (¬ ψ x))).
  {
    pose proof (n10_22 
      (fun x => ¬ φ x) (fun x => ¬ ψ x)) as n10_22.
    now symmetry in n10_22.
  }
  assert (S2 : (¬((∀ x, ¬ φ x) ∧ (∀ x, ¬ ψ x)))
    ↔ (¬(∀ x, (¬ φ x) ∧ (¬ ψ x)))).
  { now rewrite -> Transp4_11 in S1. }
  assert (S3 : ((¬(∀ x, ¬ φ x)) ∨  (¬(∀ x, ¬ ψ x)))
    ↔ (¬(∀ x, ¬(φ x ∨   ψ x)))).
  {
    rewrite -> n4_51 in S2.
    setoid_rewrite -> n4_56 in S2.
    (* n10_271 ignored - does it have something to do with 
      `setoid_rewrite`?! *)
    exact S2.
  }
  assert (S4 : (∃ x, φ x) ∨ (∃ x, ψ x) ↔ (∃ x, φ x ∨ ψ x)).
  {
    setoid_rewrite ->  n10_253_alt in S3.
    now setoid_rewrite <- n4_13 in S3.
  }
  exact S4.
Qed.

Theorem n10_43 (φ ψ : Prop → Prop) (X : Prop) :
  ((φ z <[- z -]> ψ z) ∧ φ X) ↔
  ((φ z <[- z -]> ψ z) ∧ ψ X).
Proof.
  assert (S1 : (φ z <[- z -]> ψ z) → (φ X ↔ ψ X)).
  { now apply n10_1. }
  assert (S2 : ((φ z <[- z -]> ψ z) ∧ φ X) ↔
    ((φ z <[- z -]> ψ z) ∧ ψ X)).
  { now rewrite -> n5_32 in S1. }
  exact S2.
Qed.

Theorem n10_5 (φ ψ : Prop → Prop) :
  (∃ x, φ x ∧ ψ x) → ((∃ x, φ x) ∧ (∃ x, ψ x)).
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ∀ x, (φ x ∧ ψ x) → φ x).
  {
    pose proof (Simp3_26 (φ X) (ψ X)) as Simp3_26.
    pose proof (n10_11 X (fun x => φ x ∧ ψ x → φ x)) as n10_11.
    now MP Simp3_26 n10_11.
  }
  assert (S2 : (∃ x, (φ x ∧ ψ x)) → (∃ x, φ x)).
  {
    pose proof (n10_28 (fun x => φ x ∧ ψ x) φ) as n10_28.
    now MP S1 n10_28.
  }
  assert (S3 : ∀ x, (φ x ∧ ψ x) → ψ x).
  {
    pose proof (Simp3_27 (φ X) (ψ X)) as Simp3_26.
    pose proof (n10_11 X (fun x => φ x ∧ ψ x → ψ x)) as n10_11.
    now MP Simp3_27 n10_11.
  }
  assert (S4 : (∃ x, (φ x ∧ ψ x)) → (∃ x, ψ x)).
  {
    pose proof (n10_28 (fun x => φ x ∧ ψ x) ψ) as n10_28.
    now MP S3 n10_28.
  }
  assert (S5 : (∃ x, φ x ∧ ψ x) → ((∃ x, φ x) ∧ (∃ x, ψ x))).
  {
    assert (C1 : ((∃ x, φ x ∧ ψ x) → ∃ x, φ x)
      ∧ ((∃ x, φ x ∧ ψ x) → ∃ x, ψ x)).
    { now Conj S2 S4 C1. }
    pose proof (Comp3_43 (∃ x, φ x ∧ ψ x) (∃ x, φ x)
      (∃ x, ψ x)) as Comp3_43.
    now MP C1 Comp3_43.
  }
  exact S5.
Qed.

Theorem n10_51 (φ ψ : Prop → Prop) :
  ¬(∃ x, φ x ∧ ψ x) ↔ (φ x -[ x ]> ¬ ψ x).
Proof.
  assert (S1 : (¬(∃ x, φ x ∧ ψ x)) 
    ↔ (∀ x, ¬(φ x ∧ ψ x))).
  { now apply n10_252. }
  assert (S2 : ¬(∃ x, φ x ∧ ψ x) ↔ (φ x -[ x ]> ¬ ψ x)).
  {
    setoid_rewrite -> n4_51 in S1.
    setoid_rewrite <- n4_62 in S1.
    (* n10_271 ignored *)
    exact S1.
  }
  exact S2.
Qed.

Theorem n10_52 (φ : Prop → Prop) (P : Prop) :
  (∃ x, φ x) → ((∀ x, φ x → P) ↔ P).
Proof.
  assert (S1 : (∃ x, φ x) → (P ↔ ((∃ x, φ x) → P))).
  {
    pose proof (n5_5 (∃ x, φ x) P) as n5_5.
    now symmetry in n5_5.
  }
  assert (S2 : (∃ x, φ x) → (P ↔ (∀ x, φ x → P))).
  {
    pose proof n10_23 as n10_23.
    now setoid_rewrite <- n10_23 in S1 at 2.
  }
  now symmetry in S2.
Qed.

Theorem n10_53 (φ ψ : Prop → Prop) :
  ¬(∃ x, φ x) → (φ x -[ x ]> ψ x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ∀ x, (¬ φ x) → (φ x → ψ x)).
  {
    pose proof (n2_21 (φ X) (ψ X)) as n2_21.
    pose proof (n10_11 X (fun x => (¬ φ x) → (φ x → ψ x))) 
      as n10_11.
    now MP n2_21 n10_11.
  }
  assert (S2 : (∀ x, ¬ φ x) → (∀ x, φ x → ψ x)).
  {
    pose proof (n10_27 (fun x => ¬ φ x) (fun x => φ x → ψ x)) 
      as n10_27.
    now MP S1 n10_27.
  }
  assert (S3 : ¬(∃ x, φ x) → (φ x -[ x ]> ψ x)).
  { now rewrite <- n10_252 in S2. }
  exact S3.
Qed.

Theorem n10_541 (φ ψ : Prop → Prop) (P : Prop) :
  (φ y -[ y ]> (P ∨ ψ y)) ↔ (P ∨ (φ y -[ y ]> ψ y)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* A specific `Assoc1_5` form that comes as a equiv relation, which will be later 
    used *)
  assert (Assoc1_5Eq : forall P Q R, P ∨ Q ∨ R ↔ Q ∨ P ∨ R).
  { split; apply Assoc1_5. }
  (* ******** *)
  assert (S1 : (φ y -[ y ]> (P ∨ ψ y)) 
    ↔ (∀ y, (¬ φ y) ∨ P ∨ ψ y)).
  {
    pose proof (n4_2 (φ y -[ y ]> (P ∨ ψ y))) as n4_2.
    now setoid_rewrite -> Impl1_01a in n4_2 at 2.
  }
  assert (S2 : (φ y -[ y ]> (P ∨ ψ y)) 
    ↔ (∀ y, P ∨ (¬φ y) ∨ ψ y)).
  {
    setoid_rewrite -> Assoc1_5Eq in S1.
    (* n10_271 ignored *)
    exact S1.
  }
  assert (S3 : (φ y -[ y ]> (P ∨ ψ y)) 
    ↔ (P ∨ (∀ y, (¬φ y) ∨ ψ y))).
  { now rewrite -> n10_2 in S2. }
  assert (S4 : (φ y -[ y ]> (P ∨ ψ y)) ↔ (P ∨ (φ y -[ y ]> ψ y))).
  { now setoid_rewrite <- Impl1_01a in S3. }
  exact S4.
Qed.

Theorem n10_542 (φ ψ : Prop → Prop) (P : Prop) :
  (φ y -[ y ]> (P → ψ y)) ↔ (P → (φ y -[ y ]> ψ y)).
Proof.
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  pose proof (n10_541 φ ψ (¬P)) as n10_541.
  now setoid_rewrite <- Impl1_01a in n10_541.
Qed.

Theorem n10_55 (φ ψ : Prop → Prop) :
  ((∃ x, φ x ∧ ψ x) ∧ (φ x -[ x ]> ψ x))
  ↔ ((∃ x, φ x) ∧ (φ x -[ x ]> ψ x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (φ X → ψ X) → ((φ X ∧ ψ X) ↔ φ X)).
  {
    pose proof (n4_71 (φ X) (ψ X)) as n4_71.
    replace (φ X ↔ φ X ∧ ψ X) with (φ X ∧ ψ X ↔ φ X)
      in n4_71.
    2: { apply propositional_extensionality. apply n4_21. }
    now destruct n4_71.
  }
  assert (S2 : (φ x -[x]> ψ x) 
    → (∀ x, (φ x ∧ ψ x) ↔ φ x)).
  {
    pose proof (n10_11 X (fun x => 
      (φ x → ψ x) → ((φ x ∧ ψ x) ↔ φ x))) as n10_11.
    MP S1 n10_11.
    pose proof (n10_27 (fun x => φ x → ψ x)
      (fun x => (φ x ∧ ψ x) ↔ φ x)) as n10_27.
    now MP n10_11 n10_27.
  }
  assert (S3 : (φ x -[x]> ψ x) 
    → ((∃ x, φ x ∧ ψ x) ↔ (∃ x, φ x))).
  {
    pose proof (n10_281 (fun x => φ x ∧ ψ x) φ) as n10_281.
    now Syll S2 n10_281 S3.
  }
  assert (S4 : ((∃ x, φ x ∧ ψ x) ∧ (φ x -[ x ]> ψ x))
    ↔ ((∃ x, φ x) ∧ (φ x -[ x ]> ψ x))).
  {
    rewrite -> n5_32 in S3.
    rewrite -> n4_3 in S3.
    replace (( φ x-[x]>ψ x ) ∧ ∃ x, φ x)
      with ((∃ x, φ x) ∧ ( φ x-[x]>ψ x )) in S3.
    2: { apply propositional_extensionality. now rewrite -> n4_3. }
    exact S3.
  }
  exact S4.
Qed.

Theorem n10_56 (φ ψ χ : Prop → Prop) :
  ((φ x -[ x ]> ψ x) ∧ (∃ x, φ x ∧ χ x))
  → (∃ x, ψ x ∧ χ x).
Proof.
  assert (S1 : (φ x -[ x ]> ψ x) 
    → ((φ x ∧ χ x) -[x]> (ψ x ∧ χ x))).
  { apply n10_31. }
  assert (S2 : (φ x -[ x ]> ψ x) 
    → ((∃ x, φ x ∧ χ x) → (∃ x, ψ x ∧ χ x))).
  {
    pose proof (n10_28 (fun x => (φ x ∧ χ x)) 
      (fun x => ψ x ∧ χ x)) as n10_28.
    now Syll S1 n10_28 S2.
  }
  assert (S3 : ((φ x -[ x ]> ψ x) ∧ (∃ x, φ x ∧ χ x))
    → (∃ x, ψ x ∧ χ x)).
  {
    pose proof (Imp3_31 (φ x-[x]>ψ x) (∃ x, φ x ∧ χ x)
      (∃ x, ψ x ∧ χ x)) as Imp3_31.
    now MP S2 Imp3_31.
  }
  exact S3.
Qed.

Theorem n10_57 (φ ψ χ : Prop → Prop) :
  (φ x -[ x ]> (ψ x ∨ χ x)) 
    → ((φ x -[ x ]> ψ x) ∨ (∃ x, φ x ∧ χ x)).
Proof.
  assert (S1 : ((φ x -[ x ]> (ψ x ∨ χ x)) ∧ (¬ ∃ x, φ x ∧ χ x))
    → ((φ x -[x]> (ψ x ∨ χ x)) ∧ (φ x -[x]> (¬ χ x)))).
  {
    pose proof (n10_51 φ χ) as n10_51.
    destruct n10_51 as [n10_51l n10_51r].
    clear n10_51r.
    pose proof Fact3_45 as Fact3_45.
    pose proof (Fact3_45 (¬ (∃ x, φ x ∧ χ x)) (φ x-[x]>¬ χ x)
      (φ x-[x]>(ψ x ∨ χ x))) as Fact3_45.
    MP n10_51r Fact3_45.
    rewrite -> n4_3 in Fact3_45.
    replace (( φ x-[x]>¬ χ x ) ∧  φ x-[x]>(ψ x ∨ χ x))
      with ((φ x-[x]>(ψ x ∨ χ x)) ∧ ( φ x-[x]>¬ χ x ))
      in Fact3_45.
    2: { apply propositional_extensionality. now rewrite -> n4_3. }
    exact Fact3_45.
  }
  assert (S2 : ((φ x -[ x ]> (ψ x ∨ χ x)) 
      ∧ (¬ ∃ x, φ x ∧ χ x))
    → ((φ x -[x]> ((ψ x ∨ χ x) ∧ ¬ χ x)))).
  {
    pose proof n10_29 as n10_29a.
    pose proof (n10_29 φ (fun x => (ψ x ∨ χ x)) 
      (fun x => ¬ χ x)) as n10_29.
    destruct n10_29 as [n10_29l n10_29r].
    clear n10_29r.
    now Syll S1 n10_29l S2.
  }
  assert (S3 : ((φ x -[ x ]> (ψ x ∨ χ x)) 
      ∧ (¬ ∃ x, φ x ∧ χ x))
    → (φ x -[ x ]> ψ x)).
  {
    setoid_rewrite -> n5_61 in S2.
    (* Here I think this is unprovable... *)
    admit.
  }
  assert (S4 : (φ x -[ x ]> (ψ x ∨ χ x)) 
    → ((φ x -[ x ]> ψ x) ∨ (∃ x, φ x ∧ χ x))).
  {
    pose proof (n5_6 (φ x-[x]>(ψ x ∨ χ x)) (∃ x : Prop, φ x ∧ χ x)
      (φ x-[x]>ψ x)) as n5_6.
    destruct n5_6 as [n5_6l n5_6r].
    clear n5_6r.
    MP S3 n5_6.
    now rewrite -> n4_31 in n5_6l.
  }
  exact S4.
Admitted.

Close Scope single_app_impl.
Close Scope single_app_equiv.
