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

Notes on this chapter:
1. There are several places in this chapter where n10_271 is used, 
but for all these occurrences I used `setoid_rewrite` to finish the 
proof instantly and n10_271 is completely unused. Idk how should 
n10_271 be used
2. At the very end of this chapter, n10_57 seems to contain one 
error that I cannot prove.
*)

Notation " A -[ x : P ]> B " := (∀ (x : P), A → B)
  (at level 85, x name, right associativity,
  format " '[' A '/' '[ ' -[ x : P ]> ']' '/' B ']' ")
  : type_scope.

Notation " A -[ x ]> B " := (( A -[ x : Prop ]> B ))
  (at level 80, x name, right associativity,
  format " A '/' '[ ' -[ x ]> ']' '/' B ")
  : type_scope.

Notation " A <[- x : P -]> B " := (∀ (x : P), A ↔ B)
  (at level 85, x name, right associativity,
  format " '[' A '/' '[ ' <[- x : P -]> ']' '/' B ']' ")
  : type_scope.

Notation " A <[- x -]> B " := (A <[- x : Prop -]> B)
  (at level 80, x name, right associativity,
  format " A '/' '[ ' <[- x -]> ']' '/' B ")
  : type_scope.

Definition n10_01 (Phi : Prop → Prop) : 
  (∃ x, Phi x) = ¬ (∀ x, ¬ Phi x). Admitted.

Definition n10_02 (Phi Psi : Prop → Prop) : 
  Phi x -[ x ]> Psi x = ∀ x, Phi x → Psi x. Admitted.

Definition n10_03 (Phi Psi : Prop → Prop) : 
  Phi x <[- x -]> Psi x = ∀ x, (Phi x ↔ Psi x). Admitted.

Theorem n10_1 (Phi : Prop → Prop) (Y : Prop) : (∀ x, Phi x) → Phi Y.
Proof.  exact (n9_2 Phi Y). Qed.

(* Thm 10.11: If Phi y is true whatever possible argument y may be, then ∀, Phi x is true. [*9.13] *)
Theorem n10_11 (Y : Prop) (Phi : Prop → Prop) : Phi Y → ∀ x, Phi x.
Proof.
Admitted.

Theorem n10_12 (Phi : Prop → Prop) (P : Prop) : 
  (∀ x, P ∨ Phi x) → P ∨ ∀ x, Phi x.
Proof.  exact (n9_25 P Phi). Qed.

(* Thm 10.121: If Phi x is significant, then if a is of the same type as x, Phi a is significant, and vice versa. [*9.14] *)

(* Thm 10.122: If for some a, there is a proposition Phi a, then there is a function Phi x^, and vice versa. [*9.15] *)

(* Thm 10.13: If Phi x^ and Psi x^ takes arguments of the same type, and we have |- Phi x and |- Psi x, we shall have |- Phi x ∧ Psi x . *)
(* NOTE: we didn't enforce `is_same_type` so far. Currently I decide to just leave it manually specified *)
Theorem n10_13 (Phi Psi : Prop → Prop) (X : Prop) :
  Phi X → Psi X → (Phi X ∧ Psi X).
Proof.
Admitted.

Theorem n10_14 (Phi Psi : Prop → Prop) (Y : Prop) : 
  (∀ x, Phi x) ∧ (∀ x, Psi x)
  → Phi Y ∧ Psi Y.
Proof.
  pose proof (n10_1 Phi Y) as S1.
  pose proof (n10_1 Psi Y) as S2.
  assert (S3 : ((∀ x, Phi x) → Phi Y) ∧ ((∀ x, Psi x) → Psi Y)).
  {
    pose proof (n10_13 (fun x => (∀ x, Phi x) → Phi Y) 
        (fun x => (∀ x, Psi x) → Psi Y) Y) as n10_13.
    MP n10_13 S1.
    MP n10_13 S2.
    exact n10_13. 
  }
  assert (S4 : ((∀ x, Phi x) ∧ (∀ x, Psi x)) → (Phi Y ∧ Psi Y)).
  {
    pose proof (n3_47 (∀ x, Phi x) (∀ x, Psi x)
                (Phi Y) (Psi Y)) as n3_47.
    MP n3_47 S3.
    exact n3_47.
  }
  exact S4.
Qed.

Theorem n10_2 (Phi : Prop → Prop) (P : Prop) :
  (∀ x, P ∨ Phi x) ↔ P ∨ (∀ x, Phi x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (P ∨ ∀ x, Phi x) → P ∨ Phi Y).
  {
    pose proof (n10_1 Phi Y) as n10_1.
    pose proof (Sum1_6 P (∀ x, Phi x) (Phi Y)) as Sum1_6.
    MP Sum1_6 n10_1.
    exact Sum1_6.
  }
  assert (S2 : ∀ y, (P ∨ (∀ x, Phi x) → P ∨ Phi y)).
  {
    pose proof (n10_11 Y (fun y => (P ∨ ∀ x, Phi x) → P ∨ Phi y)) as n10_11.
    MP n10_11 S1.
    exact n10_11.
  }
  assert (S3 : (P ∨ (∀ x, Phi x)) → (∀ y, P ∨ Phi y)).
  {
    setoid_rewrite -> Impl1_01a in S2.
    pose proof (n10_12 (fun y => P ∨ Phi y) (¬ (P ∨ ∀ x, Phi x))) as n10_12.
    MP n10_12 S2.
    setoid_rewrite <- Impl1_01a in n10_12.
    exact n10_12.
  }
  assert (S4 : (∀ y, (P ∨ Phi y)) → P ∨ (∀ x, Phi x)).
  { exact (n10_12 Phi P). }
  assert (S5 : (∀ x, P ∨ Phi x) ↔ P ∨ (∀ x, Phi x)).
  (* TODO: use `Equiv` for rigor *)
  { split; [exact S4 | exact S3]. }
  exact S5.
Qed.

Theorem n10_21 (Phi : Prop → Prop) (P : Prop) :
  (∀ x, P → Phi x) ↔ (P → (∀ x, Phi x)).
Proof. 
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  pose proof (n10_2 Phi (¬P)) as n10_2.
  repeat setoid_rewrite <- Impl1_01a in n10_2.
  exact n10_2.
Qed.

Theorem n10_22 (Phi Psi : Prop → Prop) :
  (∀ x, Phi x ∧ Psi x) ↔ (∀ x, Phi x) ∧ (∀ x, Psi x).
Proof. 
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, Phi x ∧ Psi x) → Phi Y ∧ Psi Y).
  { exact (n10_1 (fun x => Phi x ∧ Psi x) Y). }
  assert (S2 : (∀ x, Phi x ∧ Psi x) → Phi Y).
  { 
    pose proof (Simp3_26 (Phi Y) (Psi Y)) as Simp3_26.
    Syll Simp3_26 S1 S2.
    exact S2.
  }
  assert (S3 : (∀ y, (∀ x, Phi x ∧ Psi x) → Phi y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, Phi x ∧ Psi x) → Phi y)) as n10_11.
    MP n10_11 S2.
    exact n10_11.
  }
  assert (S4 : (∀ x, Phi x ∧ Psi x) → ∀ y, Phi y).
  {
    destruct (n10_21 Phi (∀ x, Phi x ∧ Psi x)) as [n10_21l n10_21r].
    MP n10_21l S3.
    exact n10_21l.
  }
  assert (S5 : (∀ x, Phi x ∧ Psi x) → Psi Y).
  {
    pose proof (Simp3_27 (Phi Y) (Psi Y)) as Simp3_27.
    Syll Simp3_27 S1 S5.
    exact S5.
  }
  assert (S6 : (∀ y, (∀ x, Phi x ∧ Psi x) → Psi y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, Phi x ∧ Psi x) → Psi y)) as n10_11.
    MP n10_11 S5.
    exact n10_11.
  }
  assert (S7 : (∀ x, Phi x ∧ Psi x) → ∀ y, Psi y).
  {
    destruct (n10_21 Psi (∀ x, Phi x ∧ Psi x)) as [n10_21l n10_21r].
    MP n10_21l S6.
    exact n10_21l.
  }
  assert (S8 : (∀ x, Phi x ∧ Psi x) → ((∀ y, Phi y) ∧ ∀ z, Psi z)).
  {
    pose proof (Comp3_43 (∀ x, Phi x ∧ Psi x) (∀ y, Phi y) (∀ z, Psi z)) as Comp3_43.
    assert (C1 : ((∀ x, Phi x ∧ Psi x) → ∀ y, Phi y)
      ∧ ((∀ x, Phi x ∧ Psi x) → ∀ y, Psi y)).
    { clear S1 S2 S3 S5 S6 Comp3_43. now Conj S4 S7 C1. }
    MP Comp3_43 C1.
    exact Comp3_43.
  }
  assert (S9 : ∀ y, (∀ x, Phi x) ∧ (∀ x, Psi x) → (Phi y ∧ Psi y)).
  {
    pose proof (n10_14 Phi Psi Y) as n10_14.
    pose proof (n10_11 Y (fun y => 
      (∀ x, Phi x) ∧ (∀ x, Psi x) → (Phi y ∧ Psi y))) as n10_11.
    MP n10_11 n10_14.
    exact n10_11.
  }
  assert (S10 : (∀ x, Phi x) ∧ (∀ x, Psi x) → ∀ y, (Phi y ∧ Psi y)).
  {
    pose proof n10_21 as n10_21.
    pose proof (n10_21 (fun y => (Phi y ∧ Psi y)) 
      ((∀ x, Phi x) ∧ (∀ x, Psi x))) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l S9.
    exact n10_21l.
  }
  assert (S11 : (∀ x, Phi x ∧ Psi x) ↔ (∀ x, Phi x) ∧ (∀ x, Psi x)).
  {
    assert (C1 : ((∀ x, Phi x ∧ Psi x) → ((∀ y, Phi y) ∧ ∀ z, Psi z))
      ∧ ((∀ x, Phi x) ∧ (∀ x, Psi x) → ∀ y, (Phi y ∧ Psi y))).
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

Theorem n10_23 (Phi : Prop → Prop) (P : Prop) :
  (∀ x, Phi x → P) ↔ ((∃ x, Phi x) → P).
Proof.
  assert (S1 : (∀ x, ¬ Phi x ∨ P) ↔ ((∀ x, ¬ Phi x) ∨ P)).
  {
    pose proof (n4_2 (∀ x, ¬ Phi x ∨ P)) as n4_2.
    rewrite <- n9_03 in n4_2 at 2.
    exact n4_2.
  }
  assert (S2 : (∀ x, (¬ Phi x) ∨ P) ↔ ((∃ x, Phi x) → P)).
  {
    rewrite <- n9_02 in S1.
    rewrite <- Impl1_01 in S1.
    exact S1.
  }
  assert (S3 : (∀ x, Phi x → P) ↔ ((∃ x, Phi x) → P)).
  {
    set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
      as Impl1_01a.
    setoid_rewrite <- Impl1_01a in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n10_23_alt (Phi : Prop → Prop) (P : Prop) :
  (∀ x, Phi x → P) ↔ ((∃ x, Phi x) → P).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((∃ x, Phi x) → P) ↔ ((¬ P) → (∀ x, ¬ Phi x))).
  {
    pose proof (Transp2_16 (∃ x, Phi x) P) as Transp2_16.
    rewrite -> n10_01 in Transp2_16 at 2.
    (* This can be able to be broken down into nests of `Syll`s. See S9
      Here for simplicity we use `n2_14` at the very end of the proof *)
    replace (¬ ¬ ∀ x, ¬ Phi x) with (∀ x, ¬ Phi x)
      in Transp2_16.
    pose proof (Transp2_17 (∃ x, Phi x) P) as Transp2_17.
    rewrite -> n10_01 in Transp2_17 at 1.
    replace (¬ ¬ ∀ x, ¬ Phi x) with (∀ x, ¬ Phi x)
      in Transp2_17.
    assert (C1 : (((∃ x, Phi x) → P) → (¬ P → ∀ x, ¬ Phi x))
      ∧ ((¬ P → ∀ x, ¬ Phi x) → ((∃ x, Phi x) → P))).
    { now Conj Transp2_16 Transp2_17 C1. }
    Equiv C1.
    exact C1.
    all: (
      apply propositional_extensionality;
      split; [ apply n2_12 | apply (n2_14 (∀ x, ¬ Phi x)) ]
    ).
  }
  assert (S2 : ((∃ x, Phi x) → P) ↔ (∀ x, ¬ P → ¬ Phi x)).
  {
    (* For simplicity *)
    replace (¬ P → ∀ x, ¬ Phi x) with (∀ x, ¬ P → ¬ Phi x)
      in S1 by (apply propositional_extensionality; apply n10_21).
    exact S1.
  }
  (* WTF???? *)
  assert (S3 : ((∃ x, Phi x) → P) → ((¬ P) → ¬ Phi X)).
  {
    pose proof (n10_1 (fun x => (¬ P) → ¬ Phi x) X) as n10_1.
    destruct S2 as [S2_l S2_r].
    Syll S2_l n10_1 S3.
    exact S3.
  }
  assert (S4 : ((∃ x, Phi x) → P) → (Phi X → P)).
  {
    pose proof (Transp2_17 (Phi X) P) as Transp2_17.
    Syll S3 Transp2_17 S4.
    exact S4.
  }
  (* The variable naming here is so wild *)
  assert (S5 : ∀ x0, ((∃ x, Phi x) → P) → (Phi x0 → P)).
  {
    pose proof (n10_11 X (fun x0 => ((∃ x, Phi x) → P) → (Phi x0 → P))) 
      as n10_11.
    MP n10_11 S4.
    exact n10_11.
  }
  assert (S6 : ((∃ x, Phi x) → P) → ∀ x, (Phi x → P)).
  {
    pose proof (n10_21 (fun x0 => (Phi x0 → P)) ((∃ x, Phi x) → P))
      as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l S5.
    exact n10_21l.
  }
  assert (S7 : (∀ x, (Phi x → P)) → (Phi X → P)).
  { exact (n10_1 (fun x => Phi x → P) X). }
  assert (S8 : (∀ x, (Phi x → P)) → ((¬ P) → ¬ Phi X)).
  {
    pose proof (Transp2_16 (Phi X) P) as Transp2_16.
    Syll S7 Transp2_16 S8.
    exact S8.
  }
  assert (S9 : (∀ x, (Phi x → P)) → (∀ x, (¬ P) → ¬ Phi x)).
  {
    pose proof (n10_11 X (fun x => ¬ Phi x)) as n10_11.
    assert (S8_1 : ((¬ P) → ¬ Phi X) → ((¬ P) → ∀ x, (¬ Phi x))).
    (* A demonstration of recursive `Syll`
    maybe there's even better and more natural way to handle this *)
    {
      intro.
      Syll H n10_11 H0.
      exact H0.
    }
    Syll S8 S8_1 S8_2.
    pose proof (n10_21 (fun x => ¬ Phi x) (¬ P)) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    clear S1 S2 S3 S4 S5 S6 S7 n10_11 n10_21l S8 S8_1.
    Syll S8_2 n10_21r S9.
    exact S9.
  }
  assert (S10 : (∀ x, (Phi x → P)) → (∃ x, Phi x) → P).
  {
    destruct S2 as [S2_l S2_r].
    clear S1 S3 S4 S5 S6 S7 S8 S2_l.
    Syll S9 S2_r S10.
    exact S10.
  }
  assert (S11 : (∀ x, Phi x → P) ↔ ((∃ x, Phi x) → P)).
  {
    assert (C1 : ((∀ x, (Phi x → P)) → (∃ x, Phi x) → P)
      ∧ (((∃ x, Phi x) → P) → ∀ x, (Phi x → P))).
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

Theorem n10_24 (Phi : Prop → Prop) (Y : Prop) :
  Phi Y → ∃ x, Phi x.
Proof.
  assert (S1 : (∀ x, ¬ Phi x) → ¬ Phi Y).
  { exact (n10_1 (fun x => ¬ Phi x) Y). }
  assert (S2 : Phi Y → (¬ ∀ x, ¬ Phi x)).
  {
    pose proof (Transp2_03 (∀ x, ¬ Phi x) (Phi Y)) as Transp2_03.
    MP Transp2_03 S1.
    exact Transp2_03.
  }
  assert (S3 : Phi Y → ∃ x, Phi x).
  {
    rewrite <- n10_01 in S2.
    exact S2.
  }
  exact S3.
Qed.

Theorem n10_25 (Phi : Prop → Prop) : (∀ x, Phi x) → (∃ x, Phi x).
Proof.
  set (Y := Real "y").
  pose proof (n10_1 Phi Y) as n10_1.
  pose proof (n10_24 Phi Y) as n10_24.
  Syll n10_1 n10_24 S1.
  exact S1.
Qed.

Theorem n10_251 (Phi : Prop → Prop) : (∀ x, ¬Phi x) → ¬(∀ x, Phi x).
Proof.
  pose proof (n10_25 Phi) as n10_25.
  pose proof (Transp2_16 (∀ x, Phi x) (∃ x, Phi x)) 
    as Transp2_16.
  MP Transp2_16 n10_25.
  rewrite -> n10_01 in Transp2_16.
  pose proof (n2_12 ((∀ x, ¬ Phi x))) as n2_12.
  Syll n2_12 Transp2_16 S1.
  exact S1.
Qed.

Theorem n10_252 (Phi : Prop → Prop) : ¬(∃ x, Phi x) ↔ (∀ x, ¬ Phi x).
Proof.
  pose proof (n4_2 (∀ x, ¬ Phi x)) as n4_2.
  rewrite <- n9_02 in n4_2 at 1.
  exact n4_2.
Qed.

Theorem n10_253 (Phi : Prop → Prop) : ¬(∀ x, Phi x) → (∃ x, ¬Phi x).
Proof.
  pose proof (n4_2 (¬ ∀ x, Phi x)) as n4_2.
  rewrite -> n9_01 in n4_2 at 2.
  destruct n4_2 as [n4_2l n4_2r].
  exact n4_2l.
Qed.

Theorem n10_252_alt (Phi : Prop → Prop) : ¬(∃ x, Phi x) ↔ (∀ x, ¬ Phi x).
Proof.
  pose proof (n4_13 (∀ x, ¬ Phi x)) as n4_13.
  rewrite <- n10_01 in n4_13 at 1.
  symmetry in n4_13.
  exact n4_13.
Qed.

Theorem n10_253_alt (Phi : Prop → Prop) : (¬(∀ x, Phi x)) ↔ (∃ x, ¬Phi x).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (∀ x, Phi x) → Phi Y).
  { exact (n10_1 Phi Y). }
  assert (S2 : (∀ x, Phi x) → ¬ ¬ Phi Y).
  {
    pose proof (n2_12 (Phi Y)) as n2_12.
    Syll S1 n2_12 S2.
    exact S2.
  }
  assert (S3 : (∀ x, Phi x) → ∀ y, ¬ ¬ Phi y).
  {
    (* n10_21 is unused *)
    pose proof (n10_11 Y (fun y => ¬¬ Phi y)) as n10_11.
    Syll S2 n10_21 S3.
    exact S3.
  }
  assert (S4 : (¬(∀ y, ¬ ¬ Phi y)) → ¬(∀ x, Phi x)).
  {
    pose proof (Transp2_16 (∀ x, Phi x) (∀ y, ¬ ¬ Phi y)) as Transp2_16.
    MP Transp2_16 S3.
    exact Transp2_16.
  }
  assert (S5 : (∃ y, ¬ Phi y) → ¬(∀ x, Phi x)).
  {
    rewrite <- n10_01 in S4.
    exact S4.
  }
  assert (S6 : (∀ y, ¬ ¬ Phi y) → ¬ ¬ Phi X).
  {
    exact (n10_1 (fun x => ¬ ¬ Phi x) X).
  }
  assert (S7 : (∀ y, ¬ ¬ Phi y) → Phi X).
  {
    pose proof (n2_14 (Phi X)) as n2_14.
    Syll S6 n2_14 S7.
    exact S7.
  }
  assert (S8 : (∀ y, ¬ ¬ Phi y) → (∀ x, Phi x)).
  {
    (* n10_21 is ignored *)
    pose proof (n10_11 X Phi) as n10_11.
    Syll S7 n10_11 S8.
    exact S8.
  }
  assert (S9 : (¬(∀ x, Phi x)) → ¬(∀ y, ¬ ¬ Phi y)).
  {
    pose proof (Transp2_16  (∀ y, ¬ ¬ Phi y) (∀ x, Phi x) ) as Transp2_16.
    MP Transp2_16 S8.
    exact Transp2_16.
  }
  assert (S10 : (¬(∀ x, Phi x)) → ∃ y, ¬(Phi y)).
  {
    rewrite <- n10_01 in S9.
    exact S9.
  }
  assert (S11 : (¬(∀ x, Phi x)) ↔ ∃ x, ¬ Phi x).
  {
    assert (C1 : ((¬(∀ x, Phi x)) → ∃ x, ¬ Phi x)
      ∧ ((∃ x, ¬ Phi x) → ¬(∀ x, Phi x))).
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
Theorem n10_26 (Phi Psi : Prop → Prop) (X : Prop) : 
  ((∀ z, Phi z → Psi z) ∧ Phi X) → Psi X.
Proof.
  pose proof (n10_1 (fun z => Phi z → Psi z) X) as n10_1.
  pose proof (Imp3_31 (∀ z, Phi z → Psi z) (Phi X) (Psi X)) as Imp3_31.
  MP Imp3_31 n10_1.
  exact Imp3_31.
Qed.

Theorem n10_27 (Phi Psi : Prop → Prop) : 
  (∀ z, Phi z → Psi z) → ((∀ z, Phi z) → (∀ z, Psi z)).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : ((∀ z, Phi z → Psi z) ∧ (∀ z, Phi z)) → ((Phi Y → Psi Y) ∧ Phi Y)).
  { exact (n10_14 (fun z => Phi z → Psi z) Phi Y). }
  assert (S2 : ((∀ z, Phi z → Psi z) ∧ (∀ z, Phi z)) → Psi Y).
  {
    pose proof (Ass3_35 (Phi Y) (Psi Y)) as Ass3_35.
    pose proof (n3_22 (Phi Y → Psi Y) (Phi Y)) as n3_22.
    Syll n3_22 Ass3_35 S2.
    clear n3_22.
    Syll S1 S2 S2_1.
    exact S2_1.
  }
  assert (S3 : ∀ y, ((∀ z, Phi z → Psi z) ∧ (∀ z, Phi z)) → Psi y).
  {
    (* Original text uses n10_1 and I think its a typo*)
    pose proof (n10_11 Y (fun y => (((∀ z, Phi z → Psi z) ∧ (∀ z, Phi z)) 
        → Psi y))) as n10_11.
    MP n10_11 S2.
    exact n10_11.
  }
  assert (S4 : ((∀ z, Phi z → Psi z) ∧ (∀ z, Phi z)) → ∀ y, Psi y).
  {
    pose proof (n10_21 Psi ((∀ z, Phi z → Psi z) ∧ (∀ z, Phi z))) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l S3.
    exact n10_21l.
  }
  assert (S5 : (∀ z, Phi z → Psi z) → ((∀ z, Phi z) → (∀ z, Psi z))). 
  {
    pose proof (Exp3_3 (∀ z, Phi z → Psi z) (∀ z, Phi z) (∀ y, Psi y))
       as Exp3_3.
    MP Exp3_3 S4.
    exact Exp3_3.
  }
  exact S5.
Qed.

Theorem n10_271 (Phi Psi : Prop → Prop) : 
  (∀ z, Phi z ↔ Psi z) → ((∀ z, Phi z) ↔ (∀ z, Psi z)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  (* ******** *)
  (* Whenever a proof involves `Hp`, this proof becomes a little special. 
    It seems that all deductions are given the context to only deduce with
    `Hp` being introduced, as followed... *)
  pose proof (n10_22 (fun z => Phi z → Psi z) (fun z => Psi z → Phi z)) 
    as n10_22.
  simpl in n10_22.
  setoid_rewrite <- Equiv4_01a in n10_22.
  destruct n10_22 as [n10_22l n10_22r].
  clear n10_22r.
  assert (S1 : (∀ z, Phi z ↔ Psi z) → (∀ z, Phi z → Psi z)).
  {
    pose proof (Simp3_26 (∀ x, Phi x → Psi x) (∀ x, Psi x → Phi x)) 
      as Simp3_26.
    Syll n10_22l Simp3_26 S1.
    exact S1.
  }
  assert (S2 : (∀ z, Phi z ↔ Psi z) → ((∀ z, Phi z) → (∀ z, Psi z))).
  {
    (* `Hp` always have to be after the line where `Hp` is declared. All
      theorems involved are suppose proofd to be match directly on the conclusion 
      part of the proposition, with `Hp` removed from the goal.
      This isn't something breaking the rule, as we can always proceed with 
      `Syll`s. But I think a slight intro of `Hp` adds a tiny spice aligned 
      with original proof, without harming it too much *)
    intro Hp.
    pose proof (n10_27 Phi Psi) as n10_27.
    pose proof (S1 Hp) as S1_1.
    MP n10_27 S1_1.
    exact n10_27.
  }
  assert (S3 : (∀ z, Phi z ↔ Psi z) → (∀ z, Psi z → Phi z)).
  {
    pose proof (Simp3_27 (∀ x, Phi x → Psi x) (∀ x, Psi x → Phi x)) 
      as Simp3_27.
    Syll n10_22l Simp3_27 S3.
    exact S3.
  }
  assert (S4 : (∀ z, Phi z ↔ Psi z) → ((∀ z, Psi z) → (∀ z, Phi z))).
  {
    intro Hp.
    pose proof (n10_27 Psi Phi) as n10_27.
    pose proof (S3 Hp) as S3_1.
    MP n10_27 S3_1.
    exact n10_27.
  }
  assert (S5 : (∀ z, Phi z ↔ Psi z) → ((∀ z, Phi z) ↔ (∀ z, Psi z))).
  {
    assert (C1 : ((∀ z, Phi z ↔ Psi z) → ((∀ z, Phi z) → (∀ z, Psi z)))
      ∧ ((∀ z, Phi z ↔ Psi z) → ((∀ z, Psi z) → (∀ z, Phi z)))).
    { clear n10_22l S1 S3. now Conj S2 S4 C1. }
    pose proof (Comp3_43 (∀ z, Phi z ↔ Psi z)
      ((∀ z, Phi z) → (∀ z, Psi z))
      ((∀ z, Psi z) → (∀ z, Phi z))
    ) as Comp3_43.
    MP Comp3_43 C1.
    rewrite <- Equiv4_01 in Comp3_43.
    exact Comp3_43.
  }
  exact S5.
Qed.

Theorem n10_28 (Phi Psi : Prop → Prop) :
  (∀ x, Phi x → Psi x) → ((∃ x, Phi x) → (∃ x, Psi x)).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, Phi x → Psi x) → (Phi Y → Psi Y)).
  { exact (n10_1 (fun x => Phi x → Psi x) Y). }
  assert (S2 : (∀ x, Phi x → Psi x) → ((¬Psi Y) → (¬Phi Y))).
  {
    pose proof (Transp2_16 (Phi Y) (Psi Y)) as Transp2_16.
    Syll S1 Transp2_16 S2.
    exact S2.
  }
  assert (S3 : (∀ x, Phi x → Psi x) → ∀ y, (¬Psi y) → (¬Phi y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, Phi x → Psi x) 
      → ((¬Psi y) → (¬Phi y)))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_21 (fun y => (¬Psi y) → (¬Phi y)) ((∀ x, Phi x → Psi x)))
      as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    MP n10_21l n10_11.
    exact n10_21l.
  }
  assert (S4 : (∀ x, Phi x → Psi x) → ((∀ y, ¬ Psi y) → (∀ y, ¬ Phi y))).
  {
    pose proof (n10_27 (fun y => ¬ Psi y) (fun y => ¬ Phi y)) as n10_27.
    Syll S3 n10_27 S4.
    exact S4.
  }
  assert (S5 : (∀ x, Phi x → Psi x) → ((∃ y, Phi y) → (∃ y, Psi y))).
  {
    pose proof (Transp2_16 (∀ y, ¬ Psi y) (∀ y, ¬ Phi y)) as Transp2_16.
    Syll S4 Transp2_16 S5.
    repeat rewrite <- n10_01 in S5.
    exact S5.
  }
  exact S5.
Qed.

(* Perhaps the most horrible concentration of proof I have ever seen *)
Theorem n10_281 (Phi Psi : Prop → Prop) :
  (∀ x, Phi x ↔ Psi x) → ((∃ x, Phi x) ↔ (∃ x, Psi x)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  (* ******** *)
  pose proof (n10_22 (fun x => Phi x → Psi x) (fun x => Psi x → Phi x))
    as n10_22.
  destruct n10_22 as [n10_22l n10_22r].
  setoid_rewrite <- Equiv4_01a in n10_22l.
  assert (Sa : (∀ x, Phi x ↔ Psi x) → 
    (∃ x, Phi x) → (∃ x, Psi x)).
  {
    pose proof (Simp3_26 (∀ x, Phi x → Psi x) (∀ x, Psi x → Phi x))
      as Simp3_26.
    Syll n10_22l Simp3_26 n10_22l1.
    pose proof (n10_28 Phi Psi) as n10_28a.
    Syll n10_22l1 n10_28a Sa.
    exact Sa.
  }
  assert (Sb : (∀ x, Phi x ↔ Psi x) → 
    (∃ x, Psi x) → (∃ x, Phi x)).
  {
    pose proof (Simp3_27 (∀ x, Phi x → Psi x) (∀ x, Psi x → Phi x))
      as Simp3_27.
    Syll n10_22l Simp3_27 n10_22l2.
    pose proof (n10_28 Psi Phi) as n10_28b.
    Syll n10_22l2 n10_28b Sb.
    exact Sb.
  }
  pose proof (Comp3_43 (∀ x, Phi x ↔ Psi x)
    ((∃ x, Phi x) → (∃ x, Psi x))
    ((∃ x, Psi x) → (∃ x, Phi x))
  ) as Comp3_43.
  assert (C1 : ((∀ x, Phi x ↔ Psi x) → (∃ x, Phi x) → (∃ x, Psi x))
    ∧ ((∀ x, Phi x ↔ Psi x) → (∃ x, Psi x) → (∃ x, Phi x))).
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

Theorem n10_29 (Phi Psi Chi : Prop → Prop) :
  ((∀ x, Phi x → Psi x) ∧ (∀ x, Phi x → Chi x)) ↔ (∀ x, Phi x → (Psi x ∧ Chi x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((∀ x, Phi x → Psi x) ∧ (∀ x, Phi x → Chi x)) 
    ↔ (∀ x, (Phi x → Psi x) ∧ (Phi x → Chi x))).
  {
    pose proof (n10_22 (fun x => Phi x → Psi x) 
      (fun x => Phi x → Chi x)) as n10_22.
    simpl in n10_22.
    symmetry in n10_22.
    exact n10_22.
  }
  assert (S2 : ((Phi X → Psi X) ∧ (Phi X → Chi X)) 
    ↔ (Phi X → (Psi X ∧ Chi X))).
  { exact (n4_76 (Phi X) (Psi X) (Chi X)). }
  assert (S3 : ∀ x, ((Phi x → Psi x) ∧ (Phi x → Chi x)) 
    ↔ (Phi x → (Psi x ∧ Chi x))).
  {
    pose proof (n10_11 X (fun x => ((Phi x → Psi x) ∧ (Phi x → Chi x)) 
      ↔ (Phi x → (Psi x ∧ Chi x)))) as n10_11.
    MP n10_11 S3.
    exact n10_11.
  }
  assert (S4 : (∀ x, (Phi x → Psi x) ∧ (Phi x → Chi x))
    ↔ (∀ x, Phi x → (Psi x ∧ Chi x))).
  {
    pose proof (n10_271
      (fun x => (Phi x → Psi x) ∧ (Phi x → Chi x))
      (fun x => Phi x → (Psi x ∧ Chi x))
    ) as n10_271.
    MP n10_271 S3.
    exact n10_271.
  }
  assert (S5 : ((∀ x, Phi x → Psi x) ∧ (∀ x, Phi x → Chi x)) ↔ (∀ x, Phi x → (Psi x ∧ Chi x))).
  {
    assert (C1 : 
      (((∀ x, Phi x → Psi x) ∧ (∀ x, Phi x → Chi x)) 
        ↔ (∀ x, (Phi x → Psi x) ∧ (Phi x → Chi x)))
      ∧ ((∀ x, (Phi x → Psi x) ∧ (Phi x → Chi x))
         ↔ (∀ x, Phi x → (Psi x ∧ Chi x)))).
    { clear S2 S3. now Conj S1 S4 C1. }
    pose proof (n4_22
      ((∀ x, Phi x → Psi x) ∧ (∀ x, Phi x → Chi x))
      (∀ x, (Phi x → Psi x) ∧ (Phi x → Chi x))
      (∀ x, Phi x → (Psi x ∧ Chi x))
    ) as n4_22.
    MP n4_22 C1.
    exact n4_22.
  }
  exact S5.
Qed.

(* Barbara's syllogism 2nd form *)

Theorem n10_3 (Phi Psi Chi : Prop → Prop) :
  ((∀ x, Phi x → Psi x) ∧ (∀ x, Psi x → Chi x)) → ∀ x, Phi x → Chi x.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (n10_22 (fun x => Phi x → Psi x) (fun x => Psi x → Chi x)) 
    as n10_22a.
  assert (S1 : ((∀ x, Phi x → Psi x) ∧ (∀ x, Psi x → Chi x))
    → ∀ x, (Phi x → Psi x) ∧ (Psi x → Chi x)).
  {
    (* n10_221 ignored *)
    destruct n10_22a as [n10_22l n10_22r].
    exact n10_22r.
  }
  assert (S2 : ((∀ x, Phi x → Psi x) ∧ (∀ x, Psi x → Chi x))
    → ∀ x, (Phi x → Chi x)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    (* Original proof here has abbreviated a lot of proofs being explained separately *)
    (* Note how the original proof here introduces a real variable *)
    assert (Sy1 : (Phi X → Psi X) ∧ (Psi X → Chi X) → (Phi X → Chi X)).
    {
      pose proof (Syll2_06 (Phi X) (Psi X) (Chi X)) as Syll2_06.
      pose proof (Imp3_31 (Phi X → Psi X) (Psi X → Chi X) 
        (Phi X → Chi X)) as Imp3_31.
      MP Imp3_31 Syll2_06.
      exact Imp3_31.
    }
    assert (Sy2 : ∀ x, (Phi x → Psi x) ∧ (Psi x → Chi x) → (Phi x → Chi x)).
    {
      pose proof (n10_11 X (fun x => (Phi x → Psi x) 
        ∧ (Psi x → Chi x) → (Phi x → Chi x))) as n10_11.
      MP n10_11 Sy1.
      exact n10_11.
    }
    assert (Sy3 : (∀ x, (Phi x → Psi x) ∧ (Psi x → Chi x)) 
      → (∀ y, Phi y → Chi y)).
    {
      pose proof (n10_27 (fun x => (Phi x → Psi x) ∧ (Psi x → Chi x))
        (fun x => (Phi x → Chi x))) as n10_27.
      MP n10_27 Sy2.
      exact n10_27.
    }
    MP Sy3 S1_1.
    exact Sy3.
  }
  exact S2.
Qed.

Theorem n10_301 (Phi Psi Chi : Prop → Prop) :
  (∀ x, Phi x ↔ Psi x) ∧ (∀ x, Psi x ↔ Chi x) → ∀ x, Phi x ↔ Chi x.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  pose proof (n10_22 (fun x => Phi x ↔ Psi x) (fun x => Psi x ↔ Chi x))
    as S1.
  simpl in S1.
  assert (S2 : (∀ x, Phi x ↔ Psi x) ∧ (∀ x, Psi x ↔ Chi x) → ∀ x, Phi x ↔ Chi x).
  {
    pose proof (n4_22 (Phi X) (Psi X) (Chi X)) as n4_22.
    pose proof (n10_11 X
      (fun x =>
        ((Phi x ↔ Psi x) ∧ (Psi x ↔ Chi x)) 
        → (Phi x ↔ Chi x)
      )) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27
      (fun x => (Phi x ↔ Psi x) ∧ (Psi x ↔ Chi x))
      (fun x => (Phi x ↔ Chi x))
      ) as n10_27.
    MP n10_27 n10_11.
    pose proof (n10_22
      (fun x => (Phi x ↔ Psi x))
      (fun x => (Psi x ↔ Chi x)) 
      ) as n10_22.
    simpl in n10_22.
    destruct n10_22 as [n10_22l n10_22r].
    clear S1 n4_22 n10_11 n10_22l.
    Syll n10_22r n10_27 S2.
    exact S2.
  }
  exact S2.
Qed.

Theorem n10_31 (Phi Psi Chi : Prop → Prop) :
  (∀ x, Phi x → Psi x) → (∀ x, (Phi x ∧ Chi x) → (Psi x ∧ Chi x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ∀ x, (Phi x → Psi x) 
    → (Phi x ∧ Chi x) → (Psi x ∧ Chi x)).
  {
    pose proof (Fact3_45 (Phi X) (Psi X) (Chi X)) as Fact3_45.
    pose proof (n10_11 X (fun x => (Phi x → Psi x) 
      → (Phi x ∧ Chi x) → (Psi x ∧ Chi x))) as n10_11.
    MP n10_11 Fact3_45.
    exact n10_11.
  }
  assert (S2 : (∀ x, Phi x → Psi x) → (∀ x, (Phi x ∧ Chi x) → (Psi x ∧ Chi x))).
  {
    pose proof (n10_27 (fun x => Phi x → Psi x)
      (fun x => (Phi x ∧ Chi x) → (Psi x ∧ Chi x))) as n10_27.
    MP n10_27 S1.
    exact n10_27.
  }
  exact S2.
Qed.

Theorem n10_311 (Phi Psi Chi : Prop → Prop) :
  (∀ x, Phi x ↔ Psi x) → (∀ x, (Phi x ∧ Chi x) ↔ (Psi x ∧ Chi x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ∀ x, (Phi x ↔ Psi x) → ((Phi x ∧ Chi x) ↔ (Psi x ∧ Chi x))).
  {
    pose proof (n4_36 (Phi X) (Psi X) (Chi X)) as n4_36.
    pose proof (n10_11 X (fun x => (Phi x ↔ Psi x) 
      → ((Phi x ∧ Chi x) ↔ (Psi x ∧ Chi x)))) as n10_11.
    MP n10_11 n4_36.
    exact n10_11.
  }
  assert (S2 : (∀ x, Phi x ↔ Psi x) → (∀ x, (Phi x ∧ Chi x) ↔ (Psi x ∧ Chi x))).
  {
    pose proof (n10_27 (fun x => Phi x ↔ Psi x)
      (fun x => (Phi x ∧ Chi x) ↔ (Psi x ∧ Chi x))) as n10_27.
    MP S1 n10_27.
    exact n10_27.
  }
  exact S2.
Qed.

Theorem n10_32 (Phi Psi : Prop → Prop) :
  (Phi x <[- x -]> Psi x) ↔ (Psi x <[- x -]> Phi x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)))
    as Equiv4_01a.
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((Phi x) <[- x -]> (Psi x)) ↔ 
    ((Phi x -[ x ]> Psi x) ∧ (Psi x -[ x ]> Phi x))).
  {
    pose proof (n10_22
      (fun x => (Phi x → Psi x))
      (fun x => (Psi x → Phi x))) as n10_22.
    simpl in n10_22.
    setoid_rewrite <- Equiv4_01a in n10_22.
    2: { apply Equiv4_01. }
    exact n10_22.
  }
  assert (S2 : ((Phi x) <[-x-]> (Psi x)) ↔ 
    ((Psi x -[x]> Phi x) ∧ (Phi x -[x]> Psi x))).
  {
    pose proof (n4_3 ((Phi x) -[x]> (Psi x)) ((Psi x) -[x]> (Phi x))) 
      as n4_3.
    assert (C1 : ((Phi x <[- x -]> Psi x) ↔ 
      ((Phi x -[x]> Psi x) ∧ (Psi x -[x]> Phi x)))
      ∧
      ((Phi x -[x]> Psi x) ∧ Psi x -[x]> Phi x ↔ 
      (Psi x -[x]> Phi x) ∧ Phi x -[x]> Psi x)).
    { now Conj S1 n4_3 C1. }
    pose proof (n4_22
      ((Phi x) <[- x -]> (Psi x))
      (((Phi x) -[x]> (Psi x)) ∧ ((Psi x) -[x]> (Phi x)))
      (((Psi x) -[x]> (Phi x)) ∧ ((Phi x) -[x]> (Psi x)))
    ) as n4_22.
    MP n4_22 C1.
    exact n4_22.
  }
  assert (S3 : ((Phi x) <[- x -]> (Psi x)) ↔ 
    ((Psi x) <[- x -]> (Phi x))).
  {
    pose proof (n10_22 
      (fun x => (Psi x → Phi x))
      (fun x => (Phi x → Psi x))) as n10_22. 
    symmetry in n10_22.
    simpl in n10_22.
    assert (C1 : ((Phi x <[- x -]> Psi x) ↔ 
      ((Psi x -[x]> Phi x) ∧ (Phi x -[x]> Psi x)))
      ∧
      (((Psi x -[x]> Phi x) ∧ (Phi x -[x]> Psi x)) ↔ 
      ∀ x : Prop, (Psi x → Phi x) ∧ (Phi x → Psi x))).
    { now Conj S2 n10_22 C1. }
    pose proof (n4_22
      (Phi x <[- x -]> Psi x)
      ((Psi x -[x]> Phi x) ∧ (Phi x -[x]> Psi x))
      (∀ x : Prop, (Psi x → Phi x) ∧ (Phi x → Psi x))
    ) as n4_22.
    MP n4_22 C1.
    setoid_rewrite <- Equiv4_01a in n4_22.
    2: { apply Equiv4_01. }
    exact n4_22.
  }
  exact S3.
Qed.

Theorem n10_321 (Phi Psi Chi : Prop → Prop) :
  ((Phi x <[- x -]> Psi x) ∧ (Phi x <[- x -]> Chi x)) 
  → (Psi x <[- x -]> Chi x).
Proof.
  assert (S1 : ((Phi x <[- x -]> Psi x) ∧ (Phi x <[- x -]> Chi x))
    → ((Psi x <[- x -]> Phi x) ∧ (Phi x <[- x -]> Chi x))).
  {
    pose proof (n10_32 Phi Psi) as n10_32.
    destruct n10_32 as [n10_32l n10_32r].
    pose proof (Fact3_45 (Phi x<[-x-]>Psi x) (Psi x<[-x-]>Phi x)
      (Phi x <[- x -]> Chi x))as Fact3_45.
    clear n10_32r.
    MP Fact3_45 n10_32l.
    exact Fact3_45.
  }
  assert (S2 : ((Phi x <[- x -]> Psi x) ∧ (Phi x <[- x -]> Chi x)) 
    → (Psi x <[- x -]> Chi x)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    pose proof (n10_301 Psi Phi Chi) as n10_301.
    MP n10_301 S1_1.
    exact n10_301.
  }
  exact S2.
Qed.

Theorem n10_322 (Phi Psi Chi : Prop → Prop) :
  ((Psi x <[- x -]> Phi x) ∧ (Chi x <[- x -]> Phi x)) 
  → (Psi x <[- x -]> Chi x).
Proof.
  assert (S1 : ((Psi x <[- x -]> Phi x) ∧ (Chi x <[- x -]> Phi x))
    → ((Psi x <[- x -]> Phi x) ∧ (Phi x <[- x -]> Chi x))).
  {
    intro Hp.
    pose proof (n10_32 Chi Phi) as n10_32.
    (* Here we simplify the proof and omit related theorems. We directly use 
    `rewrite` for a `↔` relation, while strictly speaking it's only allowed
    for `=` relations. *)
    rewrite -> n10_32 in Hp.
    exact Hp.
  }
  assert (S2 : ((Psi x <[- x -]> Phi x) ∧ (Chi x <[- x -]> Phi x))
    → (Psi x <[- x -]> Chi x)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    pose proof (n10_301 Psi Phi Chi) as n10_301.
    MP n10_301 S1_1.
    exact n10_301.
  }
  exact S2.
Qed.

Theorem n10_33 (Phi : Prop → Prop) (P : Prop) :
  (∀ x, Phi x ∧ P) ↔ ((∀ x, Phi x) ∧ P).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (∀ x, Phi x ∧ P) → (Phi Y ∧ P)).
  {
    pose proof (n10_1 (fun x => Phi x ∧ P) Y) as n10_1.
    exact n10_1.
  }
  assert (S2 : (∀ x, Phi x ∧ P) → P).
  {
    pose proof (Simp3_27 (Phi Y) P) as Simp3_27.
    Syll S1 Simp3_27 S2.
    exact S2.
  }
  assert (S3 : (∀ x, Phi x ∧ P) → Phi Y).
  { 
    pose proof (Simp3_26 (Phi Y) P) as Simp3_26.
    Syll S1 Simp3_26 S3.
    exact S3.
  }
  assert (S4 : (∀ x, Phi x ∧ P) → (∀ y, Phi y)).
  {
    pose proof (n10_11 Y (fun y => (∀ x, Phi x ∧ P) → Phi y)) as n10_11.
    MP n10_11 S3.
    pose proof (n10_21 Phi (∀ x, Phi x ∧ P)) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    clear n10_21r.
    MP n10_21l n10_11.
    exact n10_21l.
  }
  assert (S5 : (∀ x, Phi x ∧ P) → (∀ y, Phi y) ∧ P).
  {
    (* Original text here seems unsatisfying in a sense of rigor *)
    assert (C1 : ((∀ x, Phi x ∧ P) → ∀ y, Phi y)
      ∧ ((∀ x, Phi x ∧ P) → P)).
    {
      clear S1 S3.
      move S2 after S4.
      now Conj S4 S2 C1.
    }
    pose proof (n4_76 (∀ x, Phi x ∧ P) (∀ y, Phi y) P) as n4_76.
    destruct n4_76 as [n4_76l n4_76r].
    clear n4_76r.
    MP n4_76l C1.
    exact n4_76l.
  }
  assert (S6 : (∀ y, Phi y) → Phi X).
  { now apply n10_1. }
  assert (S7 : ((∀ y, Phi y) ∧ P) → (Phi X ∧ P)).
  {
    pose proof (Fact3_45 (∀ y, Phi y) (Phi X) P) as Fact3_45.
    now MP Fact3_45 S6.
  }
  (* Is it that we don't have alpha equivalence in this logic system?! *)
  assert (S8 : ((∀ y, Phi y) ∧ P) → ∀ x, Phi x ∧ P).
  {
    pose proof n10_11 as n10_11.
    pose proof n10_21 as n10_21.
    pose proof (n10_11 X (fun x => (∀ y : Prop, Phi y) ∧ P 
      → Phi x ∧ P)) as n10_11.
    MP n10_11 S7.
    pose proof (n10_21 (fun x => Phi x ∧ P) ((∀ y : Prop, Phi y) ∧ P)) as n10_21.
    destruct n10_21 as [n10_21l n10_21r].
    clear n10_21r.
    now MP n10_21l n10_11.
  }
  assert (S9 : (∀ x, Phi x ∧ P) ↔ ((∀ x, Phi x) ∧ P)).
  {
    clear S1 S2 S3 S4 S6 S7.
    move S5 after S8.
    Conj S8 S5 S9.
    now Equiv S9.
  }
  exact S9.
Qed.

Theorem n10_34 (Phi : Prop → Prop) (P : Prop) :
  (∃ x, Phi x → P) ↔ ((∀ x, Phi x) → P).
Proof.
  assert (S1 : (∃ x, Phi x → P) ↔ ¬(∀ x, ¬(Phi x → P))).
  {
    pose proof (n4_2 (∃ x : Prop, Phi x → P)) as n4_2.
    now rewrite -> n10_01 in n4_2 at 2.
  }
  assert (S2 : (∃ x, Phi x → P) ↔ ¬(∀ x, Phi x ∧ ¬P)).
  {
    (* n10_271 ignored - idk how should it be used *)
    now setoid_rewrite -> n4_61 in S1.
  }
  assert (S3 : (∃ x, Phi x → P) ↔ ¬((∀ x, Phi x) ∧ ¬P)).
  {
    (* In rigorous sense we should somehow use transitivity on equiv relation,
     or MP then compose back  *)
    now rewrite -> n10_33 in S2.
  }
  assert (S4 : (∃ x, Phi x → P) ↔ (~∀ x, Phi x) ∨ P).
  { now setoid_rewrite -> n4_53 in S3. }
  assert (S5 : (∃ x, Phi x → P) ↔ ((∀ x, Phi x ) → P)).
  { now setoid_rewrite <- n4_6 in S4. }
  exact S5.
Qed.

Theorem n10_35 (Phi : Prop → Prop) (P : Prop) :
  (∃ x, P ∧ Phi x) ↔ P ∧ (∃ x, Phi x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (P ∧ Phi X) → P).
  { exact (Simp3_26 P (Phi X)). }
  assert (S2 : ∀ x, (P ∧ Phi x) → P).
  {
    pose proof (n10_11 X (fun x => ((P ∧ Phi x) → P))) as n10_11.
    now MP n10_11 S1.
  }
  assert (S3 : (exists x, (P ∧ Phi x)) → P).
  {
    (* pose proof n10_23 as n10_23. *)
    pose proof (n10_23 (fun x => P ∧ Phi x) P) as n10_23.
    simpl in n10_23.
    (* omit the MP we should use *)
    now rewrite -> n10_23 in S2.
  }
  assert (S4 : (P ∧ Phi X) → (Phi X)).
  { exact (Simp3_27 P (Phi X)). }
  assert (S5 : ∀ x, (P ∧ Phi x) → Phi x).
  {
    pose proof (n10_11 X (fun x => ((P ∧ Phi x) → Phi x))) as n10_11.
    now MP n10_11 S4.
  }
  assert (S6 : (exists x, P ∧ Phi x) → (exists x, Phi x)).
  {
    pose proof (n10_28 (fun x => P ∧ Phi x) Phi) as n10_28.
    now MP n10_28 S5.
  }
  assert (S7 : P → (Phi X → (P ∧ Phi X))).
  { exact (n3_2 P (Phi X)). }
  assert (S8 : P → (∀ x, Phi x → (P ∧ Phi x))).
  {
    pose proof (n10_11 X (fun x => Phi x → (P ∧ Phi x))) as n10_11.
    simpl in n10_11.
    Syll n10_11 S7 S8.
    (* n10_21 ignored - the difference isn't significant *)
    exact S8.
  }
  assert (S9 : P → ((exists x, Phi x) → (exists x, P ∧ Phi x))).
  {
    pose proof (n10_28 Phi (fun x => P ∧ Phi x)) as n10_28.
    now Syll n10_28 S8 S9.
  }
  assert (S10 : (∃ x, P ∧ Phi x) ↔ P ∧ (∃ x, Phi x)).
  {
    clear S1 S2 S4 S5 S7 S8.
    pose proof (Imp3_31 P ((∃ x : Prop, Phi x)) (∃ x : Prop, P ∧ Phi x))
      as Imp3_31.
    MP Imp3_31 S9.
    assert (C1 : ((∃ x : Prop, P ∧ Phi x) → P) 
      ∧ ((∃ x : Prop, P ∧ Phi x) → ∃ x : Prop, Phi x)).
    { now Conj S3 S6 C1. }
    pose proof (Comp3_43 (∃ x : Prop, P ∧ Phi x) P (∃ x : Prop, Phi x))
      as Comp3_43.
    MP Comp3_43 C1.
    assert (C2 : ((∃ x : Prop, P ∧ Phi x) → P ∧ ∃ x : Prop, Phi x)
      ∧
      (P ∧ (∃ x : Prop, Phi x) → ∃ x : Prop, P ∧ Phi x)).
    { now Conj Comp3_43 Imp3_31 C2. }
    now Equiv C2.
  }
  exact S10.
Qed.

Theorem n10_36 (Phi : Prop → Prop) (P : Prop) :
  (∃ x, Phi x ∨ P) ↔ (∃ x, Phi x) ∨ P.
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (Phi X ∨ P) ↔ ((~Phi X) → P)).
  {
    pose proof (n4_64 (Phi X) P) as n4_64.
    now symmetry in n4_64.
  }
  assert (S2 : ∀ x, (Phi x ∨ P) ↔ ((~Phi x) → P)).
  {
    pose proof (n10_11 X (fun x => (Phi x ∨ P) ↔ ((~Phi x) → P))) 
      as n10_11.
    now MP n10_11 S1.
  }
  assert (S3 : (exists x, Phi x ∨ P) ↔ (exists x, (~Phi x) → P)).
  {
    pose proof (n10_281 (fun x => Phi x ∨ P) (fun x => (~Phi x) → P)) 
      as n10_281.
    now MP n10_281 S2.
  }
  assert (S4 : (exists x, Phi x ∨ P) ↔ ((∀ x, ~Phi x) → P)).
  {
    (* Same as previous attempts, here we directly use `rewrite` rather than
    going on all the decomposing and recomposing *)
    now rewrite -> n10_34 in S3.
  }
  assert (S5 : (exists x, Phi x ∨ P) ↔ ((∃ x, Phi x) ∨ P)).
  {
    rewrite -> n4_6 in S4.
    rewrite <- n10_01 in S4.
    exact S4.
  }
  exact S5.
Qed.

Theorem n10_37 (Phi : Prop → Prop) (P : Prop) :
  (∃ x, P → Phi x) ↔ (P → ∃ x, Phi x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n10_36 Phi (~P)) as n10_36.
  rewrite -> n4_31 in n10_36.
  rewrite <- Impl1_01 in n10_36.
  replace (∃ x : Prop, Phi x ∨ ¬ P) with 
    (∃ x : Prop, ¬ P ∨ Phi x) in n10_36.
  2: {
    apply propositional_extensionality.
    split; now setoid_rewrite -> n4_31 at 1.
  }
  now setoid_rewrite <- Impl1_01a in n10_36.
Qed.

Theorem n10_39 (Phi Psi Chi Theta : Prop → Prop) :
  ((Phi x -[ x ]> Chi x) ∧ (Psi x -[ x ]> Theta x)) 
  → (Phi x ∧ Psi x) -[ x ]> (Chi x ∧ Theta x).
Proof.
  assert (S1 : ((Phi x -[ x ]> Chi x) ∧ (Psi x -[ x ]> Theta x))
    → (∀ x, (Phi x → Chi x) ∧ (Psi x → Theta x))).
  {
    pose proof (n10_22 (fun x => Phi x → Chi x) (fun x => Psi x → Theta x))
      as n10_22.
    symmetry in n10_22.
    now destruct n10_22.
  }
  assert (S2 : ((Phi x -[ x ]> Chi x) ∧ (Psi x -[ x ]> Theta x))
    → (∀ x, (Phi x ∧ Psi x) → (Chi x ∧ Theta x))).
  {
    intro Hp.
    (* TODO: figure out if `intro x` can be done according to original proof *)
    intro x.
    pose proof (S1 Hp x) as S1_1.
    pose proof (n3_47 (Phi x) (Psi x) (Chi x) (Theta x)) as n3_47.
    MP n3_47 S1_1.
    (* pose proof n10_27 as n10_27. *)
    exact n3_47.
  }
  exact S2.
Qed.

Theorem n10_4 (Phi Psi Chi Theta : Prop → Prop) :
  ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
  → (Phi x ∧ Psi x) <[- x -]> (Chi x ∧ Theta x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0)) as Equiv4_01a.
  (* ******** *)
  pose proof (n10_22 (fun x => Phi x -> Chi x) 
    (fun x => Chi x -> Phi x)) as n10_22a.
  setoid_rewrite <- Equiv4_01a in n10_22a.
  destruct n10_22a as [n10_22al n10_22ar]. clear n10_22ar.
  pose proof (n10_22 (fun x => Psi x -> Theta x)
    (fun x => Theta x -> Psi x)) as n10_22b.
  setoid_rewrite <- Equiv4_01a in n10_22b.
  destruct n10_22b as [n10_22bl n10_22br]. clear n10_22br.
  (* This step has omitted a lot of things *)
  assert (S1 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> ((Phi x -[ x ]> Chi x) /\ (Psi x -[ x ]> Theta x))).
  {
    pose proof (Simp3_26 (Phi x -[x]> Chi x) (Chi x -[x]> Phi x))
      as Simp3_26a.
    Syll n10_22al Simp3_26a n10_22al_1.
    pose proof (Simp3_26 (Psi x -[x]> Theta x) (Theta x -[x]> Psi x))
      as Simp3_26b.
    Syll n10_22bl Simp3_26b n10_22bl_1.
    clear n10_22al n10_22bl Simp3_26a Simp3_26b.
    assert (C1 : (Phi x<[-x-]>Chi x  →  Phi x-[x]>Chi x)
      /\
      (Psi x<[-x-]>Theta x  →  Psi x-[x]>Theta x)).
    { now Conj n10_22al_1 n10_22bl_1 C1. }
    pose proof (n3_47 
      (Phi x <[-x-]> Chi x) (Psi x <[-x-]> Theta x)
      (Phi x -[x]> Chi x) (Psi x -[x]> Theta x))
      as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> (Phi x /\ Psi x) -[x]> (Chi x /\ Theta x)).
  {
    pose proof (n10_39 Phi Psi Chi Theta) as n10_39.
    now Syll n10_39 S1 S2.
  }
  assert (S3 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> (Chi x /\ Theta x) -[x]> (Phi x /\ Psi x)).
  {
    pose proof (Simp3_27 (Phi x-[x]>Chi x) (Chi x -[x]> Phi x))
      as Simp3_27a.
    Syll n10_22al Simp3_27a n10_22al_1.
    pose proof (Simp3_27 (Psi x-[x]>Theta x) (Theta x-[x]>Psi x))
      as Simp3_27b.
    Syll n10_22bl Simp3_27b n10_22bl_1.
    clear n10_22al n10_22bl Simp3_27a Simp3_27b.
    assert (C1 : (Phi x<[-x-]>Chi x  →  Chi x-[x]>Phi x )
      /\
      (Psi x<[-x-]>Theta x  →  Theta x-[x]>Psi x )).
    { now Conj n10_22al_1 n10_22bl_1 C1. }
    pose proof (n3_47
      (Phi x<[-x-]>Chi x) (Psi x<[-x-]>Theta x)
      (Chi x-[x]>Phi x ) (Theta x-[x]>Psi x)
    ) as n3_47.
    MP n3_47 C1.
    pose proof (n10_39 Chi Theta Phi Psi) as n10_39.
    now Syll n3_47 n10_39 S3.
  }
  assert (S4 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> (((Phi x /\ Psi x) -[x]> (Chi x /\ Theta x))
        /\
        ((Chi x /\ Theta x) -[x]> (Phi x /\ Psi x)))).
  {
    assert (C1 : 
      ((Phi x <[-x-]> Chi x) ∧ Psi x <[-x-]> Theta x 
        → (Phi x ∧ Psi x)-[x]>Chi x ∧ Theta x)
      /\
      ((Phi x <[-x-]> Chi x ) ∧ Psi x <[-x-]> Theta x 
        → (Chi x ∧ Theta x)-[x]>Phi x ∧ Psi x)).
    { now Conj S1 S3 C1. }
    pose proof (Comp3_43
      ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
      ((Phi x /\ Psi x) -[x]> (Chi x /\ Theta x))
      ((Chi x /\ Theta x) -[x]> (Phi x /\ Psi x)))
      as Comp3_43.
    now MP Comp3_43 C1.
  }
  assert (S5 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    → (Phi x ∧ Psi x) <[- x -]> (Chi x ∧ Theta x)).
  {
    intro Hp.
    pose proof (S4 Hp) as S4_1.
    rewrite <- n10_22 in S4_1.
    setoid_rewrite <- Equiv4_01a in S4_1.
    exact S4_1.
  }
  exact S5.
Qed.

Theorem n10_41 (Phi Psi : Prop → Prop) :
  (∀ x, Phi x) ∨ (∀ x, Psi x) → (∀ x, Phi x ∨ Psi x).
Proof.
  (* TOOLS *)
  set (Y := Real "y").
  (* ******** *)
  assert (S1 : (forall x, Phi x) -> Phi Y).
  { now apply n10_1. }
  assert (S2 : (forall x, Phi x) -> (Phi Y ∨  Psi Y)).
  {
    pose proof (n2_2 (Phi Y) (Psi Y)) as n2_2.
    now Syll S1 n2_2 S2.
  }
  assert (S3 : (forall x, Psi x) -> Psi Y).
  { now apply n10_1. }
  assert (S4 : (forall x, Psi x) -> (Phi Y ∨  Psi Y)).
  {
    pose proof (Add1_3 (Phi Y) (Psi Y)) as Add1_3.
    now Syll S2 Add1_3 S3.
  }
  assert (S5 : ((forall x, Phi x) -> (Phi Y ∨  Psi Y))
    /\ ((forall x, Psi x) -> (Phi Y ∨  Psi Y))).
  {
    pose proof (n10_13
      (fun y => (forall x, Phi x) -> (Phi y ∨  Psi y))
      (fun y => (forall x, Psi x) -> (Phi y ∨  Psi y))
      Y) as n10_13.
    MP n10_13 S2.
    MP n10_13 S4.
    exact n10_13.
  }
  assert (S6 : ((forall x, Phi x) ∨  (forall x, Psi x)) 
    -> (Phi Y ∨  Psi Y)).
  {
    pose proof (n3_44
      (Phi Y ∨ Psi Y)
      (∀ x : Prop, Phi x)
      (∀ x : Prop, Psi x)) as n3_44.
    now MP n3_44 S5.
  }
  assert (S7 : ((forall x, Phi x) ∨  (forall x, Psi x)) 
    -> (forall y, Phi y ∨  Psi y)).
  {
    pose proof (n10_11 Y
      (fun y =>
        ((forall x, Phi x) ∨  (forall x, Psi x)) 
        -> (Phi y ∨  Psi y))) as n10_11.
    MP n10_11 S6.
    pose proof (n10_21 (fun y => Phi y ∨  Psi y)
      ((forall x, Phi x) ∨  (forall x, Psi x))) as n10_21.
    (* We don't use `MP` here and directly rewrite *)
    now rewrite -> n10_21 in n10_11.
  }
  exact S7.
Qed.

Theorem n10_411 (Phi Psi Chi Theta : Prop → Prop) :
  ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
  → (Phi x ∨ Psi x) <[- x -]> (Chi x ∨ Theta x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> ((Phi X ↔ Chi X) /\ (Psi X ↔ Theta X))).
  {
    exact (n10_14 (fun x => Phi x ↔ Chi x) 
      (fun x => Psi x ↔ Theta x) X).
  }
  assert (S2 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> ((Phi X ∨  Psi X) ↔ (Chi X ∨  Theta X))).
  {
    pose proof (n4_39 (Phi X) (Psi X) (Chi X) (Theta X)) as n4_39.
    now Syll n4_39 S1 S2.
  }
  assert (S3 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    → (Phi x ∨ Psi x) <[- x -]> (Chi x ∨ Theta x)).
  {
    pose proof (n10_11 X
      (fun x0 =>
        ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
          -> ((Phi x0 ∨  Psi x0) ↔ (Chi x0 ∨  Theta x0)))) 
      as n10_11.
    MP S2 n10_11.
    pose proof (n10_21
      (fun x0 => ((Phi x0 ∨  Psi x0) ↔ (Chi x0 ∨  Theta x0)))
      ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    ) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  exact S3.
Qed.

Theorem n10_412 (Phi Psi : Prop → Prop) :
  (Phi x <[- x -]> Psi x) ↔ (¬ Phi x <[- x -]> ¬ Psi x).
Proof.
  set (X := Real "x").
  pose proof (Transp4_11 (Phi X) (Psi X)) as Transp4_11.
  pose proof (n10_11 X (fun x =>
    (Phi x ↔ Psi x) ↔ (¬ Phi x ↔ ¬ Psi x))) as n10_11.
  MP n10_11 Transp4_11.
  pose proof (n10_271 (fun x => Phi x ↔ Psi x) 
    (fun x => ¬ Phi x ↔ ¬ Psi x)) as n10_271.
  now MP n10_11 n10_271.
Qed.

Theorem n10_413 (Phi Psi Chi Theta : Prop → Prop) :
  ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
  → (Phi x → Psi x) <[- x -]> (Chi x → Theta x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
  -> ((~Phi x) ∨  Psi x) <[- x -]> ((~Chi x) ∨  Theta x)).
  {
    pose proof (n10_411 (fun x => ~ Phi x) Psi 
      (fun x => ~ Chi x) Theta) as n10_411.
    simpl in n10_411.
    pose proof (n10_412 Phi Chi) as n10_412.
    now rewrite <- n10_412 in n10_411.
  }
  assert (S2 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    → (Phi x → Psi x) <[- x -]> (Chi x → Theta x)).
  { now setoid_rewrite <- Impl1_01a in S1. }
  exact S2.
Qed.

Theorem n10_414 (Phi Psi Chi Theta : Prop → Prop) :
  ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
  → (Phi x ↔ Psi x) <[- x -]> (Chi x ↔ Theta x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0)) as Equiv4_01a.
  (* ******** *)
  assert (S1 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    -> ((Psi x -> Phi x) <[- x -]> (Theta x -> Chi x))).
  {
    pose proof (n10_413 Psi Phi Theta Chi) as n10_413.
    (* as always, ignore some chores *)
    now rewrite -> n4_3 in n10_413 at 1.
  }
  assert (S2 : ((Phi x <[- x -]> Chi x) ∧ ((Psi x <[- x -]> Theta x)))
    → (Phi x ↔ Psi x) <[- x -]> (Chi x ↔ Theta x)).
  {
    pose proof (n10_413 Phi Psi Chi Theta) as n10_413.
    assert (C1 :
      (( Phi x<[-x-]>Chi x ) ∧  Psi x<[-x-]>Theta x  →  
        (Psi x → Phi x)<[-x-]>(Theta x → Chi x))
      /\
      (( Phi x<[-x-]>Chi x ) ∧  Psi x<[-x-]>Theta x  →  
        (Phi x → Psi x)<[-x-]>(Chi x → Theta x) )).
    { now Conj S1 n10_413 C1. }
    pose proof (n10_4
      (fun x => Psi x → Phi x)
      (fun x => Phi x → Psi x)
      (fun x => Theta x → Chi x)
      (fun x => Chi x → Theta x)
      ) as n10_4.
    pose proof (n4_76
      (( Phi x<[-x-]>Chi x ) ∧  Psi x<[-x-]>Theta x)
      ((Psi x → Phi x)<[-x-]>(Theta x → Chi x))
      ((Phi x → Psi x)<[-x-]>(Chi x → Theta x))
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

Theorem n10_42 (Phi Psi : Prop → Prop) :
  (∃ x, Phi x) ∨ (∃ x, Psi x) ↔ (∃ x, Phi x ∨ Psi x).
Proof.
  assert (S1 : ((forall x, ~ Phi x) /\ (forall x, ~ Psi x))
    ↔ (forall x, (~ Phi x) /\ (~ Psi x))).
  {
    pose proof (n10_22 
      (fun x => ~ Phi x) (fun x => ~ Psi x)) as n10_22.
    now symmetry in n10_22.
  }
  assert (S2 : (~((forall x, ~ Phi x) /\ (forall x, ~ Psi x)))
    ↔ (~(forall x, (~ Phi x) /\ (~ Psi x)))).
  { now rewrite -> Transp4_11 in S1. }
  assert (S3 : ((~(forall x, ~ Phi x)) ∨  (~(forall x, ~ Psi x)))
    ↔ (~(forall x, ~(Phi x ∨   Psi x)))).
  {
    rewrite -> n4_51 in S2.
    setoid_rewrite -> n4_56 in S2.
    (* n10_271 ignored - does it have something to do with 
      `setoid_rewrite`?! *)
    exact S2.
  }
  assert (S4 : (∃ x, Phi x) ∨ (∃ x, Psi x) ↔ (∃ x, Phi x ∨ Psi x)).
  {
    setoid_rewrite ->  n10_253_alt in S3.
    now setoid_rewrite <- n4_13 in S3.
  }
  exact S4.
Qed.

Theorem n10_43 (Phi Psi : Prop → Prop) (X : Prop) :
  ((Phi z <[- z -]> Psi z) ∧ Phi X) ↔
  ((Phi z <[- z -]> Psi z) ∧ Psi X).
Proof.
  assert (S1 : (Phi z <[- z -]> Psi z) -> (Phi X ↔ Psi X)).
  { now apply n10_1. }
  assert (S2 : ((Phi z <[- z -]> Psi z) ∧ Phi X) ↔
    ((Phi z <[- z -]> Psi z) ∧ Psi X)).
  { now rewrite -> n5_32 in S1. }
  exact S2.
Qed.

Theorem n10_5 (Phi Psi : Prop → Prop) :
  (∃ x, Phi x ∧ Psi x) → ((∃ x, Phi x) ∧ (∃ x, Psi x)).
Proof. 
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : forall x, (Phi x /\ Psi x) -> Phi x).
  {
    pose proof (Simp3_26 (Phi X) (Psi X)) as Simp3_26.
    pose proof (n10_11 X (fun x => Phi x ∧ Psi x → Phi x)) as n10_11.
    now MP Simp3_26 n10_11.
  }
  assert (S2 : (exists x, (Phi x /\ Psi x)) -> (exists x, Phi x)).
  {
    pose proof (n10_28 (fun x => Phi x ∧ Psi x) Phi) as n10_28.
    now MP S1 n10_28.
  }
  assert (S3 : forall x, (Phi x /\ Psi x) -> Psi x).
  {
    pose proof (Simp3_27 (Phi X) (Psi X)) as Simp3_26.
    pose proof (n10_11 X (fun x => Phi x ∧ Psi x → Psi x)) as n10_11.
    now MP Simp3_27 n10_11.
  }
  assert (S4 : (exists x, (Phi x /\ Psi x)) -> (exists x, Psi x)).
  {
    pose proof (n10_28 (fun x => Phi x ∧ Psi x) Psi) as n10_28.
    now MP S3 n10_28.
  }
  assert (S5 : (∃ x, Phi x ∧ Psi x) → ((∃ x, Phi x) ∧ (∃ x, Psi x))).
  {
    assert (C1 : ((∃ x : Prop, Phi x ∧ Psi x) → ∃ x : Prop, Phi x)
      /\
      ((∃ x : Prop, Phi x ∧ Psi x) → ∃ x : Prop, Psi x)).
    { now Conj S2 S4 C1. }
    pose proof (Comp3_43
      (∃ x : Prop, Phi x ∧ Psi x)
      (∃ x : Prop, Phi x)
      (∃ x : Prop, Psi x)) as Comp3_43.
    now MP C1 Comp3_43.
  }
  exact S5.
Qed.

Theorem n10_51 (Phi Psi : Prop → Prop) :
  ¬(∃ x, Phi x ∧ Psi x) ↔ (Phi x -[ x ]> ¬ Psi x).
Proof.
  assert (S1 : (¬(∃ x, Phi x ∧ Psi x)) 
    ↔ (forall x, ~(Phi x /\ Psi x))).
  { now apply n10_252. }
  assert (S2 : ¬(∃ x, Phi x ∧ Psi x) ↔ (Phi x -[ x ]> ¬ Psi x)).
  {
    setoid_rewrite -> n4_51 in S1.
    setoid_rewrite <- n4_62 in S1.
    (* n10_271 ignored *)
    exact S1.
  }
  exact S2.
Qed.

Theorem n10_52 (Phi : Prop → Prop) (P : Prop) :
  (∃ x, Phi x) → ((∀ x, Phi x → P) ↔ P).
Proof.
  assert (S1 : (∃ x, Phi x) -> (P ↔ ((exists x, Phi x) -> P))).
  {
    pose proof (n5_5 (exists x, Phi x) P) as n5_5.
    now symmetry in n5_5.
  }
  assert (S2 : (∃ x, Phi x) -> (P ↔ (forall x, Phi x -> P))).
  {
    pose n10_23 as n10_23.
    now setoid_rewrite <- n10_23 in S1 at 2.
  }
  now symmetry in S2.
Qed.

Theorem n10_53 (Phi Psi : Prop → Prop) :
  ¬(∃ x, Phi x) → (Phi x -[ x ]> Psi x).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : forall x, (~ Phi x) -> (Phi x -> Psi x)).
  {
    pose proof (n2_21 (Phi X) (Psi X)) as n2_21.
    pose proof (n10_11 X (fun x => (~ Phi x) -> (Phi x -> Psi x))) 
      as n10_11.
    now MP n2_21 n10_11.
  }
  assert (S2 : (forall x, ~ Phi x) -> (forall x, Phi x -> Psi x)).
  {
    pose proof (n10_27 (fun x => ~ Phi x) (fun x => Phi x -> Psi x)) 
      as n10_27.
    now MP S1 n10_27.
  }
  assert (S3 : ¬(∃ x, Phi x) → (Phi x -[ x ]> Psi x)).
  { now rewrite <- n10_252 in S2. }
  exact S3.
Qed.

Theorem n10_541 (Phi Psi : Prop → Prop) (P : Prop) :
  (Phi y -[ y ]> (P ∨ Psi y)) ↔ (P \/ (Phi y -[ y ]> Psi y)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : (Phi y -[ y ]> (P ∨ Psi y)) 
    ↔ (forall y, (~ Phi y) ∨  P ∨ Psi y)).
  {
    pose proof (n4_2 (Phi y -[ y ]> (P ∨ Psi y))) as n4_2.
    now setoid_rewrite -> Impl1_01a in n4_2 at 2.
  }
  assert (S2 : (Phi y -[ y ]> (P ∨ Psi y)) 
    ↔ (forall y, P \/ (~Phi y) \/ Psi y)).
  {
    (* TODO: change with  a better way for this
    Assoc1_5 itself should be able to form a equiv relation
    design with different instantiation as tool
    *)
    replace (∀ y : Prop, ¬ Phi y ∨ P ∨ Psi y) with 
      (∀ y : Prop, P ∨ ¬ Phi y ∨ Psi y) in S1.
    2: {
        apply propositional_extensionality.
        split;
        intros H y;
        pose (H y) as H0;
        apply Assoc1_5 in H0;
        exact H0.
      }
    (* n10_271 ignored *)
    exact S1.
  }
  assert (S3 : (Phi y -[ y ]> (P ∨ Psi y)) 
    ↔ (P \/ (forall y, (~Phi y) \/ Psi y))).
  { now rewrite -> n10_2 in S2. }
  assert (S4 : (Phi y -[ y ]> (P ∨ Psi y)) ↔ (P \/ (Phi y -[ y ]> Psi y))).
  { now setoid_rewrite <- Impl1_01a in S3. }
  exact S4.
Qed.

Theorem n10_542 (Phi Psi : Prop -> Prop) (P : Prop) :
  (Phi y -[ y ]> (P -> Psi y)) ↔ (P -> (Phi y -[ y ]> Psi y)).
Proof.
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  pose proof (n10_541 Phi Psi (~P)) as n10_541.
  now setoid_rewrite <- Impl1_01a in n10_541.
Qed.

Theorem n10_55 (Phi Psi : Prop → Prop) :
  ((∃ x, Phi x ∧ Psi x) ∧ (Phi x -[ x ]> Psi x))
  ↔ ((∃ x, Phi x) ∧ (Phi x -[ x ]> Psi x)).
Proof.
  (* TOOLS *)
  set (X := Real "x").
  (* ******** *)
  assert (S1 : (Phi X -> Psi X) -> ((Phi X /\ Psi X) <-> Phi X)).
  {
    pose proof (n4_71 (Phi X) (Psi X)) as n4_71.
    replace (Phi X ↔ Phi X ∧ Psi X) with (Phi X ∧ Psi X ↔ Phi X)
      in n4_71.
    2: { apply propositional_extensionality. apply n4_21. }
    now destruct n4_71.
  }
  assert (S2 : (Phi x -[x]> Psi x) 
    -> (forall x, (Phi x /\ Psi x) <-> Phi x)).
  {
    pose proof (n10_11 X (fun x => 
      (Phi x -> Psi x) -> ((Phi x /\ Psi x) <-> Phi x))) as n10_11.
    MP S1 n10_11.
    pose proof (n10_27 (fun x => Phi x -> Psi x)
      (fun x => (Phi x /\ Psi x) <-> Phi x)) as n10_27.
    now MP n10_11 n10_27.
  }
  assert (S3 : (Phi x -[x]> Psi x) 
    -> ((exists x, Phi x /\ Psi x) <-> (exists x, Phi x))).
  {
    pose proof (n10_281 (fun x => Phi x /\ Psi x) Phi) as n10_281.
    now Syll S2 n10_281 S3.
  }
  assert (S4 : ((∃ x, Phi x ∧ Psi x) ∧ (Phi x -[ x ]> Psi x))
    ↔ ((∃ x, Phi x) ∧ (Phi x -[ x ]> Psi x))).
  {
    rewrite -> n5_32 in S3.
    rewrite -> n4_3 in S3.
    replace (( Phi x-[x]>Psi x ) ∧ ∃ x : Prop, Phi x)
      with ((∃ x : Prop, Phi x) ∧ ( Phi x-[x]>Psi x ))
      in S3.
    2: { apply propositional_extensionality. now rewrite -> n4_3. }
    exact S3.
  }
  exact S4.
Qed.

Theorem n10_56 (Phi Psi Chi : Prop → Prop) :
  ((Phi x -[ x ]> Psi x) ∧ (∃ x, Phi x ∧ Chi x))
  → (∃ x, Psi x ∧ Chi x).
Proof.
  assert (S1 : (Phi x -[ x ]> Psi x) 
    -> ((Phi x /\ Chi x) -[x]> (Psi x /\ Chi x))).
  { apply n10_31. }
  assert (S2 : (Phi x -[ x ]> Psi x) 
    -> ((exists x, Phi x /\ Chi x) -> (exists x, Psi x /\ Chi x))).
  {
    pose proof (n10_28 (fun x => (Phi x ∧ Chi x)) 
      (fun x => Psi x ∧ Chi x)) as n10_28.
    now Syll S1 n10_28 S2.
  }
  assert (S3 : ((Phi x -[ x ]> Psi x) ∧ (∃ x, Phi x ∧ Chi x))
    → (∃ x, Psi x ∧ Chi x)).
  {
    pose proof (Imp3_31 (Phi x-[x]>Psi x) 
      (∃ x : Prop, Phi x ∧ Chi x)
      (∃ x, Psi x ∧ Chi x)) as Imp3_31.
    now MP S2 Imp3_31.
  }
  exact S3.
Qed.

Theorem n10_57 (Phi Psi Chi : Prop → Prop) :
  (Phi x -[ x ]> (Psi x ∨ Chi x)) 
    → ((Phi x -[ x ]> Psi x) ∨ (∃ x, Phi x ∧ Chi x)).
Proof.
  assert (S1 : ((Phi x -[ x ]> (Psi x ∨ Chi x)) 
      /\ (~ exists x, Phi x /\ Chi x))
    -> ((Phi x -[x]> (Psi x \/ Chi x))
      /\
      (Phi x -[x]> (¬ Chi x)))
    ).
  {
    pose proof (n10_51 Phi Chi) as n10_51.
    destruct n10_51 as [n10_51l n10_51r].
    clear n10_51r.
    pose proof Fact3_45 as Fact3_45.
    pose proof (Fact3_45 
      (¬ (∃ x : Prop, Phi x ∧ Chi x))
      (Phi x-[x]>¬ Chi x)
      (Phi x-[x]>(Psi x ∨ Chi x))
    ) as Fact3_45.
    MP n10_51r Fact3_45.
    rewrite -> n4_3 in Fact3_45.
    replace (( Phi x-[x]>¬ Chi x ) ∧  Phi x-[x]>(Psi x ∨ Chi x))
      with ((Phi x-[x]>(Psi x ∨ Chi x)) ∧ ( Phi x-[x]>¬ Chi x ))
      in Fact3_45.
    2: { apply propositional_extensionality. now rewrite -> n4_3. }
    exact Fact3_45.
  }
  assert (S2 : ((Phi x -[ x ]> (Psi x ∨ Chi x)) 
      /\ (~ exists x, Phi x /\ Chi x))
    -> ((Phi x -[x]> ((Psi x \/ Chi x) /\ ~ Chi x)))).
  {
    pose proof n10_29 as n10_29a.
    pose proof (n10_29 Phi (fun x => (Psi x ∨ Chi x)) 
      (fun x => ¬ Chi x)) as n10_29.
    destruct n10_29 as [n10_29l n10_29r].
    clear n10_29r.
    now Syll S1 n10_29l S2.
  }
  assert (S3 : ((Phi x -[ x ]> (Psi x ∨ Chi x)) 
      /\ (~ exists x, Phi x /\ Chi x))
    -> (Phi x -[ x ]> Psi x)).
  {
    setoid_rewrite -> n5_61 in S2.
    (* Here I think this is unprovable... *)
    admit.
  }
  assert (S4 : (Phi x -[ x ]> (Psi x ∨ Chi x)) 
    → ((Phi x -[ x ]> Psi x) ∨ (∃ x, Phi x ∧ Chi x))).
  {
    pose proof (n5_6
      (Phi x-[x]>(Psi x ∨ Chi x))
      (∃ x : Prop, Phi x ∧ Chi x)
      (Phi x-[x]>Psi x)
    ) as n5_6.
    destruct n5_6 as [n5_6l n5_6r].
    clear n5_6r.
    MP S3 n5_6.
    now rewrite -> n4_31 in n5_6l.
  }
  exact S4.
Admitted.
