Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.

Theorem n5_1 : ∀ P Q : Prop,
  (P ∧ Q) → (P ↔ Q).
  Proof. intros P Q.
  specialize n3_4 with P Q.
  intros n3_4a.
  specialize n3_4 with Q P.
  intros n3_4b.
  specialize n3_22 with P Q.
  intros n3_22a.
  Syll n3_22a n3_4b Sa.
  clear n3_22a. clear n3_4b.
  Conj n3_4a Sa C.
  specialize n4_76 with (P∧Q) (P→Q) (Q→P).
  intros n4_76a. (*Not cited*)
  apply propositional_extensionality in n4_76a.
  replace ((P∧Q→P→Q)∧(P∧Q→Q→P)) with 
      (P ∧ Q → (P → Q) ∧ (Q → P)) in C 
      by now apply n4_76a.
  replace ((P→Q)∧(Q→P)) with (P↔Q) in C
    by now rewrite Equiv4_01.
  exact C.
Qed. 

Theorem n5_11 : ∀ P Q : Prop,
  (P → Q) ∨ (¬P → Q).
  Proof. intros P Q.
  specialize n2_5 with P Q.
  intros n2_5a.
  specialize n2_54 with (P → Q) (¬P → Q).
  intros n2_54a.
  MP n2_54a n2_5a.
  exact n2_54a.
Qed.
  (*The proof sketch cites n2_51, 
      but this may be a misprint.*)

Theorem n5_12 : ∀ P Q : Prop,
  (P → Q) ∨ (P → ¬Q).
  Proof. intros P Q.
  specialize n2_51 with P Q.
  intros n2_51a.
  specialize n2_54 with ((P → Q)) (P → ¬Q).
  intros n2_54a.
  MP n2_54a n2_5a.
  exact n2_54a.
Qed.
  (*The proof sketch cites n2_52, 
      but this may be a misprint.*)

Theorem n5_13 : ∀ P Q : Prop,
  (P → Q) ∨ (Q → P).
  Proof. intros P Q.
  specialize n2_521 with P Q.
  intros n2_521a.
  replace (¬(P → Q) → Q → P) with 
      (¬¬(P → Q) ∨ (Q → P)) in n2_521a
      by now rewrite <- Impl1_01.
  specialize n4_13 with (P→Q).
  intros n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬(P→Q)) with (P→Q)
    in n2_521a by now apply n4_13a.
  exact n2_521a.
Qed. 

Theorem n5_14 : ∀ P Q R : Prop,
  (P → Q) ∨ (Q → R).
  Proof. intros P Q R.
  specialize Simp2_02 with P Q.
  intros Simp2_02a.
  specialize Transp2_16 with Q (P→Q).
  intros Transp2_16a.
  MP Transp2_16a Simp2_02a.
  specialize n2_21 with Q R.
  intros n2_21a.
  Syll Transp2_16a n2_21a Sa.
  replace (¬(P→Q)→(Q→R)) with 
      (¬¬(P→Q)∨(Q→R)) in Sa
      by now rewrite <- Impl1_01.
  specialize n4_13 with (P→Q).
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬(P→Q)) with (P→Q) in Sa
    by now apply n4_13a.
  exact Sa.
Qed.

Theorem n5_15 : ∀ P Q : Prop,
  (P ↔ Q) ∨ (P ↔ ¬Q).
  Proof. intros P Q.
  specialize n4_61 with P Q.
  intros n4_61a.
  replace (¬(P → Q) ↔ P ∧ ¬Q) with 
      ((¬(P→Q)→P∧¬Q)∧((P∧¬Q)→¬(P→Q))) in n4_61a
      by now rewrite Equiv4_01.
  specialize Simp3_26 with 
      (¬(P → Q) → P ∧ ¬Q) ((P ∧ ¬Q) → ¬(P → Q)).
  intros Simp3_26a.
  MP Simp3_26a n4_61a.
  specialize n5_1 with P (¬Q).
  intros n5_1a.
  Syll Simp3_26a n5_1a Sa.
  specialize n2_54 with (P→Q) (P ↔ ¬Q).
  intros n2_54a.
  MP n2_54a Sa.
  specialize n4_61 with Q P.
  intros n4_61b.
  replace ((¬(Q → P)) ↔ (Q ∧ ¬P)) with 
      (((¬(Q→P))→(Q∧¬P))∧((Q∧¬P)→(¬(Q→P)))) 
      in n4_61b by now rewrite Equiv4_01.
  specialize Simp3_26 with 
      (¬(Q→P)→(Q∧¬P)) ((Q∧¬P)→(¬(Q→P))).
  intros Simp3_26b.
  MP Simp3_26b n4_61b.
  specialize n5_1 with Q (¬P).
  intros n5_1b.
  Syll Simp3_26b n5_1b Sb.
  specialize n4_12 with P Q.
  intros n4_12a.
  apply propositional_extensionality in n4_12a.
  replace (Q↔¬P) with (P↔¬Q) in Sb 
    by now apply n4_12a.
  specialize n2_54 with (Q→P) (P↔¬Q).
  intros n2_54b.
  MP n2_54b Sb.
  replace (¬(P → Q) → P ↔ ¬Q) with 
      (¬¬(P → Q) ∨ (P ↔ ¬Q)) in Sa
      by now rewrite <- Impl1_01.
  specialize n4_13 with (P→Q).
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬(P→Q)) with (P→Q) in Sa
    by now apply n4_13a.
  replace (¬(Q → P) → (P ↔ ¬Q)) with 
      (¬¬(Q → P) ∨ (P ↔ ¬Q)) in Sb
      by now rewrite <- Impl1_01.
  specialize n4_13 with (Q→P).
  intros n4_13b.
  apply propositional_extensionality in n4_13b.
  replace (¬¬(Q→P)) with (Q→P) in Sb
    by now apply n4_13b.
  clear n4_61a. clear Simp3_26a. clear n5_1a. 
      clear n2_54a. clear n4_61b. clear Simp3_26b. 
      clear n5_1b. clear n4_12a. clear n2_54b.
      clear n4_13a. clear n4_13b.
  Conj Sa Sb C.
  specialize n4_31 with (P → Q) (P ↔ ¬Q).
  intros n4_31a.
  apply propositional_extensionality in n4_31a.
  replace ((P → Q) ∨ (P ↔ ¬Q)) with 
      ((P ↔ ¬Q) ∨ (P → Q)) in C
      by now apply n4_31a.
  specialize n4_31 with (Q → P) (P ↔ ¬Q).
  intros n4_31b.
  apply propositional_extensionality in n4_31b.
  replace ((Q → P) ∨ (P ↔ ¬Q)) with 
      ((P ↔ ¬Q) ∨ (Q → P)) in C
      by now apply n4_31b.
  specialize n4_41 with (P↔¬Q) (P→Q) (Q→P).
  intros n4_41a.
  apply propositional_extensionality in n4_41a.
  replace (((P↔¬Q)∨(P→Q))∧((P↔¬Q)∨(Q→P))) 
      with ((P ↔ ¬Q) ∨ (P → Q) ∧ (Q → P)) in C
      by now apply n4_41a.
  replace ((P→Q) ∧ (Q → P)) with (P↔Q) in C
    by now rewrite Equiv4_01.
    specialize n4_31 with (P ↔ ¬Q) (P ↔ Q).
    intros n4_31c.
    apply propositional_extensionality in n4_31c.
  replace ((P ↔ ¬Q) ∨ (P ↔ Q)) with 
      ((P ↔ Q) ∨ (P ↔ ¬Q)) in C
      by now apply n4_31c.
  exact C.
Qed.

Theorem n5_16 : ∀ P Q : Prop,
  ¬((P ↔ Q) ∧ (P ↔ ¬Q)).
  Proof. intros P Q.
  specialize Simp3_26 with ((P→Q)∧ (P → ¬Q)) (Q→P).
  intros Simp3_26a.
  specialize Id2_08 with ((P ↔ Q) ∧ (P → ¬Q)).
  intros Id2_08a.
  specialize n4_32 with (P→Q) (P→¬Q) (Q→P).
  intros n4_32a.
  apply propositional_extensionality in n4_32a.
  replace (((P → Q) ∧ (P → ¬Q)) ∧ (Q → P)) with 
      ((P→Q)∧((P→¬Q)∧(Q→P))) in Simp3_26a
      by now apply n4_32a.
  specialize n4_3 with (Q→P) (P→¬Q).
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((P → ¬Q) ∧ (Q → P)) with 
      ((Q → P) ∧ (P → ¬Q)) in Simp3_26a
      by now apply n4_3a.
  specialize n4_32 with (P→Q) (Q→P) (P→¬Q).
  intros n4_32b.
  apply propositional_extensionality in n4_32b.
  replace ((P→Q) ∧ (Q → P)∧ (P → ¬Q)) with 
      (((P→Q) ∧ (Q → P)) ∧ (P → ¬Q)) in Simp3_26a
      by now apply n4_32b.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q)
       in Simp3_26a by now rewrite Equiv4_01.
  Syll Id2_08a Simp3_26a Sa.
  specialize n4_82 with P Q.
  intros n4_82a.
  apply propositional_extensionality in n4_82a.
  replace ((P → Q) ∧ (P → ¬Q)) with (¬P) in Sa
    by now apply n4_82a.
  specialize Simp3_27 with 
      (P→Q) ((Q→P)∧ (P → ¬Q)).
  intros Simp3_27a.
  replace ((P→Q) ∧ (Q → P) ∧ (P → ¬Q)) with 
      (((P→Q) ∧ (Q → P)) ∧ (P → ¬Q)) in Simp3_27a
      by now apply n4_32b.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q) 
      in Simp3_27a by now rewrite Equiv4_01.
  specialize Syll3_33 with Q P (¬Q).
  intros Syll3_33a.
  Syll Simp3_27a Syll2_06a Sb.
  specialize Abs2_01 with Q.
  intros Abs2_01a.
  Syll Sb Abs2_01a Sc.
  clear Sb. clear Simp3_26a. clear Id2_08a. 
      clear n4_82a. clear Simp3_27a. clear Syll3_33a. 
      clear Abs2_01a. clear n4_32a. clear n4_32b. clear n4_3a.
  Conj Sa Sc C.
  specialize Comp3_43 with 
      ((P ↔ Q) ∧ (P → ¬Q)) (¬P) (¬Q).
  intros Comp3_43a.
  MP Comp3_43a C.
  specialize n4_65 with Q P.
  intros n4_65a.
  specialize n4_3 with (¬P) (¬Q).
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace (¬Q ∧ ¬P) with (¬P ∧ ¬Q) in n4_65a
    by now apply n4_3a.
  apply propositional_extensionality in n4_65a.
  replace (¬P∧¬Q) with (¬(¬Q→P)) in Comp3_43a
    by now apply n4_65a.
  specialize Exp3_3 with 
      (P↔Q) (P→¬Q) (¬(¬Q→P)).
  intros Exp3_3a.
  MP Exp3_3a Comp3_43a.
  replace ((P→¬Q)→¬(¬Q→P)) with 
      (¬(P→¬Q)∨¬(¬Q→P)) in Exp3_3a
      by now rewrite <- Impl1_01.
  specialize n4_51 with (P→¬Q) (¬Q→P).
  intros n4_51a.
  apply propositional_extensionality in n4_51a.
  replace (¬(P → ¬Q) ∨ ¬(¬Q → P)) with 
      (¬((P → ¬Q) ∧ (¬Q → P))) in Exp3_3a
      by now apply n4_51a.
  replace ((P→¬Q)∧(¬Q→P)) with (P↔¬Q) 
    in Exp3_3a by now rewrite Equiv4_01.
  replace ((P↔Q)→¬(P↔¬Q)) with 
      (¬(P↔Q)∨¬(P↔¬Q)) in Exp3_3a
      by now rewrite Impl1_01.
  specialize n4_51 with (P↔Q) (P↔¬Q).
  intros n4_51b.
  apply propositional_extensionality in n4_51b.
  replace (¬(P ↔ Q) ∨ ¬(P ↔ ¬Q)) with 
      (¬((P ↔ Q) ∧ (P ↔ ¬Q))) in Exp3_3a
      by now apply n4_51b.
  exact Exp3_3a.
Qed.

Theorem n5_17 : ∀ P Q : Prop,
  ((P ∨ Q) ∧ ¬(P ∧ Q)) ↔ (P ↔ ¬Q).
  Proof. intros P Q.
  specialize n4_64 with Q P.
  intros n4_64a.
  specialize n4_21 with (Q∨P) (¬Q→P).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((¬Q→P)↔(Q∨P)) with 
      ((Q∨P)↔(¬Q→P)) in n4_64a
      by now apply n4_21a.
  specialize n4_31 with P Q.
  intros n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (Q∨P) with (P∨Q) in n4_64a
    by now apply n4_31a.
  specialize n4_63 with P Q.
  intros n4_63a.
  specialize n4_21 with (P ∧ Q) (¬(P→¬Q)).
  intros n4_21b.
  apply propositional_extensionality in n4_21b.
  replace (¬(P → ¬Q) ↔ P ∧ Q) with 
      (P ∧ Q ↔ ¬(P → ¬Q)) in n4_63a
      by now apply n4_21b.
  specialize Transp4_11 with (P∧Q) (¬(P→¬Q)).
  intros Transp4_11a.
  specialize n4_13 with (P→¬Q).
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬(P→¬Q)) with (P→¬Q) 
    in Transp4_11a by now apply n4_13a.
  apply propositional_extensionality in Transp4_11a.
  replace (P ∧ Q ↔ ¬(P → ¬Q)) with 
      (¬(P ∧ Q) ↔ (P → ¬Q)) in n4_63a
      by now apply Transp4_11a.
  clear Transp4_11a. clear n4_21a.
  clear n4_31a. clear n4_21b. clear n4_13a.
  Conj n4_64a n4_63a C.
  specialize n4_38 with 
      (P ∨ Q) (¬(P ∧ Q)) (¬Q → P) (P → ¬Q).
  intros n4_38a.
  MP n4_38a C.
  replace ((¬Q→P) ∧ (P → ¬Q)) with (¬Q↔P)
       in n4_38a by now rewrite Equiv4_01.
  specialize n4_21 with P (¬Q).
  intros n4_21c.
  apply propositional_extensionality in n4_21c.
  replace (¬Q↔P) with (P↔¬Q) in n4_38a
    by now apply n4_21c.
  exact n4_38a.
Qed.

Theorem n5_18 : ∀ P Q : Prop,
  (P ↔ Q) ↔ ¬(P ↔ ¬Q).
  Proof. intros P Q.
  specialize n5_15 with P Q.
  intros n5_15a.
  specialize n5_16 with P Q.
  intros n5_16a.
  Conj n5_15a n5_16a C.
  specialize n5_17 with (P↔Q) (P↔¬Q).
  intros n5_17a.
  rewrite Equiv4_01 in n5_17a.
  specialize Simp3_26 with 
    ((((P↔Q)∨(P↔¬Q))∧¬((P↔Q)∧(P↔¬Q)))
    →((P↔Q)↔¬(P↔¬Q))) (((P↔Q)↔¬(P↔¬Q))→
    (((P↔Q)∨(P↔¬Q))∧¬((P↔Q)∧(P↔¬Q)))).
  intros Simp3_26a. (*not cited*)
  MP Simp3_26a n5_17a.
  MP Simp3_26a C.
  exact Simp3_26a.
Qed.

Theorem n5_19 : ∀ P : Prop,
  ¬(P ↔ ¬P).
  Proof. intros P.
  specialize n5_18 with P P.
  intros n5_18a.
  specialize n4_2 with P.
  intros n4_2a.
  rewrite Equiv4_01 in n5_18a.
  specialize Simp3_26 with (P↔P→¬(P↔¬P))
    (¬(P↔¬P)→P↔P).
  intros Simp3_26a. (*not cited*)
  MP Simp3_26a n5_18a.
  MP Simp3_26a n4_2a.
  exact Simp3_26a.
Qed.

Theorem n5_21 : ∀ P Q : Prop,
  (¬P ∧ ¬Q) → (P ↔ Q).
  Proof. intros P Q.
  specialize n5_1 with (¬P) (¬Q).
  intros n5_1a.
  specialize Transp4_11 with P Q.
  intros Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  replace (¬P↔¬Q) with (P↔Q) in n5_1a
    by now apply Transp4_11a.
  exact n5_1a.
Qed.

Theorem n5_22 : ∀ P Q : Prop,
  ¬(P ↔ Q) ↔ ((P ∧ ¬Q) ∨ (Q ∧ ¬P)).
  Proof. intros P Q.
  specialize n4_61 with P Q.
  intros n4_61a.
  specialize n4_61 with Q P.
  intros n4_61b.
  Conj n4_61a n4_61b C.
  specialize n4_39 with 
      (¬(P → Q)) (¬(Q → P)) (P ∧ ¬Q) (Q ∧ ¬P).
  intros n4_39a.
  MP n4_39a C.
  specialize n4_51 with (P→Q) (Q→P).
  intros n4_51a.
  apply propositional_extensionality in n4_51a.
  replace (¬(P → Q) ∨ ¬(Q → P)) with 
      (¬((P → Q) ∧ (Q → P))) in n4_39a
      by now apply n4_51a.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q) 
      in n4_39a by now rewrite Equiv4_01.
  exact n4_39a.
Qed.

Theorem n5_23 : ∀ P Q : Prop,
  (P ↔ Q) ↔ ((P ∧ Q) ∨ (¬P ∧ ¬Q)).
  Proof. intros P Q.
  specialize n5_18 with P Q.
  intros n5_18a.
  specialize n5_22 with P (¬Q).
  intros n5_22a.
  Conj n5_18a n5_22a C.
  specialize n4_22 with (P↔Q) (¬(P↔¬Q)) 
    (P ∧ ¬¬Q ∨ ¬Q ∧ ¬P).
  intros n4_22a.
  MP n4_22a C.
  specialize n4_13 with Q.
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬Q) with Q in n4_22a by now apply n4_13a.
  specialize n4_3 with (¬P) (¬Q).
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace (¬Q ∧ ¬P) with (¬P ∧ ¬Q) in n4_22a
    by now apply n4_3a.
  exact n4_22a.
Qed. 
  (*The proof sketch in Principia offers n4_36. 
    This seems to be a misprint. We used n4_3.*)

Theorem n5_24 : ∀ P Q : Prop,
  ¬((P ∧ Q) ∨ (¬P ∧ ¬Q)) ↔ ((P ∧ ¬Q) ∨ (Q ∧ ¬P)).
  Proof. intros P Q.
  specialize n5_23 with P Q.
  intros n5_23a.
  specialize Transp4_11 with 
    (P↔Q) (P ∧ Q ∨ ¬P ∧ ¬Q).
  intros Transp4_11a. (*Not cited*)
  rewrite Equiv4_01 in Transp4_11a.
  specialize Simp3_26 with (((P↔Q)↔P∧Q∨¬P∧¬Q)
    →(¬(P↔Q)↔¬(P∧Q∨¬P∧¬Q))) 
    ((¬(P↔Q)↔¬(P∧Q∨¬P∧¬Q))
    →((P↔Q)↔P∧Q∨¬P∧¬Q)).
  intros Simp3_26a.
  MP Simp3_26a Transp4_11a.
  MP Simp3_26a n5_23a.
  specialize n5_22 with P Q.
  intros n5_22a.
    clear n5_23a. clear Transp4_11a.
  Conj Simp3_26a n5_22a C.
  specialize n4_22 with (¬(P∧Q∨¬P∧¬Q))
    (¬(P↔Q)) (P∧¬Q∨Q∧¬P).
  intros n4_22a.
  specialize n4_21 with (¬(P∧Q∨¬P∧¬Q)) (¬(P↔Q)).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((¬(P↔Q))↔(¬((P ∧ Q)∨(¬P ∧ ¬Q))))
    with ((¬((P ∧ Q)∨(¬P ∧ ¬Q)))↔(¬(P↔Q))) in C
    by now apply n4_21a.
  MP n4_22a C.
  exact n4_22a.
Qed. 

Theorem n5_25 : ∀ P Q : Prop,
  (P ∨ Q) ↔ ((P → Q) → Q).
  Proof. intros P Q.
  specialize n2_62 with P Q.
  intros n2_62a.
  specialize n2_68 with P Q.
  intros n2_68a.
  Conj n2_62a n2_68a C.
  Equiv C.
  exact C.
Qed.

Theorem n5_3 : ∀ P Q R : Prop,
  ((P ∧ Q) → R) ↔ ((P ∧ Q) → (P ∧ R)).
  Proof. intros P Q R.
  specialize Comp3_43 with (P ∧ Q) P R.
  intros Comp3_43a.
  specialize Exp3_3 with 
      (P ∧ Q → P) (P ∧ Q →R) (P ∧ Q → P ∧ R).
  intros Exp3_3a. (*Not cited*)
  MP Exp3_3a Comp3_43a.
  specialize Simp3_26 with P Q.
  intros Simp3_26a.
  MP Exp3_3a Simp3_26a.
  specialize Syll2_05 with (P ∧ Q) (P ∧ R) R.
  intros Syll2_05a.
  specialize Simp3_27 with P R.
  intros Simp3_27a.
  MP Syll2_05a Simp3_27a.
  clear Comp3_43a. clear Simp3_27a. 
      clear Simp3_26a.
  Conj Exp3_3a Syll2_05a C.
  Equiv C.
  exact C.
Qed. 

Theorem n5_31 : ∀ P Q R : Prop,
  (R ∧ (P → Q)) → (P → (Q ∧ R)).
  Proof. intros P Q R.
  specialize Comp3_43 with P Q R.
  intros Comp3_43a.
  specialize Simp2_02 with P R.
  intros Simp2_02a.
  specialize Exp3_3 with 
      (P→R) (P→Q) (P→(Q ∧ R)).
  intros Exp3_3a. (*Not cited*)
  specialize n3_22 with (P → R) (P → Q). (*Not cited*)
  intros n3_22a.
  Syll n3_22a Comp3_43a Sa.
  MP Exp3_3a Sa.
  Syll Simp2_02a Exp3_3a Sb.
  specialize Imp3_31 with R (P→Q) (P→(Q ∧ R)).
  intros Imp3_31a. (*Not cited*)
  MP Imp3_31a Sb.
  exact Imp3_31a.
Qed. 

Theorem n5_32 : ∀ P Q R : Prop,
  (P → (Q ↔ R)) ↔ ((P ∧ Q) ↔ (P ∧ R)).
  Proof. intros P Q R.
  specialize n4_76 with P (Q→R) (R→Q).
  intros n4_76a.
  specialize Exp3_3 with P Q R.
  intros Exp3_3a.
  specialize Imp3_31 with P Q R.
  intros Imp3_31a.
  Conj Exp3_3a Imp3_31a Ca.
  Equiv Ca.
  specialize Exp3_3 with P R Q.
  intros Exp3_3b.
  specialize Imp3_31 with P R Q.
  intros Imp3_31b.
  Conj Exp3_3b Imp3_31b Cb.
  Equiv Cb.
  specialize n5_3 with P Q R.
  intros n5_3a.
  specialize n5_3 with P R Q.
  intros n5_3b.
  apply propositional_extensionality in Ca.
  replace (P→Q→R) with (P∧Q→R) in n4_76a
    by now apply Ca.
  apply propositional_extensionality in Cb.
  replace (P→R→Q) with (P∧R→Q) in n4_76a
    by now apply Cb.
  apply propositional_extensionality in n5_3a.
  replace (P∧Q→R) with (P∧Q→P∧R) in n4_76a
    by now apply n5_3a.
  apply propositional_extensionality in n5_3b.
  replace (P∧R→Q) with (P∧R→P∧Q) in n4_76a
    by now apply n5_3b.
  replace ((P∧Q→P∧R)∧(P∧R→P∧Q)) with 
      ((P∧Q)↔(P∧R)) in n4_76a 
      by now rewrite Equiv4_01.
  specialize n4_21 with 
      (P→((Q→R)∧(R→Q))) ((P∧Q)↔(P∧R)).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((P∧Q↔P∧R)↔(P→(Q→R)∧(R→Q))) with 
      ((P→(Q→R)∧(R→Q))↔(P∧Q ↔ P∧R)) in n4_76a
      by now apply n4_21a.
  replace ((Q→R)∧(R→Q)) with (Q↔R) in n4_76a
    by now rewrite Equiv4_01.
  exact n4_76a.
Qed.

Theorem n5_33 : ∀ P Q R : Prop,
  (P ∧ (Q → R)) ↔ (P ∧ ((P ∧ Q) → R)).
  Proof. intros P Q R.
    specialize n5_32 with P (Q→R) ((P∧Q)→R).
    intros n5_32a.
    replace 
        ((P→(Q→R)↔(P∧Q→R))↔(P∧(Q→R)↔P∧(P∧Q→R))) 
        with 
        (((P→(Q→R)↔(P∧Q→R))→(P∧(Q→R)↔P∧(P∧Q→R)))
        ∧
        ((P∧(Q→R)↔P∧(P∧Q→R)→(P→(Q→R)↔(P∧Q→R))))) 
        in n5_32a by now rewrite Equiv4_01.
    specialize Simp3_26 with 
        ((P→(Q→R)↔(P∧Q→R))→(P∧(Q→R)↔P∧(P∧Q→R))) 
        ((P∧(Q→R)↔P∧(P∧Q→R)→(P→(Q→R)↔(P∧Q→R)))). 
    intros Simp3_26a. (*Not cited*)
    MP Simp3_26a n5_32a.
    specialize n4_73 with Q P.
    intros n4_73a.
    specialize n4_84 with Q (Q∧P) R.
    intros n4_84a.
    Syll n4_73a n4_84a Sa.
    specialize n4_3 with P Q.
    intros n4_3a.
    apply propositional_extensionality in n4_3a.
    replace (Q∧P) with (P∧Q) in Sa 
      by now apply n4_3a. (*Not cited*)
    MP Simp3_26a Sa.
    exact Simp3_26a.
Qed.

Theorem n5_35 : ∀ P Q R : Prop,
  ((P → Q) ∧ (P → R)) → (P → (Q ↔ R)).
  Proof. intros P Q R.
  specialize Comp3_43 with P Q R.
  intros Comp3_43a.
  specialize n5_1 with Q R.
  intros n5_1a.
  specialize Syll2_05 with P (Q∧R) (Q↔R).
  intros Syll2_05a.
  MP Syll2_05a n5_1a.
  Syll Comp3_43a Syll2_05a Sa.
  exact Sa.
Qed.

Theorem n5_36 : ∀ P Q : Prop,
  (P ∧ (P ↔ Q)) ↔ (Q ∧ (P ↔ Q)).
  Proof. intros P Q.
  specialize Id2_08 with (P↔Q).
  intros Id2_08a.
  specialize n5_32 with (P↔Q) P Q.
  intros n5_32a.
  apply propositional_extensionality in n5_32a.
  replace (P↔Q→P↔Q) with 
      ((P↔Q)∧P↔(P↔Q)∧Q) in Id2_08a
      by now apply n5_32a.
  specialize n4_3 with P (P↔Q).
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((P↔Q)∧P) with (P∧(P↔Q)) in Id2_08a
    by now apply n4_3a.
  specialize n4_3 with Q (P↔Q).
  intros n4_3b.
  apply propositional_extensionality in n4_3b.
  replace ((P↔Q)∧Q) with (Q∧(P↔Q)) in Id2_08a
    by now apply n4_3b.
  exact Id2_08a.
Qed. 
  (*The proof sketch cites Ass3_35 and n4_38, 
    but the sketch was indecipherable.*)

Theorem n5_4 : ∀ P Q : Prop,
  (P → (P → Q)) ↔ (P → Q).
  Proof. intros P Q.
  specialize n2_43 with P Q.
  intros n2_43a.
  specialize Simp2_02 with (P) (P→Q).
  intros Simp2_02a.
  Conj n2_43a Simp2_02a C.
  Equiv C.
  exact C.
Qed.

Theorem n5_41 : ∀ P Q R : Prop,
  ((P → Q) → (P → R)) ↔ (P → Q → R).
  Proof. intros P Q R.
  specialize n2_86 with P Q R.
  intros n2_86a.
  specialize n2_77 with P Q R.
  intros n2_77a.
  Conj n2_86a n2_77a C.
  Equiv C.
  exact C.
Qed.

Theorem n5_42 : ∀ P Q R : Prop,
  (P → Q → R) ↔ (P → Q → P ∧ R).
  Proof. intros P Q R.
  specialize n5_3 with P Q R.
  intros n5_3a.
  specialize n4_87 with P Q R.
  intros n4_87a.
  specialize Imp3_31 with P Q R.
  intros Imp3_31a.
  specialize Exp3_3 with P Q R.
  intros Exp3_3a.
  Conj Imp3_31a Exp3_3 Ca.
  Equiv Ca.
  apply propositional_extensionality in Ca.
  replace ((P∧Q)→R) with (P→Q→R) in n5_3a
    by now apply Ca.
  specialize n4_87 with P Q (P∧R).
  intros n4_87b.
  specialize Imp3_31 with P Q (P∧R).
  intros Imp3_31b.
  specialize Exp3_3 with P Q (P∧R).
  intros Exp3_3b.
  Conj Imp3_31b Exp3_3b Cb.
  Equiv Cb.
  apply propositional_extensionality in Cb.
  replace ((P∧Q)→(P∧R)) with 
      (P→Q→(P∧R)) in n5_3a by now apply Cb.
  exact n5_3a.
Qed. 

Theorem n5_44 : ∀ P Q R : Prop,
  (P→Q) → ((P → R) ↔ (P → (Q ∧ R))).
  Proof. intros P Q R.
  specialize n4_76 with P Q R.
  intros n4_76a.
  rewrite Equiv4_01 in n4_76a.
  specialize Simp3_26 with 
    (((P→Q)∧(P→R))→(P→(Q∧R)))
    ((P→(Q∧R))→((P→Q)∧(P→R))).
  intros Simp3_26a.
  MP Simp3_26a n4_76a.
  specialize Simp3_27 with 
    (((P→Q)∧(P→R))→(P→(Q∧R)))
    ((P→(Q∧R))→((P→Q)∧(P→R))).
  intros Simp3_27a.
  MP Simp3_27a n4_76a.
  specialize Simp3_27 with (P→Q) (P→Q∧R).
  intros Simp3_27d.
  Syll Simp3_27d Simp3_27a Sa.
  specialize n5_3 with (P→Q) (P→R) (P→(Q∧R)).
  intros n5_3a.
  rewrite Equiv4_01 in n5_3a.
  specialize Simp3_26 with 
    ((((P→Q)∧(P→R))→(P→(Q∧R)))→
    (((P→Q)∧(P→R))→((P→Q)∧(P→(Q∧R)))))
    ((((P→Q)∧(P→R))→((P→Q)∧(P→(Q∧R))))
    →(((P→Q)∧(P→R))→(P→(Q∧R)))).
  intros Simp3_26b.
  MP Simp3_26b n5_3a.
  specialize Simp3_27 with 
  ((((P→Q)∧(P→R))→(P→(Q∧R)))→
  (((P→Q)∧(P→R))→((P→Q)∧(P→(Q∧R)))))
  ((((P→Q)∧(P→R))→((P→Q)∧(P→(Q∧R))))
  →(((P→Q)∧(P→R))→(P→(Q∧R)))).
  intros Simp3_27b.
  MP Simp3_27b n5_3a.
  MP Simp3_26a Simp3_26b.
  MP Simp3_27a Simp3_27b.
  clear n4_76a. clear Simp3_26a. clear Simp3_27a. 
    clear Simp3_27b. clear Simp3_27d. clear n5_3a.
  Conj Simp3_26b Sa C.
  Equiv C.
  specialize n5_32 with (P→Q) (P→R) (P→(Q∧R)).
  intros n5_32a.
  rewrite Equiv4_01 in n5_32a.
  specialize Simp3_27 with 
    (((P → Q) → (P → R) ↔ (P → Q ∧ R))
      → (P → Q) ∧ (P → R) ↔ (P → Q) ∧ (P → Q ∧ R))
    ((P → Q) ∧ (P → R) ↔ (P → Q) ∧ (P → Q ∧ R)
      → (P → Q) → (P → R) ↔ (P → Q ∧ R)).
  intros Simp3_27c.
  MP Simp3_27c n5_32a.
  specialize n4_21 with 
    ((P→Q)∧(P→R)) ((P→Q)∧(P→(Q∧R))).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (((P→Q)∧(P→(Q∧R)))↔((P→Q)∧(P→R)))
    with (((P→Q)∧(P→R))↔((P→Q)∧(P→(Q∧R))))
    in C by now apply n4_21a.
  MP Simp3_27c C.
  exact Simp3_27c.
Qed. 

Theorem n5_5 : ∀ P Q : Prop,
  P → ((P → Q) ↔ Q).
  Proof. intros P Q.
  specialize Ass3_35 with P Q.
  intros Ass3_35a.
  specialize Exp3_3 with P (P→Q) Q.
  intros Exp3_3a.
  MP Exp3_3a Ass3_35a.
  specialize Simp2_02 with P Q.
  intros Simp2_02a.
  specialize Exp3_3 with P Q (P→Q).
  intros Exp3_3b.
  specialize n3_42 with P Q (P→Q). (*Not cited*)
  intros n3_42a.
  MP n3_42a Simp2_02a.
  MP Exp3_3b n3_42a.
  clear n3_42a. clear Simp2_02a. clear Ass3_35a.
  Conj Exp3_3a Exp3_3b C.
  specialize n3_47 with P P ((P→Q)→Q) (Q→(P→Q)).
  intros n3_47a.
  MP n3_47a C.
  specialize n4_24 with P.
  intros n4_24a. (*Not cited*)
  apply propositional_extensionality in n4_24a.
  replace (P∧P) with P in n3_47a by now apply n4_24a. 
  replace (((P→Q)→Q)∧(Q→(P→Q))) with ((P→Q)↔Q)
    in n3_47a by now rewrite Equiv4_01.
  exact n3_47a.
Qed.

Theorem n5_501 : ∀ P Q : Prop,
  P → (Q ↔ (P ↔ Q)).
  Proof. intros P Q.
  specialize n5_1 with P Q.
  intros n5_1a.
  specialize Exp3_3 with P Q (P↔Q).
  intros Exp3_3a.
  MP Exp3_3a n5_1a.
  specialize Ass3_35 with P Q.
  intros Ass3_35a.
  specialize Simp3_26 with (P∧(P→Q)) (Q→P).
  intros Simp3_26a. (*Not cited*)
  Syll Simp3_26a Ass3_35a Sa.
  specialize n4_32 with P (P→Q) (Q→P).
  intros n4_32a. (*Not cited*)
  apply propositional_extensionality in n4_32a.
  replace ((P∧(P→Q))∧(Q→P)) with 
      (P∧((P→Q)∧(Q→P))) in Sa by now apply n4_32a.
  replace ((P→Q)∧(Q→P)) with (P↔Q) in Sa
    by now rewrite Equiv4_01.
  specialize Exp3_3 with P (P↔Q) Q.
  intros Exp3_3b.
  MP Exp3_3b Sa.
  clear n5_1a. clear Ass3_35a. clear n4_32a.
      clear Simp3_26a. clear Sa. 
  Conj Exp3_3a Exp3_3b C.
  specialize n4_76 with P (Q→(P↔Q)) ((P↔Q)→Q).
  intros n4_76a. (*Not cited*)
  apply propositional_extensionality in n4_76a.
  replace ((P→Q→P↔Q)∧(P→P↔Q→Q)) with 
      ((P→(Q→P↔Q)∧(P↔Q→Q))) in C
      by now apply n4_76a.
  replace ((Q→(P↔Q))∧((P↔Q)→Q)) with 
      (Q↔(P↔Q)) in C by now rewrite Equiv4_01.
  exact C.
Qed.

Theorem n5_53 : ∀ P Q R S : Prop,
  (((P ∨ Q) ∨ R) → S) ↔ (((P → S) ∧ (Q → S)) ∧ (R → S)).
  Proof. intros P Q R S.
  specialize n4_77 with S (P∨Q) R.
  intros n4_77a.
  specialize n4_77 with S P Q.
  intros n4_77b.
  apply propositional_extensionality in n4_77b.
  replace (P ∨ Q → S) with 
      ((P→S)∧(Q→S)) in n4_77a
      by now apply n4_77b. (*Not cited*)
  specialize n4_21 with ((P ∨ Q) ∨ R → S) 
      (((P → S) ∧ (Q → S)) ∧ (R → S)).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace ((((P→S)∧(Q→S))∧(R→S))↔(((P∨Q)∨R)→S)) 
      with 
      ((((P∨Q)∨R)→S)↔(((P→S)∧(Q→S))∧(R→S))) 
      in n4_77a by now apply n4_21.
  exact n4_77a.
Qed.

Theorem n5_54 : ∀ P Q : Prop,
  ((P ∧ Q) ↔ P) ∨ ((P ∧ Q) ↔ Q).
  Proof. intros P Q.
  specialize n4_73 with P Q.
  intros n4_73a.
  specialize n4_44 with Q P.
  intros n4_44a.
  specialize Transp2_16 with Q (P↔(P∧Q)).
  intros Transp2_16a.
  MP n4_73a Transp2_16a.
  specialize n4_3 with P Q.
  intros n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (Q∧P) with (P∧Q) in n4_44a
    by now apply n4_3a.
  specialize Transp4_11 with Q (Q∨(P∧Q)).
  intros Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  replace (Q↔Q∨P∧Q) with 
      (¬Q↔¬(Q∨P∧Q)) in n4_44a by now apply Transp4_11a.
  apply propositional_extensionality in n4_44a.
  replace (¬Q) with (¬(Q∨P∧Q)) in Transp2_16a
    by now apply n4_44a.
  specialize n4_56 with Q (P∧Q).
  intros n4_56a. (*Not cited*)
  apply propositional_extensionality in n4_56a.
  replace (¬(Q∨P∧Q)) with 
      (¬Q∧¬(P∧Q)) in Transp2_16a
      by now apply n4_56a.
  specialize n5_1 with (¬Q) (¬(P∧Q)).
  intros n5_1a.
  Syll Transp2_16a n5_1a Sa.
  replace (¬(P↔P∧Q)→(¬Q↔¬(P∧Q))) with 
      (¬¬(P↔P∧Q)∨(¬Q↔¬(P∧Q))) in Sa
      by now rewrite Impl1_01. (*Not cited*)
  specialize n4_13 with (P ↔ (P∧Q)).
  intros n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬(P↔P∧Q)) with (P↔P∧Q) in Sa
    by now apply n4_13a.
  specialize Transp4_11 with Q (P∧Q).
  intros Transp4_11b.
  apply propositional_extensionality in Transp4_11b.
  replace (¬Q↔¬(P∧Q)) with (Q↔(P∧Q)) in Sa
    by now apply Transp4_11b.
  specialize n4_21 with (P∧Q) Q.
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (Q↔(P∧Q)) with ((P∧Q)↔Q) in Sa
    by now apply n4_21a.
  specialize n4_21 with (P∧Q) P.
  intros n4_21b. (*Not cited*)
  apply propositional_extensionality in n4_21b.
  replace (P↔(P∧Q)) with ((P∧Q)↔P) in Sa
    by now apply n4_21b.
  exact Sa.
Qed. 

Theorem n5_55 : ∀ P Q : Prop,
  ((P ∨ Q) ↔ P) ∨ ((P ∨ Q) ↔ Q).
  Proof. intros P Q.
  specialize Add1_3 with (P∧Q) (P).
  intros Add1_3a.
  specialize n4_3 with P Q.
  intros n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  specialize n4_41 with P Q P. 
  intros n4_41a. (*Not cited*)
  replace (Q ∧ P) with (P ∧ Q) in n4_41a 
    by now apply n4_3a.
  specialize n4_31 with (P ∧ Q) P.
  intros n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (P ∨ P ∧ Q) with (P ∧ Q ∨ P) in n4_41a
    by now apply n4_31a.
  apply propositional_extensionality in n4_41a.
  replace ((P∧Q)∨P) with ((P∨Q)∧(P∨P)) in Add1_3a
    by now apply n4_4a.
  specialize n4_25 with P.
  intros n4_25a. (*Not cited*)
  apply propositional_extensionality in n4_25a.
  replace (P∨P) with P in Add1_3a
    by now apply n4_25a.
  specialize n4_31 with P Q.
  intros n4_31b.
  apply propositional_extensionality in n4_31b.
  replace (Q∨P) with (P∨Q) in Add1_3a
    by now apply n4_31b. 
  specialize n5_1 with P (P∨Q).
  intros n5_1a.
  specialize n4_3 with (P ∨ Q) P.
  intros n4_3b.
  apply propositional_extensionality in n4_3b.
  replace ((P ∨ Q) ∧ P) with (P ∧ (P ∨ Q)) in Add1_3a
    by now apply n4_3b.
  Syll Add1_3a n5_1a Sa.
  specialize n4_74 with P Q.
  intros n4_74a.
  specialize Transp2_15 with P (Q↔P∨Q).
  intros Transp2_15a. (*Not cited*)
  MP Transp2_15a n4_74a.
  Syll Transp2_15a Sa Sb.
  replace (¬ (Q ↔ P ∨ Q) → P ↔ P ∨ Q) with
    (¬¬(Q ↔ P ∨ Q) ∨ (P ↔ P ∨ Q)) in Sb 
    by now rewrite Impl1_01.
  specialize n4_13 with (Q ↔ P ∨ Q).
  intros n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬(Q↔(P∨Q))) with (Q↔(P∨Q)) in Sb
    by now apply n4_13a.
  specialize n4_21 with (P ∨ Q) Q.
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (Q↔(P∨Q)) with ((P∨Q)↔Q) in Sb
    by now apply n4_21a.
  specialize n4_21 with (P ∨ Q) P.
  intros n4_21b. (*Not cited*)
  apply propositional_extensionality in n4_21b.
  replace (P↔(P∨Q)) with ((P∨Q)↔P) in Sb
    by now apply n4_21b.
  apply n4_31 in Sb.
  exact Sb. 
Qed.

Theorem n5_6 : ∀ P Q R : Prop,
  ((P ∧ ¬Q) → R) ↔ (P → (Q ∨ R)).
  Proof. intros P Q R.
  specialize n4_87 with P (¬Q) R.
  intros n4_87a.
  specialize n4_64 with Q R.
  intros n4_64a.
  specialize n4_85 with P Q R.
  intros n4_85a.
  replace (((P∧¬Q→R)↔(P→¬Q→R))↔((¬Q→P→R)↔(¬Q∧P→R)))
       with 
       ((((P∧¬Q→R)↔(P→¬Q→R))→((¬Q→P→R)↔(¬Q∧P→R)))
       ∧
       ((((¬Q→P→R)↔(¬Q∧P→R)))→(((P∧¬Q→R)↔(P→¬Q→R))))) 
       in n4_87a by now rewrite Equiv4_01.
  specialize Simp3_27 with 
      (((P∧¬Q→R)↔(P→¬Q→R)→(¬Q→P→R)↔(¬Q∧P→R))) 
      (((¬Q→P→R)↔(¬Q∧P→R)→(P∧¬Q→R)↔(P→¬Q→R))).
  intros Simp3_27a.
  MP Simp3_27a n4_87a.
  specialize Imp3_31 with (¬Q) P R.
  intros Imp3_31a.
  specialize Exp3_3 with (¬Q) P R.
  intros Exp3_3a.
  Conj Imp3_31a Exp3_3a C.
  Equiv C.
  MP Simp3_27a C.
  apply propositional_extensionality in n4_64a.
  replace (¬Q→R) with (Q∨R) in Simp3_27a
    by now apply n4_64a.
  exact Simp3_27a.  
Qed. 

Theorem n5_61 : ∀ P Q : Prop,
  ((P ∨ Q) ∧ ¬Q) ↔ (P ∧ ¬Q).
  Proof. intros P Q.
  specialize n4_74 with Q P.
  intros n4_74a.
  specialize n5_32 with (¬Q) P (Q∨P).
  intros n5_32a.
  apply propositional_extensionality in n5_32a.
  replace (¬Q → P ↔ Q ∨ P) with 
      (¬Q ∧ P ↔ ¬Q ∧ (Q ∨ P)) in n4_74a
      by now apply n5_32a.
  specialize n4_3 with P (¬Q).
  intros n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (¬Q ∧ P) with (P ∧ ¬Q) in n4_74a
    by now apply n4_3a.
  specialize n4_3 with (Q ∨ P) (¬Q).
  intros n4_3b. (*Not cited*)
  apply propositional_extensionality in n4_3b.
  replace (¬Q ∧ (Q ∨ P)) with ((Q ∨ P) ∧ ¬Q) in n4_74a
    by now apply n4_3b.
  specialize n4_31 with P Q.
  intros n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n4_74a
    by now apply n4_31a.
  specialize n4_21 with ((P ∨ Q) ∧ ¬Q) (P ∧ ¬Q).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∧ ¬Q ↔ (P ∨ Q) ∧ ¬Q) with 
      ((P ∨ Q) ∧ ¬Q ↔ P ∧ ¬Q) in n4_74a
      by now apply n4_21a.
  exact n4_74a.
Qed.

Theorem n5_62 : ∀ P Q : Prop,
  ((P ∧ Q) ∨ ¬Q) ↔ (P ∨ ¬Q).
  Proof. intros P Q.
  specialize n4_7 with Q P.
  intros n4_7a.
  replace (Q→P) with (¬Q∨P) in n4_7a
    by now rewrite Impl1_01.
  replace (Q→(Q∧P)) with (¬Q∨(Q∧P)) in n4_7a
    by now rewrite Impl1_01.
  specialize n4_31 with (Q ∧ P) (¬Q).
  intros n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace (¬Q∨(Q∧P)) with ((Q∧P)∨¬Q) in n4_7a
    by now apply n4_31a.
  specialize n4_31 with P (¬Q).
  intros n4_31b. (*Not cited*)
  apply propositional_extensionality in n4_31b.
  replace (¬Q∨P) with (P∨¬Q) in n4_7a
    by now apply n4_31b.
  specialize n4_3 with P Q.
  intros n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (Q∧P) with (P∧Q) in n4_7a
    by now apply n4_3a.
  specialize n4_21 with (P ∧ Q ∨ ¬Q) (P ∨ ¬Q).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∨ ¬Q ↔ P ∧ Q ∨ ¬Q) with 
      (P ∧ Q ∨ ¬Q ↔ P ∨ ¬Q) in n4_7a
      by now apply n4_21a.
  exact n4_7a.
Qed.

Theorem n5_63 : ∀ P Q : Prop,
  (P ∨ Q) ↔ (P ∨ (¬P ∧ Q)).
  Proof. intros P Q.
  specialize n5_62 with Q (¬P).
  intros n5_62a.
  specialize n4_13 with P.
  intros n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬P) with P in n5_62a
    by now apply n4_13a.
  specialize n4_31 with P Q.
  intros n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n5_62a
    by now apply n4_31a.
  specialize n4_31 with P (Q∧¬P).
  intros n4_31b. (*Not cited*)
  apply propositional_extensionality in n4_31b.
  replace ((Q∧¬P)∨P) with (P∨(Q∧¬P)) in n5_62a
    by now apply n4_31b.
  specialize n4_21 with (P∨Q) (P∨(Q∧¬P)).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∨ Q ∧ ¬P ↔ P ∨ Q) with 
      (P ∨ Q ↔ P ∨ Q ∧ ¬P) in n5_62a
      by now apply n4_21a.
  specialize n4_3 with (¬P) Q.
  intros n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (Q∧¬P) with (¬P∧Q) in n5_62a
    by now apply n4_3a.
  exact n5_62a.
Qed.

Theorem n5_7 : ∀ P Q R : Prop,
  ((P ∨ R) ↔ (Q ∨ R)) ↔ (R ∨ (P ↔ Q)).
  Proof. intros P Q R.
  specialize n4_74 with R P.
  intros n4_74a.
  specialize n4_74 with R Q.
  intros n4_74b. (*Greg's suggestion*)
  Conj n4_74a n4_74b Ca.
  specialize Comp3_43 with 
    (¬R) (P↔R∨P) (Q↔R∨Q).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  specialize n4_22 with P (R∨P) (R∨Q).
  intros n4_22a.
  specialize n4_22 with P (R∨Q) Q.
  intros n4_22b.
  specialize Exp3_3 with (P↔(R∨Q)) 
    ((R∨Q)↔Q) (P↔Q).
  intros Exp3_3a.
  MP Exp3_3a n4_22b.
  Syll n4_22a Exp3_3a Sa.
  specialize Imp3_31 with ((P↔(R∨P))∧
    ((R ∨ P) ↔ (R ∨ Q))) ((R∨Q)↔Q) (P↔Q).
  intros Imp3_31a.
  MP Imp3_31a Sa.
  specialize n4_32 with (P↔R∨P) (R∨P↔R∨Q) (R∨Q↔Q).
  intros n4_32a.
  apply propositional_extensionality in n4_32a.
  replace (((P↔(R∨P))∧((R ∨ P) ↔ 
      (R ∨ Q))) ∧ ((R∨Q)↔Q)) with 
    ((P↔(R∨P))∧(((R ∨ P) ↔ 
      (R ∨ Q)) ∧ ((R∨Q)↔Q))) in Imp3_31a 
    by now apply n4_32a.
  specialize n4_3 with (R ∨ Q ↔ Q) (R ∨ P ↔ R ∨ Q).
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((R ∨ P ↔ R ∨ Q) ∧ (R ∨ Q ↔ Q)) with 
    ((R ∨ Q ↔ Q) ∧ (R ∨ P ↔ R ∨ Q)) in Imp3_31a
    by now apply n4_3a.
  specialize n4_32 with (P ↔ R ∨ P) (R ∨ Q ↔ Q) (R ∨ P ↔ R ∨ Q).
  intros n4_32b.
  apply propositional_extensionality in n4_32b.
  replace ((P↔(R∨P)) ∧ 
      ((R ∨ Q ↔ Q) ∧ (R ∨ P ↔ R ∨ Q))) with 
    (((P↔(R∨P)) ∧ (R ∨ Q ↔ Q)) ∧ 
      (R ∨ P ↔ R ∨ Q)) in Imp3_31a
    by now apply n4_32b.
  specialize Exp3_3 with 
    ((P↔(R∨P))∧(R∨Q↔Q)) 
    (R ∨ P ↔ R ∨ Q) (P ↔ Q).
  intros Exp3_3b.
  MP Exp3_3b Imp3_31a.
  specialize n4_21 with Q (R∨Q).
  intros n4_21a.
  apply propositional_extensionality in n4_21a. 
  replace (Q↔R∨Q) with (R∨Q↔Q) in Comp3_43a
    by now apply n4_21a.
  Syll Comp3_43a Exp3_3b Sb.
  specialize n4_31 with P R.
  intros n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (R∨P) with (P∨R) in Sb by now apply n4_31a.
  specialize n4_31 with Q R.
  intros n4_31b.
  apply propositional_extensionality in n4_31b.
  replace (R∨Q) with (Q∨R) in Sb by now apply n4_31b.
  specialize Imp3_31 with (¬R) (P∨R↔Q∨R) (P↔Q).
  intros Imp3_31b.
  MP Imp3_31b Sb.
  specialize n4_3 with (P ∨ R ↔ Q ∨ R) (¬R).
  intros n4_3b. 
  apply propositional_extensionality in n4_3b.
  replace (¬R ∧ (P ∨ R ↔ Q ∨ R)) with 
    ((P ∨ R ↔ Q ∨ R) ∧ ¬R) in Imp3_31b
    by now apply n4_3b.
  specialize Exp3_3 with 
    (P ∨ R ↔ Q ∨ R) (¬R) (P ↔ Q).
  intros Exp3_3c.
  MP Exp3_3c Imp3_31b.
  replace (¬R→(P↔Q)) with (¬¬R∨(P↔Q)) 
    in Exp3_3c by now rewrite Impl1_01.
  specialize n4_13 with R.
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬R) with R in Exp3_3c
    by now apply n4_13a.
  specialize Add1_3 with P R.
  intros Add1_3a.
  specialize Add1_3 with Q R.
  intros Add1_3b.
  Conj Add1_3a Add1_3b Cb.
  specialize Comp3_43 with (R) (P∨R) (Q∨R).
  intros Comp3_43b.
  MP Comp3_43b Cb.
  specialize n5_1 with (P ∨ R) (Q ∨ R).
  intros n5_1a.
  Syll Comp3_43b n5_1a Sc.
  specialize n4_37 with P Q R.
  intros n4_37a.
  Conj Sc n4_37a Cc.
  specialize n4_77 with (P ∨ R ↔ Q ∨ R)
    R (P↔Q).
  intros n4_77a.
  rewrite Equiv4_01 in n4_77a.
  specialize Simp3_26 with 
    ((R → P ∨ R ↔ Q ∨ R) ∧ 
      (P ↔ Q → P ∨ R ↔ Q ∨ R)
    → R ∨ (P ↔ Q) → P ∨ R ↔ Q ∨ R)
    ((R ∨ (P ↔ Q) → P ∨ R ↔ Q ∨ R)
      → (R → P ∨ R ↔ Q ∨ R) ∧ 
        (P ↔ Q → P ∨ R ↔ Q ∨ R)).
  intros Simp3_26a.
  MP Simp3_26 n4_77a.
  MP Simp3_26a Cc.
  clear n4_77a. clear Cc. clear n4_37a. clear Sa.
    clear n5_1a. clear Comp3_43b. clear Cb. 
    clear Add1_3a. clear Add1_3b. clear Ca. clear Imp3_31b.
    clear n4_74a. clear n4_74b. clear Comp3_43a.
    clear Imp3_31a. clear n4_22a. clear n4_22b. 
    clear Exp3_3a. clear Exp3_3b. clear Sb. clear Sc.
    clear n4_13a. clear n4_3a. clear n4_3b. clear n4_21a.
    clear n4_31a. clear n4_31b. clear n4_32a. clear n4_32b.
  Conj Exp3_3c Simp3_26a Cdd.
  Equiv Cdd.
  exact Cdd.
Qed.

Theorem n5_71 : ∀ P Q R : Prop,
  (Q → ¬R) → (((P ∨ Q) ∧ R) ↔ (P ∧ R)).
  Proof. intros P Q R.
  specialize n4_62 with Q R.
  intros n4_62a.
  specialize n4_51 with Q R.
  intros n4_51a.
  specialize n4_21 with (¬(Q∧R)) (¬Q∨¬R).
  intros n4_21a.
  rewrite Equiv4_01 in n4_21a.
  specialize Simp3_26 with 
    ((¬(Q∧R)↔(¬Q∨¬R))→((¬Q∨¬R)↔¬(Q∧R)))
    (((¬Q∨¬R)↔¬(Q∧R))→(¬(Q∧R)↔(¬Q∨¬R))).
  intros Simp3_26a.
  MP Simp3_26a n4_21a.
  MP Simp3_26a n4_51a.
  clear n4_21a. clear n4_51a.
  Conj n4_62a Simp3_26a C.
  specialize n4_22 with 
    (Q→¬R) (¬Q∨¬R) (¬(Q∧R)).
  intros n4_22a.
  MP n4_22a C.
  replace ((Q→¬R)↔¬(Q∧R)) with 
      (((Q→¬R)→¬(Q∧R))
      ∧
      (¬(Q∧R)→(Q→¬R))) in n4_22a
      by now rewrite Equiv4_01.
  specialize Simp3_26 with 
      ((Q→¬R)→¬(Q∧R)) (¬(Q∧R)→(Q→¬R)).
  intros Simp3_26b.
  MP Simp3_26b n4_22a.
  specialize n4_74 with (Q∧R) (P∧R).
  intros n4_74a.
  Syll Simp3_26a n4_74a Sa.
  specialize n4_31 with (Q∧R) (P∧R).
  intros n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace ((P∧R)∨(Q∧R)) with ((Q∧R)∨(P∧R))
       in Sa by now rewrite n4_31a.
  specialize n4_31 with (R∧Q) (R∧P).
  intros n4_31b. (*Not cited*)
  apply propositional_extensionality in n4_31b.
  specialize n4_21 with ((P∨Q)∧R) (P∧R).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  specialize n4_4 with R P Q.
  intros n4_4a.
  replace (R ∧ P ∨ R ∧ Q) with (R ∧ Q ∨ R ∧ P) 
    in n4_4a by now apply n4_31b.
  specialize n4_3 with P R.
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace (R ∧ P) with (P ∧ R) in n4_4a 
    by now apply n4_3a.
  specialize n4_3 with Q R.
  intros n4_3b.
  apply propositional_extensionality in n4_3b.
  replace (R ∧ Q) with (Q ∧ R) in n4_4a 
    by now apply n4_3b.
  apply propositional_extensionality in n4_4a.
  replace ((Q∧R)∨(P∧R)) with (R∧(P∨Q)) in Sa
    by now apply n4_4a.
  specialize n4_3 with (P∨Q) R.
  intros n4_3c. (*Not cited*)
  apply propositional_extensionality in n4_3c. 
  replace (R∧(P∨Q)) with ((P∨Q)∧R) in Sa
    by now apply n4_3c.
  replace ((P∧R)↔((P∨Q)∧R)) with 
      (((P∨Q)∧R)↔(P∧R)) in Sa
      by now apply n4_21a.
  exact Sa.
Qed.

Theorem n5_74 : ∀ P Q R : Prop,
  (P → (Q ↔ R)) ↔ ((P → Q) ↔ (P → R)).
  Proof. intros P Q R.
  specialize n5_41 with P Q R.
  intros n5_41a.
  specialize n5_41 with P R Q.
  intros n5_41b.
  Conj n5_41a n5_41b C.
  specialize n4_38 with 
      ((P→Q)→(P→R)) ((P→R)→(P→Q)) 
      (P→Q→R) (P→R→Q).
  intros n4_38a.
  MP n4_38a C.
  replace (((P→Q)→(P→R))∧((P→R)→(P→Q))) 
    with ((P→Q)↔(P→R)) in n4_38a
    by now rewrite Equiv4_01.
  specialize n4_76 with P (Q→R) (R→Q).
  intros n4_76a.
  replace ((Q→R)∧(R→Q)) with (Q↔R) in n4_76a
    by now rewrite Equiv4_01.
  apply propositional_extensionality in n4_76a.
  replace ((P→Q→R)∧(P→R→Q)) with 
      (P→(Q↔R)) in n4_38a by now apply n4_76a.
  specialize n4_21 with (P→Q↔R) 
    ((P→Q)↔(P→R)).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (((P→Q)↔(P→R))↔(P→Q↔R)) with 
      ((P→(Q↔R))↔((P→Q)↔(P→R))) in n4_38a
      by now apply n4_21a.
  exact n4_38a.
Qed.

Theorem n5_75 : ∀ P Q R : Prop,
  ((R → ¬Q) ∧ (P ↔ Q ∨ R)) → ((P ∧ ¬Q) ↔ R).
  Proof. intros P Q R.
  specialize n5_6 with P Q R.
  intros n5_6a.
  replace ((P∧¬Q→R)↔(P→Q∨R)) with 
      (((P∧¬Q→R)→(P→Q∨R)) ∧
      ((P→Q∨R)→(P∧¬Q→R))) in n5_6a
      by now rewrite Equiv4_01.
  specialize Simp3_27 with 
      ((P∧¬Q→R)→(P→Q∨R)) 
      ((P→Q∨R)→(P∧¬Q→R)).
  intros Simp3_27a.
  MP Simp3_27a n5_6a.
  specialize Simp3_26 with 
    (P→(Q∨R)) ((Q∨R)→P).
  intros Simp3_26a.
  replace ((P→(Q∨R))∧((Q∨R)→P)) with 
      (P↔(Q∨R)) in Simp3_26a
      by now rewrite Equiv4_01.
  Syll Simp3_26a Simp3_27a Sa.
  specialize Simp3_27 with 
    (R→¬Q) (P↔(Q∨R)).
  intros Simp3_27b.
  Syll Simp3_27b Sa Sb.
  specialize Simp3_27 with 
    (P→(Q∨R)) ((Q∨R)→P).
  intros Simp3_27c.
  replace ((P→(Q∨R))∧((Q∨R)→P)) with 
      (P↔(Q∨R)) in Simp3_27c 
      by now rewrite Equiv4_01.
  Syll Simp3_27b Simp3_27c Sc.
  specialize n4_77 with P Q R.
  intros n4_77a.
  apply propositional_extensionality in n4_77a.
  replace (Q∨R→P) with ((Q→P)∧(R→P)) in Sc
    by now apply n4_77a.
  specialize Simp3_27 with (Q→P) (R→P).
  intros Simp3_27d.
  Syll Sa Simp3_27d Sd.
  specialize Simp3_26 with (R→¬Q) (P↔(Q∨R)).
  intros Simp3_26b.
  Conj Sd Simp3_26b Ca.
  specialize Comp3_43 with 
      ((R→¬Q)∧(P↔(Q∨R))) (R→P) (R→¬Q).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  specialize Comp3_43 with R P (¬Q).
  intros Comp3_43b.
  Syll Comp3_43a Comp3_43b Se.
  clear n5_6a. clear Simp3_27a. 
      clear Simp3_27c. clear Simp3_27d. 
      clear Simp3_26a.  clear Comp3_43b. 
      clear Simp3_26b. clear Comp3_43a.
      clear Sa. clear Sc. clear Sd. clear Ca. 
      clear n4_77a. clear Simp3_27b. 
  Conj Sb Se Cb.
  specialize Comp3_43 with 
    ((R→¬Q)∧(P↔Q∨R)) 
    (P∧¬Q→R) (R→P∧¬Q).
  intros Comp3_43c.
  MP Comp3_43c Cb.
  replace ((P∧¬Q→R)∧(R→P∧¬Q)) with 
      (P∧¬Q↔R) in Comp3_43c 
      by now rewrite Equiv4_01.
  exact Comp3_43c.
Qed.
