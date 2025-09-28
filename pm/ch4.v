Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.

Theorem Equiv4_01 : ∀ P Q : Prop, 
  (P ↔ Q) = ((P → Q) ∧ (Q → P)). 
Proof. intros. reflexivity. Qed.

(* Theorem Equiv4_01 : ∀ P Q : Prop, 
(P ↔ Q) = ((P → Q) ∧ (Q → P)). 
Proof. intros P Q.
apply propositional_extensionality.
specialize iff_to_and with P Q.
intros iff_to_and.
exact iff_to_and.
Qed. *)
(*This is a notational definition in Principia;
it is used to switch between "↔" and "→∧←".*)

(*Axiom Abb4_02 : ∀ P Q R : Prop,
(P ↔ Q ↔ R) = ((P ↔ Q) ∧ (Q ↔ R)).*)
(*Since Coq forbids ill-formed strings, or else 
automatically associates to the right, we leave 
this notational axiom commented out.*)

Ltac Equiv H1 :=
  match goal with 
    | [ H1 : (?P→?Q) ∧ (?Q→?P) |- _ ] => 
      replace ((P→Q) ∧ (Q→P)) with (P↔Q) in H1
      by now rewrite Equiv4_01
  end. 

Theorem Transp4_1 : ∀ P Q : Prop,
  (P → Q) ↔ (¬Q → ¬P).
Proof. intros P Q.
  pose (Transp2_16 P Q) as Transp2_16a.
  pose (Transp2_17 P Q) as Transp2_17a. 
  Conj Transp2_16a Transp2_17a C.
  Equiv C. 
  exact C.
Qed.

Theorem Transp4_11 : ∀ P Q : Prop,
  (P ↔ Q) ↔ (¬P ↔ ¬Q).
Proof. intros P Q.
  pose (Transp2_16 P Q) as Transp2_16a.
  pose (Transp2_16 Q P) as Transp2_16b.
  Conj Transp2_16a Transp2_16b Ca.
  specialize n3_47 with (P→Q) (Q→P) (¬Q→¬P) (¬P→¬Q). 
  intros n3_47a.
  MP n3_47 Ca.
  specialize n3_22 with (¬Q → ¬P) (¬P → ¬Q). 
  intros n3_22a.
  Syll n3_47a n3_22a Sa.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q) in Sa
    by now rewrite Equiv4_01.
  replace ((¬P → ¬Q) ∧ (¬Q → ¬P)) with (¬P↔¬Q) 
    in Sa by now rewrite Equiv4_01.
  clear Transp2_16a. clear Ca. clear Transp2_16b. 
  clear n3_22a. clear n3_47a.
  specialize Transp2_17 with Q P. 
  intros Transp2_17a.
  specialize Transp2_17 with P Q. 
  intros Transp2_17b.
  Conj Transp2_17a Transp2_17b Cb.
  specialize n3_47 with (¬P→¬Q) (¬Q→¬P) (Q→P) (P→Q).
  intros n3_47a.
  MP n3_47a Cb.
  specialize n3_22 with (Q→P) (P→Q).
  intros n3_22a.
  Syll n3_47a n3_22a Sb.
  clear Transp2_17a. clear Transp2_17b. clear Cb. 
      clear n3_47a. clear n3_22a.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q) in Sb
    by now rewrite Equiv4_01.
  replace ((¬P → ¬Q) ∧ (¬Q → ¬P)) with (¬P↔¬Q)
    in Sb by now rewrite Equiv4_01.
  Conj Sa Sb Cc.
  Equiv Cc.
  exact Cc.
Qed.

Theorem n4_12 : ∀ P Q : Prop,
  (P ↔ ¬Q) ↔ (Q ↔ ¬P).
Proof. intros P Q.
  specialize Transp2_03 with P Q. 
  intros Transp2_03a.
  specialize Transp2_15 with Q P. 
  intros Transp2_15a.
  Conj Transp2_03a Transp2_15a Ca.
  specialize n3_47 with (P→¬Q) (¬Q→P) (Q→¬P) (¬P→Q).
  intros n3_47a.
  MP n3_47a C.
  specialize Transp2_03 with Q P. 
  intros Transp2_03b.
  specialize Transp2_15 with P Q. 
  intros Transp2_15b.
  Conj Transp2_03b Transp2_15b Cb.
  specialize n3_47 with (Q→¬P) (¬P→Q) (P→¬Q) (¬Q→P).
  intros n3_47b.
  MP n3_47b H0.
  clear Transp2_03a. clear Transp2_15a. clear Ca. 
  clear Transp2_03b. clear Transp2_15b. clear Cb.
  Conj n3_47a n3_47b Cc.
  rewrite <- Equiv4_01 in Cc.
  rewrite <- Equiv4_01 in Cc.
  rewrite <- Equiv4_01 in Cc.
  exact Cc.
Qed.

Theorem n4_13 : ∀ P : Prop,
  P ↔ ¬¬P.
Proof. intros P.
  specialize n2_12 with P. 
  intros n2_12a.
  specialize n2_14 with P. 
  intros n2_14a.
  Conj n2_12a n2_14a C.
  Equiv C. 
  exact C. 
Qed.

Theorem n4_14 : ∀ P Q R : Prop,
  ((P ∧ Q) → R) ↔ ((P ∧ ¬R) → ¬Q).
Proof. intros P Q R.
  specialize Transp3_37 with P Q R. 
  intros Transp3_37a.
  specialize Transp3_37 with P (¬R) (¬Q).
  intros Transp3_37b.
  Conj Transp3_37a Transp3_37b C.
  specialize n4_13 with Q. 
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  specialize n4_13 with R. 
  intros n4_13b.
  apply propositional_extensionality in n4_13b.
  replace (¬¬Q) with Q in C
  by now apply n4_13a.
  replace (¬¬R) with R in C
  by now apply n4_13b.
  Equiv C. 
  exact C.
Qed.

Theorem n4_15 : ∀ P Q R : Prop,
  ((P ∧ Q) → ¬R) ↔ ((Q ∧ R) → ¬P).
Proof. intros P Q R.
  specialize n4_14 with Q P (¬R). 
  intros n4_14a.
  specialize n3_22 with Q P. 
  intros n3_22a.
  specialize Syll2_06 with (Q∧P) (P∧Q) (¬R). 
  intros Syll2_06a.
  MP Syll2_06a n3_22a.
  specialize n4_13 with R. 
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬R) with R in n4_14a
    by now apply n4_13a.
  rewrite Equiv4_01 in n4_14a.
  specialize Simp3_26 with ((Q ∧ P → ¬R) → Q ∧ R → ¬P) 
      ((Q ∧ R → ¬P) → Q ∧ P → ¬R). 
  intros Simp3_26a.
  MP Simp3_26a n4_14a.
  Syll Syll2_06a Simp3_26a Sa.
  specialize Simp3_27 with ((Q ∧ P → ¬R) → Q ∧ R → ¬P) 
      ((Q ∧ R → ¬P) → Q ∧ P → ¬R). 
  intros Simp3_27a.
  MP Simp3_27a n4_14a.
  specialize n3_22 with P Q. 
  intros n3_22b.
  specialize Syll2_06 with (P∧Q) (Q∧P) (¬R). 
  intros Syll2_06b.
  MP Syll2_06b n3_22b.
  Syll Syll2_06b Simp3_27a Sb.
  clear n4_14a. clear n3_22a. clear Syll2_06a. 
      clear n4_13a. clear Simp3_26a. clear n3_22b.
      clear Simp3_27a. clear Syll2_06b.
  Conj Sa Sb C.
  Equiv C.
  exact C.
Qed.

Theorem n4_2 : ∀ P : Prop,
  P ↔ P.
Proof. intros P.
  specialize n3_2 with (P→P) (P→P). 
  intros n3_2a.
  specialize Id2_08 with P. 
  intros Id2_08a.
  MP n3_2a Id2_08a.
  MP n3_2a Id2_08a.
  Equiv n3_2a.
  exact n3_2a.
Qed.

Theorem n4_21 : ∀ P Q : Prop,
  (P ↔ Q) ↔ (Q ↔ P).
Proof. intros P Q.
  specialize n3_22 with (P→Q) (Q→P). 
  intros n3_22a.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q) 
    in n3_22a by now rewrite Equiv4_01.
  replace ((Q → P) ∧ (P → Q)) with (Q↔P)
  in n3_22a by now rewrite Equiv4_01.
  specialize n3_22 with (Q→P) (P→Q). 
  intros n3_22b.
  replace ((P → Q) ∧ (Q → P)) with (P↔Q) 
    in n3_22b by now rewrite Equiv4_01.
  replace ((Q → P) ∧ (P → Q)) with (Q↔P) 
    in n3_22b by now rewrite Equiv4_01.
  Conj n3_22a n3_22b C.
  Equiv C.
  exact C.
Qed.

Theorem n4_22 : ∀ P Q R : Prop,
  ((P ↔ Q) ∧ (Q ↔ R)) → (P ↔ R).
Proof. intros P Q R.
  specialize Simp3_26 with (P↔Q) (Q↔R). 
  intros Simp3_26a.
  specialize Simp3_26 with (P→Q) (Q→P). 
  intros Simp3_26b.
  replace ((P→Q) ∧ (Q→P)) with (P↔Q) 
    in Simp3_26b by now rewrite Equiv4_01.
  Syll Simp3_26a Simp3_26b Sa.
  specialize Simp3_27 with (P↔Q) (Q↔R). 
  intros Simp3_27a.
  specialize Simp3_26 with (Q→R) (R→Q). 
  intros Simp3_26c.
  replace ((Q→R) ∧ (R→Q)) with (Q↔R) 
    in Simp3_26c by now rewrite Equiv4_01.
  Syll Simp3_27a Simp3_26c Sb.
  specialize n2_83 with ((P↔Q)∧(Q↔R)) P Q R. 
  intros n2_83a.
  MP n2_83a Sa. 
  MP n2_83a Sb.
  specialize Simp3_27 with (P↔Q) (Q↔R). 
  intros Simp3_27b.
  specialize Simp3_27 with (Q→R) (R→Q). 
  intros Simp3_27c.
  replace ((Q→R) ∧ (R→Q)) with (Q↔R) 
    in Simp3_27c by now rewrite Equiv4_01.
  Syll Simp3_27b Simp3_27c Sc.
  specialize Simp3_26 with (P↔Q) (Q↔R).
  intros Simp3_26d.
  specialize Simp3_27 with (P→Q) (Q→P). 
  intros Simp3_27d.
  replace ((P→Q) ∧ (Q→P)) with (P↔Q) 
    in Simp3_27d by now rewrite Equiv4_01.
  Syll Simp3_26d Simp3_27d Sd.
  specialize n2_83 with ((P↔Q)∧(Q↔R)) R Q P. 
  intros n2_83b.
  MP n2_83b Sc. MP n2_83b Sd.
  clear Sd. clear Sb. clear Sc. clear Sa. clear Simp3_26a. 
      clear Simp3_26b. clear Simp3_26c. clear Simp3_26d. 
      clear Simp3_27a. clear Simp3_27b. clear Simp3_27c. 
      clear Simp3_27d.
  Conj n2_83a n2_83b C. 
  specialize Comp3_43 with ((P↔Q)∧(Q↔R)) (P→R) (R→P).
  intros Comp3_43a.
  MP Comp3_43a C.
  replace ((P→R) ∧ (R→P)) with (P↔R) 
    in Comp3_43a by now rewrite Equiv4_01.
  exact Comp3_43a.
Qed.

Theorem n4_24 : ∀ P : Prop,
  P ↔ (P ∧ P).
Proof. intros P.
  specialize n3_2 with P P. 
  intros n3_2a.
  specialize n2_43 with P (P ∧ P). 
  intros n2_43a.
  MP n3_2a n2_43a.
  specialize Simp3_26 with P P. 
  intros Simp3_26a.
  Conj n2_43a Simp3_26a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_25 : ∀ P : Prop,
  P ↔ (P ∨ P).
Proof. intros P.
  specialize Add1_3 with P P.
  intros Add1_3a.
  specialize Taut1_2 with P. 
  intros Taut1_2a.
  Conj Add1_3a Taut1_2a C.
  Equiv C. 
  exact C.
Qed.

Theorem n4_3 : ∀ P Q : Prop,
  (P ∧ Q) ↔ (Q ∧ P).
Proof. intros P Q.
  specialize n3_22 with P Q.
  intros n3_22a.
  specialize n3_22 with Q P.
  intros n3_22b.
  Conj n3_22a n3_22b C.
  Equiv C. 
  exact C.
Qed.

Theorem n4_31 : ∀ P Q : Prop,
  (P ∨ Q) ↔ (Q ∨ P).
Proof. intros P Q.
  specialize Perm1_4 with P Q.
  intros Perm1_4a.
  specialize Perm1_4 with Q P.
  intros Perm1_4b.
  Conj Perm1_4a Perm1_4b C.
  Equiv C. 
  exact C.
Qed.

Theorem n4_32 : ∀ P Q R : Prop,
  ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)).
Proof. intros P Q R.
  specialize n4_15 with P Q R.
  intros n4_15a.
  specialize Transp4_1 with P (¬(Q ∧ R)).
  intros Transp4_1a.
  apply propositional_extensionality in Transp4_1a.
  specialize n4_13 with (Q ∧ R).
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  specialize n4_21 with (¬(P∧Q→¬R)↔¬(P→¬(Q∧R)))
    ((P∧Q→¬R)↔(P→¬(Q∧R))).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (¬¬(Q ∧ R)) with (Q ∧ R) in Transp4_1a
    by now apply n4_13a.
  replace (Q ∧ R→¬P) with (P→¬(Q ∧ R)) in n4_15a
    by now apply Transp4_1a.
  specialize Transp4_11 with (P∧Q→¬R) (P→¬(Q∧R)).
  intros Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((P ∧ Q → ¬R) ↔ (P → ¬(Q ∧ R))) with 
      (¬(P ∧ Q → ¬R) ↔ ¬(P → ¬(Q ∧ R))) in n4_15a
      by now apply Transp4_11a.
  replace (P ∧ Q → ¬R) with 
      (¬(P ∧ Q ) ∨ ¬R) in n4_15a
      by now rewrite Impl1_01.
  replace (P → ¬(Q ∧ R)) with 
      (¬P ∨ ¬(Q ∧ R)) in n4_15a
      by now rewrite Impl1_01.
  replace (¬(¬(P ∧ Q) ∨ ¬R)) with 
      ((P ∧ Q) ∧ R) in n4_15a
      by now rewrite Prod3_01.
  replace (¬(¬P ∨ ¬(Q ∧ R))) with 
      (P ∧ (Q ∧ R )) in n4_15a
      by now rewrite Prod3_01.
  exact n4_15a.
Qed. 
  (*Note that the actual proof uses n4_12, but 
      that transposition involves transforming a 
      biconditional into a conditional. This citation
      of the lemma may be a misprint. Using 
      Transp4_1 to transpose a conditional and 
      then applying n4_13 to double negate does 
      secure the desired formula.*)

Theorem n4_33 : ∀ P Q R : Prop,
  (P ∨ (Q ∨ R)) ↔ ((P ∨ Q) ∨ R).
Proof. intros P Q R.
  specialize n2_31 with P Q R.
  intros n2_31a.
  specialize n2_32 with P Q R.
  intros n2_32a.
  Conj n2_31a n2_32a C.
  Equiv C.
  exact C.
Qed.

  Theorem Abb4_34 : ∀ P Q R : Prop,
(P ∧ Q ∧ R) = ((P ∧ Q) ∧ R).
Proof. intros P Q R.
  apply propositional_extensionality.
  specialize n4_21 with ((P ∧ Q) ∧ R) (P ∧ Q ∧ R).
  intros n4_21.
  replace (((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R) ↔ (P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R))
    with ((((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R) → (P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R)) 
    ∧ ((P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R) → ((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R))) 
    in n4_21 by now rewrite Equiv4_01.
  specialize Simp3_26 with 
    (((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R) → (P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R))
    ((P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R) → ((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R)).
  intros Simp3_26.
  MP Simp3_26 n4_21.
  specialize n4_32 with P Q R.
  intros n4_32.
  MP Simp3_26 n4_32.
  exact Simp3_26.
Qed.

Theorem n4_36 : ∀ P Q R : Prop,
  (P ↔ Q) → ((P ∧ R) ↔ (Q ∧ R)).
Proof. intros P Q R.
  specialize Fact3_45 with P Q R.
  intros Fact3_45a.
  specialize Fact3_45 with Q P R.
  intros Fact3_45b.
  Conj Fact3_45a Fact3_45b C.
  specialize n3_47 with (P→Q) (Q→P) 
      (P ∧ R → Q ∧ R) (Q ∧ R → P ∧ R).
  intros n3_47a.
  MP n3_47 C.
  replace  ((P → Q) ∧ (Q → P)) with (P↔Q) in n3_47a
  by now rewrite Equiv4_01.
  replace ((P∧R→Q∧R)∧(Q∧R→P∧R)) with (P∧R↔Q∧R) 
      in n3_47a by now rewrite Equiv4_01.
  exact n3_47a.
Qed.

Theorem n4_37 : ∀ P Q R : Prop,
  (P ↔ Q) → ((P ∨ R) ↔ (Q ∨ R)).
Proof. intros P Q R.
  specialize Sum1_6 with R P Q.
  intros Sum1_6a.
  specialize Sum1_6 with R Q P.
  intros Sum1_6b.
  Conj Sum1_6a Sum1_6b C.
  specialize n3_47 with (P → Q) (Q → P) 
      (R ∨ P → R ∨ Q) (R ∨ Q → R ∨ P).
  intros n3_47a.
  MP n3_47 C.
  replace  ((P → Q) ∧ (Q → P)) with (P↔Q) in n3_47a
  by now rewrite Equiv4_01.
  replace ((R∨P→R∨Q)∧(R∨Q→R∨P)) with (R∨P↔R∨Q) 
      in n3_47a by now rewrite Equiv4_01.
  specialize n4_31 with Q R.
  intros n4_31a.
  apply propositional_extensionality in n4_31a.
  specialize n4_31 with P R.
  intros n4_31b.
  apply propositional_extensionality in n4_31b.
  replace (R ∨ P) with (P ∨ R) in n3_47a
    by now apply n4_31b.
  replace (R ∨ Q) with (Q ∨ R) in n3_47a
    by now apply n4_31a.
  exact n3_47a.
Qed.

Theorem n4_38 : ∀ P Q R S : Prop,
  ((P ↔ R) ∧ (Q ↔ S)) → ((P ∧ Q) ↔ (R ∧ S)).
Proof. intros P Q R S.
  specialize n3_47 with P Q R S.
  intros n3_47a.
  specialize n3_47 with R S P Q.
  intros n3_47b.
  Conj n3_47a n3_47b Ca.
  specialize n3_47 with ((P→R) ∧ (Q→S)) 
      ((R→P) ∧ (S→Q)) (P ∧ Q → R ∧ S) (R ∧ S → P ∧ Q).
  intros n3_47c.
  MP n3_47c Ca.
  specialize n4_32 with (P→R) (Q→S) ((R→P) ∧ (S → Q)).
  intros n4_32a.
  apply propositional_extensionality in n4_32a.
  symmetry in n4_32a.
  replace (((P → R) ∧ (Q → S)) ∧ (R → P) ∧ (S → Q)) with 
      ((P → R) ∧ (Q → S) ∧ (R → P) ∧ (S → Q)) in n3_47c
      by now apply n4_32a.
  specialize n4_32 with (Q→S) (R→P) (S → Q).
  intros n4_32b.
  apply propositional_extensionality in n4_32b.
  replace ((Q → S) ∧ (R → P) ∧ (S → Q)) with 
      (((Q → S) ∧ (R → P)) ∧ (S → Q)) in n3_47c
      by now apply n4_32b.
  specialize n3_22 with (Q→S) (R→P).
  intros n3_22a.
  specialize n3_22 with (R→P) (Q→S).
  intros n3_22b.
  Conj n3_22a n3_22b Cb.
  Equiv Cb.
  specialize n4_3 with (R→P) (Q→S).
  intros n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((Q → S) ∧ (R → P)) with 
      ((R → P) ∧ (Q → S)) in n3_47c
      by now apply n4_3a.
  specialize n4_32 with (R → P) (Q → S) (S → Q).
  intros n4_32c.
  apply propositional_extensionality in n4_32c.
  symmetry in n4_32c.
  replace (((R → P) ∧ (Q → S)) ∧ (S → Q)) with 
      ((R → P) ∧ (Q → S) ∧ (S → Q)) in n3_47c
      by now apply n4_32c.
  specialize n4_32 with (P→R) (R → P) ((Q → S)∧(S → Q)).
  intros n4_32d.
  apply propositional_extensionality in n4_32d.
  replace ((P → R) ∧ (R → P) ∧ (Q → S) ∧ (S → Q)) with 
      (((P → R) ∧ (R → P)) ∧ (Q → S) ∧ (S → Q)) in n3_47c
      by now apply n4_32d.
  replace ((P→R) ∧ (R → P)) with (P↔R) in n3_47c
  by now rewrite Equiv4_01.
  replace ((Q → S) ∧ (S → Q)) with (Q↔S) in n3_47c
  by now rewrite Equiv4_01.
  replace ((P∧Q→R∧S)∧(R∧S→P∧Q)) with ((P∧Q)↔(R∧S)) 
      in n3_47c by now rewrite Equiv4_01.
  exact n3_47c.
Qed.

Theorem n4_39 : ∀ P Q R S : Prop,
((P ↔ R) ∧ (Q ↔ S)) → ((P ∨ Q) ↔ (R ∨ S)).
Proof.  intros P Q R S.
  specialize n3_48 with P Q R S.
  intros n3_48a.
  specialize n3_48 with R S P Q.
  intros n3_48b.
  Conj n3_48a n3_48b Ca.
  specialize n3_47 with ((P → R) ∧ (Q → S)) 
      ((R → P) ∧ (S → Q)) (P ∨ Q → R ∨ S) (R ∨ S → P ∨ Q).
  intros n3_47a.
  MP n3_47a Ca.
  replace ((P∨Q→R∨S)∧(R∨S→P∨Q)) with ((P∨Q)↔(R∨S)) 
      in n3_47a by now rewrite Equiv4_01.
  specialize n4_32 with ((P → R) ∧ (Q → S)) (R → P) (S → Q).
  intros n4_32a.
  apply propositional_extensionality in n4_32a.
  replace (((P → R) ∧ (Q → S)) ∧ (R → P) ∧ (S → Q)) with 
      ((((P → R) ∧ (Q → S)) ∧ (R → P)) ∧ (S → Q)) in n3_47a
      by now apply n4_32a.
  specialize n4_32 with (P → R) (Q → S) (R → P).
  intros n4_32b.
  apply propositional_extensionality in n4_32b.
  symmetry in n4_32b.
  replace (((P → R) ∧ (Q → S)) ∧ (R → P)) with 
      ((P → R) ∧ (Q → S) ∧ (R → P)) in n3_47a
      by now apply n4_32b.
  specialize n3_22 with (Q → S) (R → P).
  intros n3_22a. 
  specialize n3_22 with (R → P) (Q → S).
  intros n3_22b.
  Conj  n3_22a n3_22b Cb.
  Equiv Cb.
  apply propositional_extensionality in Cb.
  symmetry in Cb.
  replace ((Q → S) ∧ (R → P)) with 
      ((R → P) ∧ (Q → S)) in n3_47a
      by now apply Cb.
  specialize n4_32 with (P → R) (R → P) (Q → S).
  intros n4_32c.
  apply propositional_extensionality in n4_32c.
  replace ((P → R) ∧ (R → P) ∧ (Q → S)) with 
      (((P → R) ∧ (R → P)) ∧ (Q → S)) in n3_47a
      by now apply n4_32c.
  replace ((P → R) ∧ (R → P)) with (P↔R) in n3_47a
    by now rewrite Equiv4_01.
  specialize n4_32 with (P↔R) (Q→S) (S→Q).
  intros n4_32d.
  apply propositional_extensionality in n4_32d.
  symmetry in n4_32d.
  replace (((P ↔ R) ∧ (Q → S)) ∧ (S → Q)) with 
      ((P ↔ R) ∧ (Q → S) ∧ (S → Q)) in n3_47a
      by now apply n4_32d.
  replace ((Q → S) ∧ (S → Q)) with (Q ↔ S) in n3_47a
  by now rewrite Equiv4_01.
  exact n3_47a.
Qed.

Theorem n4_4 : ∀ P Q R : Prop,
  (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)).
Proof. intros P Q R.
  specialize n3_2 with P Q.
  intros n3_2a.
  specialize n3_2 with P R.
  intros n3_2b.
  Conj n3_2a n3_2b Ca.
  specialize Comp3_43 with P (Q→P∧Q) (R→P∧R).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  specialize n3_48 with Q R (P∧Q) (P∧R).
  intros n3_48a.
  Syll Comp3_43a n3_48a Sa.
  specialize Imp3_31 with P (Q∨R) ((P∧ Q) ∨ (P ∧ R)).
  intros Imp3_31a.
  MP Imp3_31a Sa.
  specialize Simp3_26 with P Q.
  intros Simp3_26a.
  specialize Simp3_26 with P R.
  intros Simp3_26b.
  Conj Simp3_26a Simp3_26b Cb.
  specialize n3_44 with P (P∧Q) (P∧R).
  intros n3_44a.
  MP n3_44a Cb.
  specialize Simp3_27 with P Q.
  intros Simp3_27a.
  specialize Simp3_27 with P R.
  intros Simp3_27b.
  Conj Simp3_27a Simp3_27b Cc.
  specialize n3_48 with (P∧Q) (P∧R) Q R.
  intros n3_48b.
  MP n3_48b Cc.
  clear Cc. clear Simp3_27a. clear Simp3_27b.
  Conj n3_44a n3_48b Cdd. (*Cd is reserved*)
  specialize Comp3_43 with (P ∧ Q ∨ P ∧ R) P (Q∨R).
  intros Comp3_43b.
  MP Comp3_43b Cdd.
  clear Cdd. clear Cb. clear n3_44a. clear n3_48b. 
      clear Simp3_26a. clear Simp3_26b.
  Conj Imp3_31a Comp3_43b Ce.
  Equiv Ce.
  exact Ce.
Qed.

Theorem n4_41 : ∀ P Q R : Prop,
  (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)).
Proof. intros P Q R.
  specialize Simp3_26 with Q R.
  intros Simp3_26a.
  specialize Sum1_6 with P (Q ∧ R) Q.
  intros Sum1_6a.
  MP Simp3_26a Sum1_6a.
  specialize Simp3_27 with Q R.
  intros Simp3_27a.
  specialize Sum1_6 with P (Q ∧ R) R.
  intros Sum1_6b.
  MP Simp3_27a Sum1_6b.
  clear Simp3_26a. clear Simp3_27a.
  Conj Sum1_6a Sum1_6a Ca.
  specialize Comp3_43 with (P ∨ Q ∧ R) (P ∨ Q) (P ∨ R).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  specialize n2_53 with P Q. 
  intros n2_53a.
  specialize n2_53 with P R. 
  intros n2_53b.
  Conj n2_53a n2_53b Cb.
  specialize n3_47 with (P ∨ Q) (P ∨ R) (¬P → Q) (¬P → R).
  intros n3_47a.
  MP n3_47a Cb.
  specialize Comp3_43 with (¬P) Q R.
  intros Comp3_43b.
  Syll n3_47a Comp3_43b Sa.
  specialize n2_54 with P (Q∧R).
  intros n2_54a.
  Syll Sa n2_54a Sb.
  clear Sum1_6a. clear Sum1_6b. clear Ca. clear n2_53a.
      clear n2_53b. clear Cb. clear n3_47a. clear Sa.
      clear Comp3_43b. clear n2_54a.
  Conj Comp3_43a Sb Cc.
  Equiv Cc.
  exact Cc.
Qed.

Theorem n4_42 : ∀ P Q : Prop,
  P ↔ ((P ∧ Q) ∨ (P ∧ ¬Q)).
Proof. intros P Q.
  specialize n3_21 with P (Q ∨ ¬Q).
  intros n3_21a.
  specialize n2_11 with Q.
  intros n2_11a.
  MP n3_21a n2_11a.
  specialize Simp3_26 with P (Q ∨ ¬Q).
  intros Simp3_26a. clear n2_11a.
  Conj n3_21a Simp3_26a C.
  Equiv C.
  specialize n4_4 with P Q (¬Q).
  intros n4_4a.
  apply propositional_extensionality in C.
  replace (P ∧ (Q ∨ ¬Q)) with P in n4_4a
    by now apply C.
  exact n4_4a.
Qed.

Theorem n4_43 : ∀ P Q : Prop,
  P ↔ ((P ∨ Q) ∧ (P ∨ ¬Q)).
Proof. intros P Q.
  specialize n2_2 with P Q.
  intros n2_2a.
  specialize n2_2 with P (¬Q).
  intros n2_2b.
  Conj n2_2a n2_2b Ca.
  specialize Comp3_43 with P (P∨Q) (P∨¬Q).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  specialize n2_53 with P Q.
  intros n2_53a.
  specialize n2_53 with P (¬Q).
  intros n2_53b.
  Conj n2_53a n2_53b Cb.
  specialize n3_47 with (P∨Q) (P∨¬Q) (¬P→Q) (¬P→¬Q).
  intros n3_47a.
  MP n3_47a Cb.
  specialize n2_65 with (¬P) Q. 
  intros n2_65a.
  specialize n4_13 with P.
  intros n4_13a. 
  apply propositional_extensionality in n4_13a.
  replace (¬¬P) with P in n2_65a by now apply n4_13a.
  specialize Imp3_31 with (¬P → Q) (¬P → ¬Q) (P).
  intros Imp3_31a.
  MP Imp3_31a n2_65a.
  Syll n3_47a Imp3_31a Sa.
  clear n2_2a. clear n2_2b. clear Ca. clear n2_53a. 
    clear n2_53b. clear Cb. clear n2_65a. 
    clear n3_47a. clear Imp3_31a. clear n4_13a.
  Conj Comp3_43a Sa Cc.
  Equiv Cc.
  exact Cc.
Qed.

Theorem n4_44 : ∀ P Q : Prop,
  P ↔ (P ∨ (P ∧ Q)).
Proof. intros P Q.
  specialize n2_2 with P (P∧Q).
  intros n2_2a.
  specialize Id2_08 with P.
  intros Id2_08a.
  specialize Simp3_26 with P Q.
  intros Simp3_26a.
  Conj Id2_08a Simp3_26a Ca.
  specialize n3_44 with P P (P ∧ Q).
  intros n3_44a.
  MP n3_44a Ca.
  clear Ca. clear Id2_08a. clear Simp3_26a.
  Conj n2_2a n3_44a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_45 : ∀ P Q : Prop,
  P ↔ (P ∧ (P ∨ Q)).
Proof. intros P Q.
  specialize n2_2 with (P ∧ P) (P ∧ Q).
  intros n2_2a.
  specialize n4_4 with P P Q.
  intros n4_4a.
  apply propositional_extensionality in n4_4a.
  replace (P∧P∨P∧Q) with (P∧(P∨Q)) in n2_2a
    by now apply n4_4a.
  specialize n4_24 with P.
  intros n4_24a.
  apply propositional_extensionality in n4_24a.
  replace (P ∧ P) with P in n2_2a 
    by now apply n4_24a.
  specialize Simp3_26 with P (P ∨ Q).
  intros Simp3_26a.
  clear n4_4a. clear n4_24a.
  Conj n2_2a Simp3_26a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_5 : ∀ P Q : Prop,
  P ∧ Q ↔ ¬(¬P ∨ ¬Q).
Proof. intros P Q.
  specialize n4_2 with (P ∧ Q).
  intros n4_2a.
  replace ((P ∧ Q)↔(P ∧ Q)) with 
    ((P ∧ Q)↔¬(¬P ∨ ¬Q)) in n4_2a 
    by now rewrite Prod3_01.
  exact n4_2a.
Qed.

Theorem n4_51 : ∀ P Q : Prop,
  ¬(P ∧ Q) ↔ (¬P ∨ ¬Q).
Proof. intros P Q.
  specialize n4_5 with P Q.
  intros n4_5a.
  specialize n4_12 with (P ∧ Q) (¬P ∨ ¬Q).
  intros n4_12a.
  specialize Simp3_26 with 
    ((P ∧ Q ↔ ¬(¬P ∨ ¬Q)) → (¬P ∨ ¬Q ↔ ¬(P ∧ Q)))
    ((¬P ∨ ¬Q ↔ ¬(P ∧ Q)) → ((P ∧ Q ↔ ¬(¬P ∨ ¬Q)))).
  intros Simp3_26a.
  replace ((P ∧ Q ↔ ¬(¬P ∨ ¬Q)) ↔ (¬P ∨ ¬Q ↔ ¬(P ∧ Q)))
    with (((P ∧ Q ↔ ¬(¬P ∨ ¬Q)) → (¬P ∨ ¬Q ↔ ¬(P ∧ Q)))
    ∧ ((¬P ∨ ¬Q ↔ ¬(P ∧ Q)) → ((P ∧ Q ↔ ¬(¬P ∨ ¬Q)))))
    in n4_12a by now rewrite Equiv4_01.
  MP Simp3_26a n4_12a.
  MP Simp3_26a n4_5a.
  specialize n4_21 with (¬(P ∧ Q)) (¬P ∨ ¬Q).
  intros n4_21a.
  specialize Simp3_27 with 
  (((¬(P ∧ Q) ↔ ¬P ∨ ¬Q)) → ((¬P ∨ ¬Q ↔ ¬(P ∧ Q))))
  (((¬P ∨ ¬Q ↔ ¬(P ∧ Q))) → ((¬(P ∧ Q) ↔ ¬P ∨ ¬Q))).
  intros Simp3_27a.
  MP Simp3_27a n4_21a.
  MP Simp3_27a Simp3_26a.
  exact Simp3_27a.
Qed.

Theorem n4_52 : ∀ P Q : Prop,
  (P ∧ ¬Q) ↔ ¬(¬P ∨ Q).
Proof. intros P Q.
  specialize n4_5 with P (¬Q).
  intros n4_5a.
  specialize n4_13 with Q.
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬Q) with Q in n4_5a 
    by now apply n4_13a.
  exact n4_5a.
Qed.

Theorem n4_53 : ∀ P Q : Prop,
  ¬(P ∧ ¬Q) ↔ (¬P ∨ Q).
Proof. intros P Q.
  specialize n4_52 with P Q.
  intros n4_52a.
  specialize n4_12 with (P ∧ ¬Q) ((¬P ∨ Q)).
  intros n4_12a.
  replace ((P ∧ ¬Q ↔ ¬(¬P ∨ Q)) ↔ (¬P ∨ Q ↔ ¬(P ∧ ¬Q)))
    with (((P ∧ ¬Q ↔ ¬(¬P ∨ Q)) → (¬P ∨ Q ↔ ¬(P ∧ ¬Q)))
    ∧ ((¬P ∨ Q ↔ ¬(P ∧ ¬Q)) → (P ∧ ¬Q ↔ ¬(¬P ∨ Q))))
    in n4_12a by now rewrite Equiv4_01.
  specialize Simp3_26 with 
    ((P ∧ ¬Q ↔ ¬(¬P ∨ Q)) → (¬P ∨ Q ↔ ¬(P ∧ ¬Q)))
    ((¬P ∨ Q ↔ ¬(P ∧ ¬Q)) → (P ∧ ¬Q ↔ ¬(¬P ∨ Q))).
  intros Simp3_26a.
  MP Simp3_26a n4_12a.
  MP Simp3_26a n4_52a.
  specialize n4_21 with (¬(P ∧ ¬Q)) (¬P ∨ Q).
  intros n4_21a.
  replace ((¬(P ∧ ¬ Q) ↔ ¬P ∨ Q) ↔ (¬P ∨ Q ↔ ¬(P ∧ ¬Q)))
    with (((¬(P ∧ ¬ Q) ↔ ¬P ∨ Q) → (¬P ∨ Q ↔ ¬(P ∧ ¬Q)))
    ∧ ((¬P ∨ Q ↔ ¬(P ∧ ¬Q)) → (¬(P ∧ ¬ Q) ↔ ¬P ∨ Q)))
    in n4_21a by now rewrite Equiv4_01.
  specialize Simp3_27 with 
    ((¬(P ∧ ¬ Q) ↔ ¬P ∨ Q) → (¬P ∨ Q ↔ ¬(P ∧ ¬Q)))
    ((¬P ∨ Q ↔ ¬(P ∧ ¬Q)) → (¬(P ∧ ¬ Q) ↔ ¬P ∨ Q)).
  intros Simp3_27a.
  MP Simp3_27a n4_21a.
  MP Simp3_27a Simp3_26a.
  exact Simp3_27a.
Qed.

Theorem n4_54 : ∀ P Q : Prop,
  (¬P ∧ Q) ↔ ¬(P ∨ ¬Q).
Proof. intros P Q.
  specialize n4_5 with (¬P) Q.
  intros n4_5a.
  specialize n4_13 with P.
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬P) with P in n4_5a
   by now apply n4_13a.
  exact n4_5a.
Qed.

Theorem n4_55 : ∀ P Q : Prop,
  ¬(¬P ∧ Q) ↔ (P ∨ ¬Q).
Proof. intros P Q.
  specialize n4_54 with P Q.
  intros n4_54a.
  specialize n4_12 with (¬P ∧ Q) (P ∨ ¬Q).
  intros n4_12a.
  apply propositional_extensionality in n4_12a.
  symmetry in n4_12a.
  replace (¬P ∧ Q ↔ ¬(P ∨ ¬Q)) with 
      (P ∨ ¬Q ↔ ¬(¬P ∧ Q)) in n4_54a 
      by now apply n4_12a.
  specialize n4_21 with (¬(¬P ∧ Q)) (P ∨ ¬Q).
  intros n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∨ ¬Q ↔ ¬(¬P ∧ Q)) with 
      (¬(¬P ∧ Q) ↔ (P ∨ ¬Q)) in n4_54a
      by now apply n4_21a.
  exact n4_54a.
Qed.

Theorem n4_56 : ∀ P Q : Prop,
  (¬P ∧ ¬Q) ↔ ¬(P ∨ Q).
Proof. intros P Q.
  specialize n4_54 with P (¬Q).
  intros n4_54a.
  specialize n4_13 with Q.
  intros n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬Q) with Q in n4_54a 
    by now apply n4_13a.
  exact n4_54a.
Qed.

Theorem n4_57 : ∀ P Q : Prop,
  ¬(¬P ∧ ¬Q) ↔ (P ∨ Q).
Proof. intros P Q.
  specialize n4_56 with P Q.
  intros n4_56a.
  specialize n4_12 with (¬P ∧ ¬Q) (P ∨ Q).
  intros n4_12a.
  apply propositional_extensionality in n4_12a.
  symmetry in n4_12a.
  replace (¬P ∧ ¬Q ↔ ¬(P ∨ Q)) with 
      (P ∨ Q ↔ ¬(¬P ∧ ¬Q)) in n4_56a
      by now apply n4_12a.
  specialize n4_21 with (¬(¬P ∧ ¬Q)) (P ∨ Q).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (P ∨ Q ↔ ¬(¬P ∧ ¬Q)) with 
      (¬(¬P ∧ ¬Q) ↔ P ∨ Q) in n4_56a
      by now apply n4_21a.
  exact n4_56a.
Qed.
  
Theorem n4_6 : ∀ P Q : Prop,
  (P → Q) ↔ (¬P ∨ Q).
Proof. intros P Q.
  specialize n4_2 with (¬P∨ Q).
  intros n4_2a.
  rewrite Impl1_01.
  exact n4_2a.
Qed.

Theorem n4_61 : ∀ P Q : Prop,
  ¬(P → Q) ↔ (P ∧ ¬Q).
Proof. intros P Q.
  specialize n4_6 with P Q.
  intros n4_6a.
  specialize Transp4_11 with (P→Q) (¬P∨Q).
  intros Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((P → Q) ↔ ¬P ∨ Q) with 
      (¬(P → Q) ↔ ¬(¬P ∨ Q)) in n4_6a
      by now apply Transp4_11a.
  specialize n4_52 with P Q.
  intros n4_52a.
  apply propositional_extensionality in n4_52a.
  replace (¬(¬P ∨ Q)) with (P ∧ ¬Q) in n4_6a
    by now apply n4_52a.
  exact n4_6a.
Qed.

Theorem n4_62 : ∀ P Q : Prop,
  (P → ¬Q) ↔ (¬P ∨ ¬Q).
Proof. intros P Q.
  specialize n4_6 with P (¬Q).
  intros n4_6a.
  exact n4_6a.
Qed.

Theorem n4_63 : ∀ P Q : Prop,
  ¬(P → ¬Q) ↔ (P ∧ Q).
Proof. intros P Q.
  specialize n4_62 with P Q.
  intros n4_62a.
  specialize Transp4_11 with (P → ¬Q) (¬P ∨ ¬Q).
  intros Transp4_11a.
  specialize n4_5 with P Q.
  intros n4_5a.
  apply propositional_extensionality in n4_5a.
  replace (¬(¬P ∨ ¬Q)) with (P ∧ Q) in Transp4_11a
    by now apply n4_5a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((P → ¬Q) ↔ ¬P ∨ ¬Q) with 
      ((¬(P → ¬Q) ↔ P ∧ Q)) in n4_62a
      by now apply Transp4_11a.
  exact n4_62a.
Qed.
(*One could use Prod3_01 in lieu of n4_5.*)

Theorem n4_64 : ∀ P Q : Prop,
  (¬P → Q) ↔ (P ∨ Q).
Proof. intros P Q.
  specialize n2_54 with P Q.
  intros n2_54a.
  specialize n2_53 with P Q.
  intros n2_53a.
  Conj n2_54a n2_53a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_65 : ∀ P Q : Prop,
  ¬(¬P → Q) ↔ (¬P ∧ ¬Q).
Proof. intros P Q.
  specialize n4_64 with P Q.
  intros n4_64a.
  specialize Transp4_11 with(¬P → Q) (P ∨ Q).
  intros Transp4_11a.
  specialize n4_21 with (¬(¬P → Q)↔¬(P ∨ Q))
      ((¬P → Q)↔(P ∨ Q)).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (((¬P→Q)↔P∨Q)↔(¬(¬P→Q)↔¬(P∨Q))) with 
      ((¬(¬P→Q)↔¬(P∨Q))↔((¬P→Q)↔P∨Q)) in Transp4_11a
      by now apply n4_21a.
  apply propositional_extensionality in Transp4_11a.
  replace ((¬P → Q) ↔ P ∨ Q) with 
      (¬(¬P → Q) ↔ ¬(P ∨ Q)) in n4_64a
      by now apply Transp4_11a.
  specialize n4_56 with P Q.
  intros n4_56a.
  apply propositional_extensionality in n4_56a.
  replace (¬(P ∨ Q)) with (¬P ∧ ¬Q) in n4_64a
    by now apply n4_56a.
  exact n4_64a.
Qed.

Theorem n4_66 : ∀ P Q : Prop,
  (¬P → ¬Q) ↔ (P ∨ ¬Q).
Proof. intros P Q.
  specialize n4_64 with P (¬Q).
  intros n4_64a.
  exact n4_64a.
Qed.

Theorem n4_67 : ∀ P Q : Prop,
  ¬(¬P → ¬Q) ↔ (¬P ∧ Q).
Proof. intros P Q.
  specialize n4_66 with P Q.
  intros n4_66a.
  specialize Transp4_11 with (¬P → ¬Q) (P ∨ ¬Q).
  intros Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((¬P → ¬Q) ↔ P ∨ ¬Q) with 
      (¬(¬P → ¬Q) ↔ ¬(P ∨ ¬Q)) in n4_66a
      by now apply Transp4_11a.
  specialize n4_54 with P Q.
  intros n4_54a.
  apply propositional_extensionality in n4_54a.
  replace (¬(P ∨ ¬Q)) with (¬P ∧ Q) in n4_66a
    by now apply n4_54a.
  exact n4_66a.
Qed.

Theorem n4_7 : ∀ P Q : Prop,
  (P → Q) ↔ (P → (P ∧ Q)).
Proof. intros P Q.
  specialize Comp3_43 with P P Q.
  intros Comp3_43a.
  specialize Exp3_3 with 
      (P → P) (P → Q) (P → P ∧ Q).
  intros Exp3_3a.
  MP Exp3_3a Comp3_43a.
  specialize Id2_08 with P.
  intros Id2_08a.
  MP Exp3_3a Id2_08a.
  specialize Simp3_27 with P Q.
  intros Simp3_27a.
  specialize Syll2_05 with P (P ∧ Q) Q.
  intros Syll2_05a.
  MP Syll2_05a Simp3_27a.
  clear Id2_08a. clear Comp3_43a. clear Simp3_27a.
  Conj Syll2_05a Exp3_3a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_71 : ∀ P Q : Prop,
  (P → Q) ↔ (P ↔ (P ∧ Q)).
Proof. intros P Q.
  specialize n4_7 with P Q.
  intros n4_7a.
  specialize n3_21 with (P→(P∧Q)) ((P∧Q)→P).
  intros n3_21a.
  replace ((P→P∧Q)∧(P∧Q→P)) with (P↔(P∧Q)) 
      in n3_21a by now rewrite Equiv4_01.
  specialize Simp3_26 with P Q.
  intros Simp3_26a.
  MP n3_21a Simp3_26a.
  specialize Simp3_26 with (P→(P∧Q)) ((P∧Q)→P).
  intros Simp3_26b.
  replace ((P→P∧Q)∧(P∧Q→P)) with (P↔(P∧Q)) 
    in Simp3_26b by now rewrite Equiv4_01.
  clear Simp3_26a.
  Conj n3_21a Simp3_26b Ca.
  Equiv Ca.
  clear n3_21a. clear Simp3_26b.
  Conj n4_7a Ca Cb.
  specialize n4_22 with (P → Q) (P → P ∧ Q) (P ↔ P ∧ Q).
  intros n4_22a.
  MP n4_22a Cb.
  exact n4_22a.
Qed.

Theorem n4_72 : ∀ P Q : Prop,
  (P → Q) ↔ (Q ↔ (P ∨ Q)).
Proof. intros P Q.
  specialize Transp4_1 with P Q.
  intros Transp4_1a.
  specialize n4_71 with (¬Q) (¬P).
  intros n4_71a.
  Conj Transp4_1a n4_71a Ca.
  specialize n4_22 with 
      (P→Q) (¬Q→¬P) (¬Q↔¬Q ∧ ¬P).
  intros n4_22a.
  MP n4_22a Ca.
  specialize n4_21 with (¬Q) (¬Q ∧ ¬P).
  intros n4_21a.
  Conj n4_22a n4_21a Cb.
  specialize n4_22 with 
      (P→Q) (¬Q ↔ ¬Q ∧ ¬P) (¬Q ∧ ¬P ↔ ¬Q).
  intros n4_22b.
  MP n4_22b Cb.
  specialize n4_12 with (¬Q ∧ ¬P) (Q).
  intros n4_12a.
  Conj n4_22b n4_12a Cc.
  specialize n4_22 with 
      (P → Q) ((¬Q ∧ ¬P) ↔ ¬Q) (Q ↔ ¬(¬Q ∧ ¬P)).
  intros n4_22c.
  MP n4_22b Cc.
  specialize n4_57 with Q P.
  intros n4_57a.
  apply propositional_extensionality in n4_57a.
  symmetry in n4_57a.
  replace (¬(¬Q ∧ ¬P)) with (Q ∨ P) in n4_22c
    by now apply n4_57a.
  specialize n4_31 with P Q.
  intros n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n4_22c
    by now apply n4_31a.
  exact n4_22c.
Qed.
(*One could use Prod3_01 in lieu of n4_57.*)

Theorem n4_73 : ∀ P Q : Prop,
  Q → (P ↔ (P ∧ Q)).
Proof. intros P Q.
  specialize Simp2_02 with P Q.
  intros Simp2_02a.
  specialize n4_71 with P Q.
  intros n4_71a.
  replace ((P → Q) ↔ (P ↔ P ∧ Q)) with 
      (((P→Q)→(P↔P∧Q))∧((P↔P∧Q)→(P→Q))) 
      in n4_71a by now rewrite Equiv4_01.
  specialize Simp3_26 with 
      ((P → Q) → P ↔ P ∧ Q) (P ↔ P ∧ Q → P → Q).
  intros Simp3_26a.
  MP Simp3_26a n4_71a.
  Syll Simp2_02a Simp3_26a Sa.
  exact Sa.
Qed.

Theorem n4_74 : ∀ P Q : Prop,
  ¬P → (Q ↔ (P ∨ Q)).
Proof. intros P Q.
  specialize n2_21 with P Q.
  intros n2_21a.
  specialize n4_72 with P Q.
  intros n4_72a.
  apply propositional_extensionality in n4_72a.
  symmetry in n4_72a.
  replace (P → Q) with (Q ↔ P ∨ Q) in n2_21a
    by now apply n4_72a.
  exact n2_21a.
Qed.

Theorem n4_76 : ∀ P Q R : Prop,
  ((P → Q) ∧ (P → R)) ↔ (P → (Q ∧ R)).
Proof. intros P Q R.
  specialize n4_41 with (¬P) Q R.
  intros n4_41a.
  replace (¬P ∨ Q) with (P→Q) in n4_41a
    by now rewrite Impl1_01.
  replace (¬P ∨ R) with (P→R) in n4_41a
    by now rewrite Impl1_01.
  replace (¬P ∨ Q ∧ R) with (P → Q ∧ R) in n4_41a
    by now rewrite Impl1_01.
  specialize n4_21 with ((P → Q) ∧ (P → R)) (P → Q ∧ R).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((P → Q ∧ R) ↔ (P → Q) ∧ (P → R)) with 
      ((P → Q) ∧ (P → R) ↔ (P → Q ∧ R)) in n4_41a
      by now apply n4_21a.
  exact n4_41a.
Qed.

Theorem n4_77 : ∀ P Q R : Prop,
  ((Q → P) ∧ (R → P)) ↔ ((Q ∨ R) → P).
Proof. intros P Q R.
  specialize n3_44 with P Q R.
  intros n3_44a.
  specialize n2_2 with Q R.
  intros n2_2a.
  specialize Add1_3 with Q R.
  intros Add1_3a.
  specialize Syll2_06 with Q (Q ∨ R) P.
  intros Syll2_06a.
  MP Syll2_06a n2_2a.
  specialize Syll2_06 with R (Q ∨ R) P.
  intros Syll2_06b.
  MP Syll2_06b Add1_3a.
  Conj Syll2_06a Syll2_06b Ca.
  specialize Comp3_43 with ((Q ∨ R)→P)
    (Q→P) (R→P).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  clear n2_2a. clear Add1_3a. clear Ca.
    clear Syll2_06a. clear Syll2_06b.
  Conj n3_44a Comp3_43a Cb.
  Equiv Cb.
  exact Cb.
Qed. 

Theorem n4_78 : ∀ P Q R : Prop,
  ((P → Q) ∨ (P → R)) ↔ (P → (Q ∨ R)).
Proof. intros P Q R.
  specialize n4_2 with ((P→Q) ∨ (P → R)).
  intros n4_2a.
  replace (((P→Q)∨(P→R))↔((P→Q)∨(P→R))) with 
      (((P → Q) ∨ (P → R))↔((P → Q) ∨ ¬P ∨ R)) in n4_2a
      by now rewrite <- Impl1_01.
  replace (((P → Q) ∨ (P → R))↔((P → Q) ∨ ¬P ∨ R)) with 
      (((P → Q) ∨ (P → R))↔((¬P ∨ Q) ∨ ¬P ∨ R)) in n4_2a
      by now rewrite <- Impl1_01.
  specialize n4_33 with (¬P) Q (¬P ∨ R).
  intros n4_33a.
  apply propositional_extensionality in n4_33a.
  replace ((¬P ∨ Q) ∨ ¬P ∨ R) with 
      (¬P ∨ Q ∨ ¬P ∨ R) in n4_2a 
      by now apply n4_33a.
  specialize n4_33 with Q (¬P) R.
  intros n4_33b.
  apply propositional_extensionality in n4_33b.
  symmetry in n4_33b.
  replace (Q ∨ ¬P ∨ R) with 
      ((Q ∨ ¬P) ∨ R) in n4_2a
      by now apply n4_33b.
  specialize n4_31 with (¬P) Q.
  intros n4_31a.
  specialize n4_37 with (¬P∨Q) (Q ∨ ¬P) R.
  intros n4_37a.
  MP n4_37a n4_31a.
  apply propositional_extensionality in n4_37a.
  replace ((Q ∨ ¬P) ∨ R) with 
      ((¬P ∨ Q) ∨ R) in n4_2a
      by now apply n4_37a.
  specialize n4_33 with (¬P) (¬P∨Q) R.
  intros n4_33c.
  apply propositional_extensionality in n4_33c.
  symmetry in n4_33c.
  replace (¬P ∨ (¬P ∨ Q) ∨ R) with 
      ((¬P ∨ (¬P ∨ Q)) ∨ R) in n4_2a
      by now apply n4_33c.
  specialize n4_33 with (¬P) (¬P) Q.
  intros n4_33d.
  apply propositional_extensionality in n4_33d.
  symmetry in n4_33d.
  replace (¬P ∨ ¬P ∨ Q) with 
      ((¬P ∨ ¬P) ∨ Q) in n4_2a
      by now apply n4_33d.
  specialize n4_33 with (¬P ∨ ¬P) Q R.
  intros n4_33e.
  apply propositional_extensionality in n4_33e.
  replace (((¬P ∨ ¬P) ∨ Q) ∨ R) with 
      ((¬P ∨ ¬P) ∨ Q ∨ R) in n4_2a
      by now apply n4_33e.
  specialize n4_25 with (¬P).
  intros n4_25a.
  specialize n4_37 with 
      (¬P) (¬P ∨ ¬P) (Q ∨ R).
  intros n4_37b.
  MP n4_37b n4_25a.
  apply propositional_extensionality in n4_25a.
  replace ((¬P ∨ ¬P) ∨ Q ∨ R) with 
      ((¬P) ∨ (Q ∨ R)) in n4_2a
      by now rewrite <- n4_25a.
  replace (¬P ∨ Q ∨ R) with 
      (P → (Q ∨ R)) in n4_2a
      by now rewrite Impl1_01.
  exact n4_2a.
Qed.

Theorem n4_79 : ∀ P Q R : Prop,
  ((Q → P) ∨ (R → P)) ↔ ((Q ∧ R) → P).
Proof. intros P Q R.
  specialize Transp4_1 with Q P.
  intros Transp4_1a.
  specialize Transp4_1 with R P.
  intros Transp4_1b.
  Conj Transp4_1a Transp4_1b Ca.
  specialize n4_39 with 
      (Q→P) (R→P) (¬P→¬Q) (¬P→¬R).
  intros n4_39a.
  MP n4_39a Ca.
  specialize n4_78 with (¬P) (¬Q) (¬R).
  intros n4_78a.
  rewrite Equiv4_01 in n4_78a.
  specialize Simp3_26 with 
    (((¬P→¬Q)∨(¬P→¬R))→(¬P→(¬Q∨¬R)))
    ((¬P→(¬Q∨¬R))→((¬P→¬Q)∨(¬P→¬R))).
  intros Simp3_26a.
  MP Simp3_26a n4_78a.
  specialize Transp2_15 with P (¬Q∨¬R).
  intros Transp2_15a.
  specialize Simp3_27 with 
    (((¬P→¬Q)∨(¬P→¬R))→(¬P→(¬Q∨¬R)))
    ((¬P→(¬Q∨¬R))→((¬P→¬Q)∨(¬P→¬R))).
  intros Simp3_27a.
  MP Simp3_27a n4_78a.
  specialize Transp2_15 with (¬Q∨¬R) P.
  intros Transp2_15b.
  specialize Syll2_06 with ((¬P→¬Q)∨(¬P→¬R))
    (¬P→(¬Q∨¬R)) (¬(¬Q∨¬R)→P).
  intros Syll2_06a.
  MP Syll2_06a Simp3_26a.
  MP Syll2_06a Transp2_15a.
  specialize Syll2_06 with (¬(¬Q∨¬R)→P)
    (¬P→(¬Q∨¬R)) ((¬P→¬Q)∨(¬P→¬R)).
  intros Syll2_06b.
  MP Syll2_06b Trans2_15b.
  MP Syll2_06b Simp3_27a.
  Conj Syll2_06a Syll2_06b Cb.
  Equiv Cb.
  clear Transp4_1a. clear Transp4_1b. clear Ca.
    clear Simp3_26a. clear Syll2_06b. clear n4_78a.
    clear Transp2_15a. clear Simp3_27a. 
    clear Transp2_15b. clear Syll2_06a.
  Conj n4_39a Cb Cc.
  specialize n4_22 with ((Q→P)∨(R→P))
    ((¬P→¬Q)∨(¬P→¬R)) (¬(¬Q∨¬R)→P).
  intros n4_22a.
  MP n4_22a Cc.
  specialize n4_2 with (¬(¬Q∨¬R)→P).
  intros n4_2a.
  Conj n4_22a n4_2a Cdd.
  specialize n4_22 with ((Q→P)∨(R→P))
  (¬(¬Q∨¬R)→P) (¬(¬Q∨¬R)→P).
  intros n4_22b.
  MP n4_22b Cdd.
  rewrite <- Prod3_01 in n4_22b.
  exact n4_22b.
Qed.

Theorem n4_8 : ∀ P : Prop,
  (P → ¬P) ↔ ¬P.
Proof. intros P.
  specialize Abs2_01 with P.
  intros Abs2_01a.
  specialize  Simp2_02 with P (¬P).
  intros Simp2_02a.
  Conj Abs2_01a Simp2_02a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_81 : ∀ P : Prop,
  (¬P → P) ↔ P.
Proof. intros P.
  specialize n2_18 with P.
  intros n2_18a.
  specialize  Simp2_02 with (¬P) P.
  intros Simp2_02a.
  Conj n2_18a Simp2_02a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_82 : ∀ P Q : Prop,
  ((P → Q) ∧ (P → ¬Q)) ↔ ¬P.
Proof. intros P Q. 
  specialize n2_65 with P Q.
  intros n2_65a.
  specialize Imp3_31 with (P→Q) (P→¬Q) (¬P).
  intros Imp3_31a.
  MP Imp3_31a n2_65a.
  specialize n2_21 with P Q.
  intros n2_21a.
  specialize n2_21 with P (¬Q).
  intros n2_21b.
  Conj n2_21a n2_21b Ca.
  specialize Comp3_43 with (¬P) (P→Q) (P→¬Q).
  intros Comp3_43a.
  MP Comp3_43a Ca.
  clear n2_65a. clear n2_21a. 
    clear n2_21b. clear Ca.
  Conj Imp3_31a Comp3_43a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_83 : ∀ P Q : Prop,
  ((P → Q) ∧ (¬P → Q)) ↔ Q.
Proof. intros P Q.
  specialize n2_61 with P Q.
  intros n2_61a.
  specialize Imp3_31 with (P→Q) (¬P→Q) (Q).
  intros Imp3_31a.
  MP Imp3_31a n2_61a.
  specialize Simp2_02 with P Q.
  intros Simp2_02a.
  specialize Simp2_02 with (¬P) Q.
  intros Simp2_02b.
  Conj Simp2_02a Simp2_02b Ca.
  specialize Comp3_43 with Q (P→Q) (¬P→Q).
  intros Comp3_43a.
  MP Comp3_43a H.
  clear n2_61a. clear Simp2_02a. 
  clear Simp2_02b. clear Ca.
  Conj Imp3_31a Comp3_43a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_84 : ∀ P Q R : Prop,
  (P ↔ Q) → ((P → R) ↔ (Q → R)).
Proof. intros P Q R.
  specialize Syll2_06 with P Q R.
  intros Syll2_06a.
  specialize Syll2_06 with Q P R.
  intros Syll2_06b.
  Conj Syll2_06a Syll2_06b Ca.
  specialize n3_47 with 
      (P→Q) (Q→P) ((Q→R)→P→R) ((P→R)→Q→R).
  intros n3_47a.
  MP n3_47a Ca.
  replace ((P→Q) ∧ (Q → P)) with (P↔Q) 
      in n3_47a by now rewrite Equiv4_01.
  replace (((Q→R)→P→R)∧((P→R)→Q→R)) with 
    ((Q→R)↔(P→R)) in n3_47a by 
    now rewrite Equiv4_01.
  specialize n4_21 with (P→R) (Q→R).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((Q → R) ↔ (P → R)) with 
      ((P→ R) ↔ (Q → R)) in n3_47a
      by now apply n4_21a.
  exact n3_47a.
Qed.

Theorem n4_85 : ∀ P Q R : Prop,
  (P ↔ Q) → ((R → P) ↔ (R → Q)).
Proof. intros P Q R.
  specialize Syll2_05 with R P Q.
  intros Syll2_05a.
  specialize Syll2_05 with R Q P.
  intros Syll2_05b.
  Conj Syll2_05a Syll2_05b Ca.
  specialize n3_47 with 
      (P→Q) (Q→P) ((R→P)→R→Q) ((R→Q)→R→P).
  intros n3_47a.
  MP n3_47a Ca.
  replace ((P→Q) ∧ (Q → P)) with (P↔Q) in n3_47a
  by now rewrite Equiv4_01.
  replace (((R→P)→R→Q)∧((R→Q)→R→P)) with 
    ((R→P)↔(R→Q)) in n3_47a 
    by now rewrite Equiv4_01.
  exact n3_47a.
Qed.

Theorem n4_86 : ∀ P Q R : Prop,
  (P ↔ Q) → ((P ↔ R) ↔ (Q ↔ R)). 
Proof. intros P Q R.
  specialize n4_22 with  Q P R.
  intros n4_22a.
  specialize Exp3_3 with (Q↔P) (P↔R) (Q↔R).
  intros Exp3_3a. (*Not cited*)
  MP Exp3_3a n4_22a.
  specialize n4_22 with  P Q R.
  intros n4_22b.
  specialize Exp3_3 with (P↔Q) (Q↔R) (P↔R).
  intros Exp3_3b.
  MP Exp3_3b n4_22b.
  specialize n4_21 with P Q.
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (Q↔P) with (P↔Q) in Exp3_3a
    by now apply n4_21a.
  clear n4_22a. clear n4_22b. clear n4_21a.
  Conj Exp3_3a Exp3_3b Ca.
  specialize Comp3_43 with (P↔Q)
      ((P↔R)→(Q↔R)) ((Q↔R)→(P↔R)).
  intros Comp3_43a. (*Not cited*)
  MP Comp3_43a Ca.
  replace (((P↔R)→(Q↔R))∧((Q↔R)→(P↔R)))
    with ((P↔R)↔(Q↔R)) in Comp3_43a 
    by now rewrite Equiv4_01.
  exact Comp3_43a.
Qed.

Theorem n4_87 : ∀ P Q R : Prop,
  (((P ∧ Q) → R) ↔ (P → Q → R)) ↔ 
      ((Q → (P → R)) ↔ (Q ∧ P → R)).
Proof. intros P Q R.
  specialize Exp3_3 with P Q R.
  intros Exp3_3a.
  specialize Imp3_31 with P Q R.
  intros Imp3_31a.
  Conj Exp3_3a Imp3_31a Ca.
  Equiv Ca.
  specialize Exp3_3 with Q P R.
  intros Exp3_3b.
  specialize Imp3_31 with Q P R.
  intros Imp3_31b.
  Conj Exp3_3b Imp3_31b Cb.
  Equiv Cb.
  specialize n4_21 with (Q→P→R) (Q∧P→R).
  intros n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((Q∧P→R)↔(Q→P→R)) with 
    ((Q→P→R)↔(Q∧P→R)) in Cb
    by now apply n4_21a.
  specialize Simp2_02 with ((P∧Q→R)↔(P→Q→R))
    ((Q→P→R)↔(Q∧P→R)).
  intros Simp2_02a.
  MP Simp2_02a Cb.
  specialize Simp2_02 with ((Q→P→R)↔(Q∧P→R)) 
    ((P∧Q→R)↔(P→Q→R)).
  intros Simp2_02b.
  MP Simp2_02b Ca.
  Conj Simp2_02a Simp2_02b Cc.
  Equiv Cc.
  exact Cc.
Qed.
(*The proof sketch cites Comm2_04. This 
  bit of the sketch was indecipherable.*)
