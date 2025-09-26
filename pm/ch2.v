Require Import PM.pm.lib.
Require Import PM.pm.ch1.

Import Unicode.Utf8.
Import Classical_Prop.
Import ClassicalFacts.
Import PropExtensionality.

(*We proceed to the deductions of of Principia.*)

Theorem Abs2_01 : ∀ P : Prop,
  (P → ¬P) → ¬P.
Proof. intros P.
  specialize Taut1_2 with (¬P).
  intros Taut1_2.
  replace (¬P ∨ ¬P) with (P → ¬P) in Taut1_2
    by now rewrite Impl1_01.
  exact Taut1_2.
Qed.

Theorem Simp2_02 : ∀ P Q : Prop, 
  Q → (P → Q).
Proof. intros P Q.
  specialize Add1_3 with (¬P) Q.
  intros Add1_3.
  replace (¬P ∨ Q) with (P → Q) in Add1_3
    by now rewrite Impl1_01.
  exact Add1_3.
Qed.

Theorem Transp2_03 : ∀ P Q : Prop,
  (P → ¬Q) → (Q → ¬P).
Proof. intros P Q.
  specialize Perm1_4 with (¬P) (¬Q).
  intros Perm1_4.
  replace (¬P ∨ ¬Q) with (P → ¬Q) in Perm1_4
    by now rewrite Impl1_01. 
  replace (¬Q ∨ ¬P) with (Q → ¬P) in Perm1_4
    by now rewrite Impl1_01.
  exact Perm1_4.
Qed.

Theorem Comm2_04 : ∀ P Q R : Prop,
  (P → (Q → R)) → (Q → (P → R)).
Proof. intros P Q R.
  specialize Assoc1_5 with (¬P) (¬Q) R.
  intros Assoc1_5.
  replace (¬Q ∨ R) with (Q → R) in Assoc1_5
    by now rewrite Impl1_01. 
  replace (¬P ∨ (Q → R)) with (P → (Q → R)) in Assoc1_5
    by now rewrite Impl1_01. 
  replace (¬P ∨ R) with (P → R) in Assoc1_5
    by now rewrite Impl1_01. 
  replace (¬Q ∨ (P → R)) with (Q → (P → R)) in Assoc1_5
    by now rewrite Impl1_01. 
  exact Assoc1_5.
Qed.

Theorem Syll2_05 : ∀ P Q R : Prop,
  (Q → R) → ((P  → Q) → (P → R)).
Proof. intros P Q R.
  specialize Sum1_6 with (¬P) Q R.
  intros Sum1_6.
  replace (¬P ∨ Q) with (P → Q) in Sum1_6
    by now rewrite Impl1_01.  
  replace (¬P ∨ R) with (P → R) in Sum1_6
    by now rewrite Impl1_01.
  exact Sum1_6.
Qed.

Theorem Syll2_06 : ∀ P Q R : Prop,
  (P → Q) → ((Q → R) → (P → R)).
Proof. intros P Q R. 
  specialize Comm2_04 with (Q → R) (P → Q) (P → R). 
  intros Comm2_04.
  specialize Syll2_05 with P Q R. 
  intros Syll2_05.
  MP Comm2_04 Syll2_05.
  exact Comm2_04.
Qed.

Theorem n2_07 : ∀ P : Prop,
  P → (P ∨ P).
Proof. intros P.
  specialize Add1_3 with P P.
  intros Add1_3.
  exact Add1_3.
Qed.

Theorem Id2_08 : ∀ P : Prop,
  P → P.
Proof. intros P.
  specialize Syll2_05 with P (P ∨ P) P. 
  intros Syll2_05.
  specialize Taut1_2 with P. 
  intros Taut1_2.
  MP Syll2_05 Taut1_2.
  specialize n2_07 with P.
  intros n2_07.
  MP Syll2_05 n2_07.
  exact Syll2_05.
Qed.

Theorem n2_1 : ∀ P : Prop,
  (¬P) ∨ P.
Proof. intros P.
  specialize Id2_08 with P. 
  intros Id2_08.
  replace (P → P) with (¬P ∨ P) in Id2_08
    by now rewrite Impl1_01. 
  exact Id2_08.
Qed.

Theorem n2_11 : ∀ P : Prop,
  P ∨ ¬P.
Proof. intros P.
  specialize Perm1_4 with (¬P) P. 
  intros Perm1_4.
  specialize n2_1 with P. 
  intros n2_1.
  MP Perm1_4 n2_1.
  exact Perm1_4.
Qed.

Theorem n2_12 : ∀ P : Prop,
  P → ¬¬P.
Proof. intros P.
  specialize n2_11 with (¬P). 
  intros n2_11.
  replace (¬P ∨ ¬¬P) with (P → ¬¬P) in n2_11
    by now rewrite Impl1_01.
  exact n2_11.
Qed.

Theorem n2_13 : ∀ P : Prop,
  P ∨ ¬¬¬P.
Proof. intros P.
  specialize Sum1_6 with P (¬P) (¬¬¬P). 
  intros Sum1_6.
  specialize n2_12 with (¬P). 
  intros n2_12.
  MP Sum1_6 n2_12.
  specialize n2_11 with P.
  intros n2_11.
  MP Sum1_6 n2_11.
  exact Sum1_6.
Qed.

Theorem n2_14 : ∀ P : Prop,
  ¬¬P → P.
Proof. intros P.
  specialize Perm1_4 with P (¬¬¬P). 
  intros Perm1_4.
  specialize n2_13 with P. 
  intros n2_13.
  MP Perm1_4 n2_13.
  replace (¬¬¬P ∨ P) with (¬¬P → P) in Perm1_4
    by now rewrite Impl1_01.
  exact Perm1_4.
Qed.

Theorem Transp2_15 : ∀ P Q : Prop,
  (¬P → Q) → (¬Q → P).
Proof. intros P Q.
  specialize Syll2_05 with (¬P) Q (¬¬Q). 
  intros Syll2_05a.
  specialize n2_12 with Q. 
  intros n2_12.
  MP Syll2_05a n2_12.
  specialize Transp2_03 with (¬P) (¬Q). 
  intros Transp2_03.
  specialize Syll2_05 with (¬Q) (¬¬P) P. 
  intros Syll2_05b.
  specialize n2_14 with P.
  intros n2_14.
  MP Syll2_05b n2_14.
  specialize Syll2_05 with (¬P → Q) (¬P → ¬¬Q) (¬Q → ¬¬P). 
  intros Syll2_05c.
  MP Syll2_05c Transp2_03.
  MP Syll2_05c Syll2_05a.
  specialize Syll2_05 with (¬P → Q) (¬Q → ¬¬P) (¬Q → P). 
  intros Syll2_05d.
  MP Syll2_05d Syll2_05b.
  MP Syll2_05d Syll2_05c.
  exact Syll2_05d.
Qed.

Ltac Syll H1 H2 S :=
  let S := fresh S in match goal with 
    | [ H1 : ?P → ?Q, H2 : ?Q → ?R |- _ ] =>
       assert (S : P → R) by (intros p; exact (H2 (H1 p)))
end. 

Theorem Transp2_16 : ∀ P Q : Prop,
  (P → Q) → (¬Q → ¬P).
Proof. intros P Q.
  specialize n2_12 with Q. 
  intros n2_12a.
  specialize Syll2_05 with P Q (¬¬Q). 
  intros Syll2_05a.
  specialize Transp2_03 with P (¬Q). 
  intros Transp2_03a.
  MP n2_12a Syll2_05a.
  Syll Syll2_05a Transp2_03a S.
  exact S.
Qed.

Theorem Transp2_17 : ∀ P Q : Prop,
  (¬Q → ¬P) → (P → Q).
Proof. intros P Q.
  specialize Transp2_03 with (¬Q) P. 
  intros Transp2_03a.
  specialize n2_14 with Q. 
  intros n2_14a.
  specialize Syll2_05 with P (¬¬Q) Q. 
  intros Syll2_05a.
  MP n2_14a Syll2_05a.
  Syll Transp2_03a Syll2_05a S.
  exact S.
Qed.

Theorem n2_18 : ∀ P : Prop,
  (¬P → P) → P.
Proof. intros P.
  specialize n2_12 with P.
  intro n2_12a.
  specialize Syll2_05 with (¬P) P (¬¬P). 
  intro Syll2_05a.
  MP Syll2_05a n2_12.
  specialize Abs2_01 with (¬P). 
  intros Abs2_01a.
  Syll Syll2_05a Abs2_01a Sa.
  specialize n2_14 with P. 
  intros n2_14a.
  Syll H n2_14a Sb.
  exact Sb.
Qed.

Theorem n2_2 : ∀ P Q : Prop,
  P → (P ∨ Q).
Proof. intros P Q.
  specialize Add1_3 with Q P. 
  intros Add1_3a.
  specialize Perm1_4 with Q P. 
  intros Perm1_4a.
  Syll Add1_3a Perm1_4a S.
  exact S.
Qed.

Theorem n2_21 : ∀ P Q : Prop,
  ¬P → (P → Q).
Proof. intros P Q.
  specialize n2_2 with (¬P) Q. 
  intros n2_2a.
  replace (¬P∨Q) with (P→Q) in n2_2a
    by now rewrite Impl1_01.
  exact n2_2a.
Qed.

Theorem n2_24 : ∀ P Q : Prop,
  P → (¬P → Q).
Proof. intros P Q.
  specialize n2_21 with P Q. 
  intros n2_21a.
  specialize Comm2_04 with (¬P) P Q. 
  intros Comm2_04a.
  MP Comm2_04a n2_21a.
  exact Comm2_04a.
Qed.

Theorem n2_25 : ∀ P Q : Prop,
  P ∨ ((P ∨ Q) → Q).
Proof. intros P Q.
  specialize n2_1 with (P ∨ Q).
  intros n2_1a.
  specialize Assoc1_5 with (¬(P∨Q)) P Q. 
  intros Assoc1_5a.
  MP Assoc1_5a n2_1a.
  replace (¬(P∨Q)∨Q) with (P∨Q→Q) in Assoc1_5a
    by now rewrite Impl1_01.
  exact Assoc1_5a.
Qed.

Theorem n2_26 : ∀ P Q : Prop,
  ¬P ∨ ((P → Q) → Q).
Proof. intros P Q.
  specialize n2_25 with (¬P) Q. 
  intros n2_25a.
  replace (¬P∨Q) with (P→Q) in n2_25a
    by now rewrite Impl1_01.
  exact n2_25a.
Qed.

Theorem n2_27 : ∀ P Q : Prop,
  P → ((P → Q) → Q).
Proof. intros P Q.
  specialize n2_26 with P Q. 
  intros n2_26a.
  replace (¬P∨((P→Q)→Q)) with (P→(P→Q)→Q) 
    in n2_26a by now rewrite Impl1_01. 
  exact n2_26a.
Qed.

Theorem n2_3 : ∀ P Q R : Prop,
  (P ∨ (Q ∨ R)) → (P ∨ (R ∨ Q)).
Proof. intros P Q R.
  specialize Perm1_4 with Q R. 
  intros Perm1_4a.
  specialize Sum1_6 with P (Q∨R) (R∨Q). 
  intros Sum1_6a.
  MP Sum1_6a Perm1_4a.
  exact Sum1_6a.
Qed.

Theorem n2_31 : ∀ P Q R : Prop,
  (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R).
Proof. intros P Q R.
  specialize n2_3 with P Q R. 
  intros n2_3a.
  specialize Assoc1_5 with P R Q. 
  intros Assoc1_5a.
  specialize Perm1_4 with R (P∨Q). 
  intros Perm1_4a.
  Syll Assoc1_5a Perm1_4a Sa.
  Syll n2_3a Sa Sb.
  exact Sb.
Qed.

Theorem n2_32 : ∀ P Q R : Prop,
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof. intros P Q R.
  specialize Perm1_4 with (P∨Q) R. 
  intros Perm1_4a.
  specialize Assoc1_5 with R P Q. 
  intros Assoc1_5a.
  specialize n2_3 with P R Q. 
  intros n2_3a.
  specialize Syll2_06 with ((P∨Q)∨R) (R∨P∨Q) (P∨R∨Q). 
  intros Syll2_06a.
  MP Syll2_06a Perm1_4a.
  MP Syll2_06a Assoc1_5a.
  specialize Syll2_06 with ((P∨Q)∨R) (P∨R∨Q) (P∨Q∨R). 
  intros Syll2_06b.
  MP Syll2_06b Syll2_06a.
  MP Syll2_06b n2_3a.
  exact Syll2_06b.
Qed.

(* Theorem Abb2_33 : ∀ P Q R : Prop,
  (P ∨ Q ∨ R) = ((P ∨ Q) ∨ R). 
Proof. intros P Q R. rewrite → n2_32. *)

Theorem Abb2_33 : ∀ P Q R : Prop,
  (P ∨ Q ∨ R) = ((P ∨ Q) ∨ R). 
Proof. intros P Q R.
  apply propositional_extensionality.
  split.
  specialize n2_31 with P Q R.
  intros n2_31.
  exact n2_31.
  specialize n2_32 with P Q R.
  intros n2_32.
  exact n2_32.
Qed.
  (*The default in Coq is right association.*)

Theorem n2_36 : ∀ P Q R : Prop,
  (Q → R) → ((P ∨ Q) → (R ∨ P)).
Proof. intros P Q R.
  specialize Perm1_4 with P R. 
  intros Perm1_4a.
  specialize Syll2_05 with (P∨Q) (P∨R) (R∨P). 
  intros Syll2_05a.
  MP Syll2_05a Perm1_4a.
  specialize Sum1_6 with P Q R. 
  intros Sum1_6a.
  Syll Sum1_6a Syll2_05a S.
  exact S.
Qed.

Theorem n2_37 : ∀ P Q R : Prop,
  (Q → R) → ((Q ∨ P) → (P ∨ R)).
Proof. intros P Q R.
  specialize Perm1_4 with Q P. 
  intros Perm1_4a.
  specialize Syll2_06 with (Q∨P) (P∨Q) (P∨R). 
  intros Syll2_06a.
  MP Syll2_06a Perm1_4a.
  specialize Sum1_6 with P Q R. 
  intros Sum1_6a.
  Syll Sum1_6a Syll2_06a S.
  exact S.
Qed.

Theorem n2_38 : ∀ P Q R : Prop,
  (Q → R) → ((Q ∨ P) → (R ∨ P)).
Proof. intros P Q R.
  specialize Perm1_4 with P R. 
  intros Perm1_4a.
  specialize Syll2_05 with (Q∨P) (P∨R) (R∨P). 
  intros Syll2_05a.
  MP Syll2_05a Perm1_4a.
  specialize Perm1_4 with Q P. 
  intros Perm1_4b.
  specialize Syll2_06 with (Q∨P) (P∨Q) (P∨R). 
  intros Syll2_06a.
  MP Syll2_06a Perm1_4b.
  Syll Syll2_06a Syll2_05a H.
  specialize Sum1_6 with P Q R. 
  intros Sum1_6a.
  Syll Sum1_6a H S.
  exact S.
Qed.

Theorem n2_4 : ∀ P Q : Prop,
  (P ∨ (P ∨ Q)) → (P ∨ Q).
Proof. intros P Q.
  specialize n2_31 with P P Q. 
  intros n2_31a.
  specialize Taut1_2 with P. 
  intros Taut1_2a.
  specialize n2_38 with Q (P∨P) P. 
  intros n2_38a.
  MP n2_38a Taut1_2a.
  Syll n2_31a n2_38a S.
  exact S.
Qed.

Theorem n2_41 : ∀ P Q : Prop,
  (Q ∨ (P ∨ Q)) → (P ∨ Q).
Proof. intros P Q.
  specialize Assoc1_5 with Q P Q. 
  intros Assoc1_5a.
  specialize Taut1_2 with Q. 
  intros Taut1_2a.
  specialize Sum1_6 with P (Q∨Q) Q. 
  intros Sum1_6a.
  MP Sum1_6a Taut1_2a.
  Syll Assoc1_5a Sum1_6a S.
  exact S.
Qed.

Theorem n2_42 : ∀ P Q : Prop,
  (¬P ∨ (P → Q)) → (P → Q).
Proof. intros P Q.
  specialize n2_4 with (¬P) Q. 
  intros n2_4a.
  replace (¬P∨Q) with (P→Q) in n2_4a
    by now rewrite Impl1_01.
  exact n2_4a. 
Qed.

Theorem n2_43 : ∀ P Q : Prop,
  (P → (P → Q)) → (P → Q).
Proof. intros P Q.
  specialize n2_42 with P Q. 
  intros n2_42a.
  replace (¬P ∨ (P→Q)) with (P→(P→Q)) 
    in n2_42a by now rewrite Impl1_01. 
  exact n2_42a. 
Qed.

Theorem n2_45 : ∀ P Q : Prop,
  ¬(P ∨ Q) → ¬P.
Proof. intros P Q.
  specialize n2_2 with P Q. 
  intros n2_2a.
  specialize Transp2_16 with P (P∨Q). 
  intros Transp2_16a.
  MP n2_2 Transp2_16a.
  exact Transp2_16a.
Qed.

Theorem n2_46 : ∀ P Q : Prop,
  ¬(P ∨ Q) → ¬Q.
Proof. intros P Q.
  specialize Add1_3 with P Q. 
  intros Add1_3a.
  specialize Transp2_16 with Q (P∨Q). 
  intros Transp2_16a.
  MP Add1_3a Transp2_16a.
  exact Transp2_16a.
Qed.

Theorem n2_47 : ∀ P Q : Prop,
  ¬(P ∨ Q) → (¬P ∨ Q).
Proof. intros P Q.
  specialize n2_45 with P Q. 
  intros n2_45a.
  specialize n2_2 with (¬P) Q. 
  intros n2_2a.
  Syll n2_45a n2_2a S.
  exact S.
Qed.

Theorem n2_48 : ∀ P Q : Prop,
  ¬(P ∨ Q) → (P ∨ ¬Q).
Proof. intros P Q.
  specialize n2_46 with P Q. 
  intros n2_46a.
  specialize Add1_3 with P (¬Q). 
  intros Add1_3a.
  Syll n2_46a Add1_3a S.
  exact S.
Qed.

Theorem n2_49 : ∀ P Q : Prop,
  ¬(P ∨ Q) → (¬P ∨ ¬Q).
Proof. intros P Q.
  specialize n2_45 with P Q. 
  intros n2_45a.
  specialize n2_2 with (¬P) (¬Q). 
  intros n2_2a.
  Syll n2_45a n2_2a S.
  exact S.
Qed.

Theorem n2_5 : ∀ P Q : Prop,
  ¬(P → Q) → (¬P → Q).
Proof. intros P Q.
  specialize n2_47 with (¬P) Q. 
  intros n2_47a.
  replace (¬P∨Q) with (P→Q) in n2_47a
    by now rewrite Impl1_01.
  replace (¬¬P∨Q) with (¬P→Q) in n2_47a
    by now rewrite Impl1_01.
  exact n2_47a.
Qed.

Theorem n2_51 : ∀ P Q : Prop,
  ¬(P → Q) → (P → ¬Q).
Proof. intros P Q.
  specialize n2_48 with (¬P) Q. 
  intros n2_48a.
  replace (¬P∨Q) with (P→Q) in n2_48a
    by now rewrite Impl1_01.
  replace (¬P∨¬Q) with (P→¬Q) in n2_48a
    by now rewrite Impl1_01.
  exact n2_48a.
Qed.

Theorem n2_52 : ∀ P Q : Prop,
  ¬(P → Q) → (¬P → ¬Q).
Proof. intros P Q.
  specialize n2_49 with (¬P) Q. 
  intros n2_49a.
  replace (¬P∨Q) with (P→Q) in n2_49a
   by now rewrite Impl1_01.
  replace (¬¬P∨¬Q) with (¬P→¬Q) in n2_49a
    by now rewrite Impl1_01.
  exact n2_49a.
Qed.

Theorem n2_521 : ∀ P Q : Prop,
  ¬(P→Q)→(Q→P).
Proof. intros P Q.
  specialize n2_52 with P Q. 
  intros n2_52a.
  specialize Transp2_17 with Q P. 
  intros Transp2_17a.
  Syll n2_52a Transp2_17a S.
  exact S.
Qed.

Theorem n2_53 : ∀ P Q : Prop,
  (P ∨ Q) → (¬P → Q).
Proof. intros P Q.
  specialize n2_12 with P. 
  intros n2_12a.
  specialize n2_38 with Q P (¬¬P). 
  intros n2_38a.
  MP n2_38a n2_12a.
  replace (¬¬P∨Q) with (¬P→Q) in n2_38a
    by now rewrite Impl1_01.
  exact n2_38a. 
Qed.

Theorem n2_54 : ∀ P Q : Prop,
  (¬P → Q) → (P ∨ Q).
Proof. intros P Q.
  specialize n2_14 with P. 
  intros n2_14a.
  specialize n2_38 with Q (¬¬P) P. 
  intros n2_38a.
  MP n2_38a n2_12a.
  replace (¬¬P∨Q) with (¬P→Q) in n2_38a
    by now rewrite Impl1_01.
  exact n2_38a. 
Qed.

Theorem n2_55 : ∀ P Q : Prop,
  ¬P → ((P ∨ Q) → Q).
Proof. intros P Q.
  specialize n2_53 with P Q.
  intros n2_53a.
  specialize Comm2_04 with (P∨Q) (¬P) Q. 
  intros Comm2_04a.
  MP n2_53a Comm2_04a.
  exact Comm2_04a.
Qed.

Theorem n2_56 : ∀ P Q : Prop,
  ¬Q → ((P ∨ Q) → P).
Proof. intros P Q.
  specialize n2_55 with Q P. 
  intros n2_55a.
  specialize Perm1_4 with P Q. 
  intros Perm1_4a.
  specialize Syll2_06 with (P∨Q) (Q∨P) P. 
  intros Syll2_06a.
  MP Syll2_06a Perm1_4a.
  Syll n2_55a Syll2_06a Sa.
  exact Sa.
Qed.

Theorem n2_6 : ∀ P Q : Prop,
  (¬P→Q) → ((P → Q) → Q).
Proof. intros P Q.
  specialize n2_38 with Q (¬P) Q. 
  intros n2_38a.
  specialize Taut1_2 with Q. 
  intros Taut1_2a.
  specialize Syll2_05 with (¬P∨Q) (Q∨Q) Q. 
  intros Syll2_05a.
  MP Syll2_05a Taut1_2a.
  Syll n2_38a Syll2_05a S.
  replace (¬P∨Q) with (P→Q) in S
    by now rewrite Impl1_01.
  exact S.
Qed.

Theorem n2_61 : ∀ P Q : Prop,
  (P → Q) → ((¬P → Q) → Q).
Proof. intros P Q.
  specialize n2_6 with P Q. 
  intros n2_6a.
  specialize Comm2_04 with (¬P→Q) (P→Q) Q. 
  intros Comm2_04a.
  MP Comm2_04a n2_6a.
  exact Comm2_04a.
Qed.

Theorem n2_62 : ∀ P Q : Prop,
  (P ∨ Q) → ((P → Q) → Q).
Proof. intros P Q.
  specialize n2_53 with P Q. 
  intros n2_53a.
  specialize n2_6 with P Q. 
  intros n2_6a.
  Syll n2_53a n2_6a S.
  exact S.
Qed.

Theorem n2_621 : ∀ P Q : Prop,
  (P → Q) → ((P ∨ Q) → Q).
Proof. intros P Q.
  specialize n2_62 with P Q. 
  intros n2_62a.
  specialize Comm2_04 with (P ∨ Q) (P→Q) Q. 
  intros Comm2_04a.
  MP Comm2_04a n2_62a. 
  exact Comm2_04a.
Qed.

Theorem n2_63 : ∀ P Q : Prop,
  (P ∨ Q) → ((¬P ∨ Q) → Q).
Proof. intros P Q.
  specialize n2_62 with P Q. 
  intros n2_62a.
  replace (P→Q) with (¬P∨Q) in n2_62a
    by now rewrite Impl1_01.
  exact n2_62a.
Qed.

Theorem n2_64 : ∀ P Q : Prop,
  (P ∨ Q) → ((P ∨ ¬Q) → P).
Proof. intros P Q.
  specialize n2_63 with Q P. 
  intros n2_63a.
  specialize Perm1_4 with P Q. 
  intros Perm1_4a.
  Syll n2_63a Perm1_4a Ha.
  specialize Syll2_06 with (P∨¬Q) (¬Q∨P) P.
  intros Syll2_06a.
  specialize Perm1_4 with P (¬Q).
  intros Perm1_4b.
  MP Syll2_06a Perm1_4b.
  Syll Syll2_06a Ha S.
  exact S.
Qed.

Theorem n2_65 : ∀ P Q : Prop,
  (P → Q) → ((P → ¬Q) → ¬P).
Proof. intros P Q.
  specialize n2_64 with (¬P) Q. 
  intros n2_64a.
  replace (¬P∨Q) with (P→Q) in n2_64a
    by now rewrite Impl1_01.
  replace (¬P∨¬Q) with (P→¬Q) in n2_64a
    by now rewrite Impl1_01.
  exact n2_64a.
Qed.

Theorem n2_67 : ∀ P Q : Prop,
  ((P ∨ Q) → Q) → (P → Q).
Proof. intros P Q.
  specialize n2_54 with P Q. 
  intros n2_54a.
  specialize Syll2_06 with (¬P→Q) (P∨Q) Q. 
  intros Syll2_06a.
  MP Syll2_06a n2_54a.
  specialize n2_24 with  P Q. 
  intros n2_24.
  specialize Syll2_06 with P (¬P→Q) Q. 
  intros Syll2_06b.
  MP Syll2_06b n2_24a.
  Syll Syll2_06b Syll2_06a S.
  exact S.
Qed.

Theorem n2_68 : ∀ P Q : Prop,
  ((P → Q) → Q) → (P ∨ Q).
Proof. intros P Q.
  specialize n2_67 with (¬P) Q. 
  intros n2_67a.
  replace (¬P∨Q) with (P→Q) in n2_67a
    by now rewrite Impl1_01.
  specialize n2_54 with P Q. 
  intros n2_54a.
  Syll n2_67a n2_54a S.
  exact S.
Qed.

Theorem n2_69 : ∀ P Q : Prop,
  ((P → Q) → Q) → ((Q → P) → P).
Proof. intros P Q.
  specialize n2_68 with P Q. 
  intros n2_68a.
  specialize Perm1_4 with P Q. 
  intros Perm1_4a.
  Syll n2_68a Perm1_4a Sa.
  specialize n2_62 with Q P. 
  intros n2_62a.
  Syll Sa n2_62a Sb.
  exact Sb.
Qed.

Theorem n2_73 : ∀ P Q R : Prop,
  (P → Q) → (((P ∨ Q) ∨ R) → (Q ∨ R)).
Proof. intros P Q R.
  specialize n2_621 with P Q. 
  intros n2_621a.
  specialize n2_38 with R (P∨Q) Q. 
  intros n2_38a.
  Syll n2_621a n2_38a S.
  exact S.
Qed.

Theorem n2_74 : ∀ P Q R : Prop,
  (Q → P) → ((P ∨ Q) ∨ R) → (P ∨ R).
Proof. intros P Q R.
  specialize n2_73 with Q P R. 
  intros n2_73a.
  specialize Assoc1_5 with P Q R. 
  intros Assoc1_5a.
  specialize n2_31 with Q P R. 
  intros n2_31a. (*not cited*)
  Syll Assoc1_5a n2_31a Sa. 
  specialize n2_32 with P Q R. 
  intros n2_32a. (*not cited*)
  Syll n2_32a Sa Sb.
  specialize Syll2_06 with ((P∨Q)∨R) ((Q∨P)∨R) (P∨R). 
  intros Syll2_06a.
  MP Syll2_06a Sb.
  Syll n2_73a Syll2_05a H.
  exact H.
Qed.

Theorem n2_75 : ∀ P Q R : Prop,
  (P ∨ Q) → ((P ∨ (Q → R)) → (P ∨ R)).
Proof. intros P Q R.
  specialize n2_74 with P (¬Q) R. 
  intros n2_74a.
  specialize n2_53 with Q P. 
  intros n2_53a.
  Syll n2_53a n2_74a Sa.
  specialize n2_31 with P (¬Q) R. 
  intros n2_31a.
  specialize Syll2_06 with (P∨(¬Q)∨R)((P∨(¬Q))∨R) (P∨R). 
  intros Syll2_06a.
  MP Syll2_06a n2_31a.
  Syll Sa Syll2_06a Sb.
  specialize Perm1_4 with P Q. 
  intros Perm1_4a. (*not cited*)
  Syll Perm1_4a Sb Sc.
  replace (¬Q∨R) with (Q→R) in Sc
    by now rewrite Impl1_01.
  exact Sc.
Qed.

Theorem n2_76 : ∀ P Q R : Prop,
  (P ∨ (Q → R)) → ((P ∨ Q) → (P ∨ R)).
Proof. intros P Q R.
  specialize n2_75 with P Q R. 
  intros n2_75a.
  specialize Comm2_04 with (P∨Q) (P∨(Q→R)) (P∨R). 
  intros Comm2_04a.
  MP Comm2_04a n2_75a.
  exact Comm2_04a. 
Qed.

Theorem n2_77 : ∀ P Q R : Prop,
  (P → (Q → R)) → ((P → Q) → (P → R)).
Proof. intros P Q R.
  specialize n2_76 with (¬P) Q R. 
  intros n2_76a.
  replace (¬P∨(Q→R)) with (P→Q→R) in n2_76a
    by now rewrite Impl1_01.
  replace (¬P∨Q) with (P→Q) in n2_76a
    by now rewrite Impl1_01.
  replace (¬P∨R) with (P→R) in n2_76a
    by now rewrite Impl1_01.
  exact n2_76a.
Qed.

Theorem n2_8 : ∀ Q R S : Prop,
  (Q ∨ R) → ((¬R ∨ S) → (Q ∨ S)).
Proof. intros Q R S.
  specialize n2_53 with R Q. 
  intros n2_53a.
  specialize Perm1_4 with Q R. 
  intros Perm1_4a.
  Syll Perm1_4a n2_53a Ha.
  specialize n2_38 with S (¬R) Q. 
  intros n2_38a.
  Syll H n2_38a Hb.
  exact Hb.
Qed.

Theorem n2_81 : ∀ P Q R S : Prop,
  (Q → (R → S)) → ((P ∨ Q) → ((P ∨ R) → (P ∨ S))).
Proof. intros P Q R S.
  specialize Sum1_6 with P Q (R→S). 
  intros Sum1_6a.
  specialize n2_76 with P R S. 
  intros n2_76a.
  specialize Syll2_05 with (P∨Q) (P∨(R→S)) ((P∨R)→(P∨S)). 
  intros Syll2_05a.
  MP Syll2_05a n2_76a.
  Syll Sum1_6a Syll2_05a H.
  exact H.
Qed.

Theorem n2_82 : ∀ P Q R S : Prop,
  (P ∨ Q ∨ R)→((P ∨ ¬R ∨ S)→(P ∨ Q ∨ S)).
Proof. intros P Q R S.
  specialize n2_8 with Q R S. 
  intros n2_8a.
  specialize n2_81 with P (Q∨R) (¬R∨S) (Q∨S). 
  intros n2_81a.
  MP n2_81a n2_8a.
  exact n2_81a.
Qed.

Theorem n2_83 : ∀ P Q R S : Prop,
  (P→(Q→R))→((P→(R→S))→(P→(Q→S))).
Proof. intros P Q R S.
  specialize n2_82 with (¬P) (¬Q) R S. 
  intros n2_82a.
  replace (¬Q∨R) with (Q→R) in n2_82a
    by now rewrite Impl1_01.
  replace (¬P∨(Q→R)) with (P→Q→R) in n2_82a
    by now rewrite Impl1_01.
  replace (¬R∨S) with (R→S) in n2_82a
    by now rewrite Impl1_01.
  replace (¬P∨(R→S)) with (P→R→S) in n2_82a
    by now rewrite Impl1_01.
  replace (¬Q∨S) with (Q→S) in n2_82a
    by now rewrite Impl1_01.
  replace (¬Q∨S) with (Q→S) in n2_82a
    by now rewrite Impl1_01.
  replace (¬P∨(Q→S)) with (P→Q→S) in n2_82a
    by now rewrite Impl1_01.
  exact n2_82a.
Qed.

Theorem n2_85 : ∀ P Q R : Prop,
  ((P ∨ Q) → (P ∨ R)) → (P ∨ (Q → R)).
Proof. intros P Q R.
  specialize Add1_3 with P Q. 
  intros Add1_3a.
  specialize Syll2_06 with Q (P∨Q) R. 
  intros Syll2_06a.
  MP Syll2_06a Add1_3a.
  specialize n2_55 with P R. 
  intros n2_55a.
  specialize Syll2_05 with (P∨Q) (P∨R) R. 
  intros Syll2_05a.
  Syll n2_55a Syll2_05a Ha.
  specialize n2_83 with (¬P) ((P∨Q)→(P∨R)) ((P∨Q)→R) (Q→R). 
  intros n2_83a.
  MP n2_83a Ha.
  specialize Comm2_04 with (¬P) (P∨Q→P∨R) (Q→R). 
  intros Comm2_04a.
  Syll Ha Comm2_04a Hb.
  specialize n2_54 with P (Q→R). 
  intros n2_54a.
  specialize Simp2_02 with (¬P) ((P∨Q→R)→(Q→R)). 
  intros Simp2_02a. (*Not cited*)
  (*Greg's suggestion per the BRS list on June 25, 2017.*)
  MP Syll2_06a Simp2_02a.
  MP Hb Simp2_02a.
  Syll Hb n2_54a Hc.
  exact Hc.
Qed.

Theorem n2_86 : ∀ P Q R : Prop,
  ((P → Q) → (P → R)) → (P → (Q →  R)).
Proof. intros P Q R.
  specialize n2_85 with (¬P) Q R. 
  intros n2_85a.
  replace (¬P∨Q) with (P→Q) in n2_85a
    by now rewrite Impl1_01.
  replace (¬P∨R) with (P→R) in n2_85a
    by now rewrite Impl1_01.
  replace (¬P∨(Q→R)) with (P→Q→R) in n2_85a
    by now rewrite Impl1_01.
  exact n2_85a.
Qed.

Axiom n9_01 : ∀ F : Prop → Prop,
  (¬(∀ x : Prop, F x)) = (∃ x : Prop, ¬ F x).

Axiom n9_02 : ∀ F : Prop → Prop,
  ¬(∃ x : Prop, F x) = (∀ x : Prop, ¬ F x).

Axiom n9_03 : ∀ F : Prop → Prop, ∀ P : Prop,
  ((∀ x : Prop, F x) ∨ P) = (∀ x : Prop, F x ∨ P).

Axiom n9_04 : ∀ F : Prop → Prop, ∀ P : Prop,
  (P ∨ (∀ x : Prop, F x)) = (∀ x : Prop, P ∨ F x).

Axiom n9_05 : ∀ (F : Prop → Prop) (P : Prop),
  ((∃ x : Prop, F x) ∨ P) = (∃ x : Prop, F x ∨ P).

Definition n9_06 (p : Prop) (Phi : Prop → Prop) : 
  (p ∨ (∃ x : Prop, Phi x)) = ∃ x : Prop, p ∨ Phi x. Admitted.

Theorem n9_07 : ∀ (Phi Psi : Prop → Prop),
  (∀ x : Prop, Phi x) \/ (∃ y : Prop, Psi y)
  = ∀ x : Prop, ∃ y : Prop, Phi x \/ Psi y.
Proof. Admitted.

Definition n9_08 (Phi Psi : Prop → Prop) :
  ((∃ y, Psi y) \/ (∀ x, Phi x)) = ∀ x, ∃ y, Psi y \/ Phi x. Admitted.

Definition n9_1 (Phi : Prop → Prop) (x : Prop) : 
  (Phi x → ∃ z : Prop, Phi z). Admitted.

Axiom n9_11 : ∀ x y : Prop, ∀ F : Prop → Prop, ((F x ∨ F y) → (∃z : Prop, F z)).

Axiom n9_13 : ∀ x : Prop, ∀ F : Prop → Prop, F x
  → (∀ y : Prop, F y).

Theorem n9_2 (y : Prop) : ∀ (Phi : Prop → Prop), (∀ x : Prop, Phi x) → Phi y.
Proof. intros.
  (** Step 1 **)
  specialize n2_1 with (Phi y). intros n2_1a.
  (** Step 2 **)
  specialize n9_1 with (fun x : Prop => ~ Phi x \/ Phi y) y. intros n9_1a.
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
difference between `z` and `forall z, z`. We will have to check how to express this
according to the original article
*)
Theorem n9_21 (Z : Prop) (Phi Psi : Prop → Prop) :
  (forall x, Phi x → Psi x) 
  → (forall y, Phi y) 
  → forall z, Psi z.
Proof.
  (** S1 **)
  pose proof (Id2_08 (Phi Z → Psi Z)) as S1.
  (** S2 **)
  assert (S2 : ∃ y : Prop, (Phi Z → Psi Z) → Phi y → Psi Z).
  {
    remember (fun x => (Phi Z → Psi Z) → Phi x → Psi Z) as f_S1 eqn:eqf_S1.
    pose (n9_1 f_S1 Z) as n9_1.
    rewrite → eqf_S1 in n9_1. rewrite → eqf_S1.
    exact (n9_1 S1).
  }
  (** S3 **)
  assert (S3 : ∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi Z).
  {
    remember (fun x => (∃ z0 : Prop, (Phi x → Psi x) → Phi z0 → Psi Z))
      as f_S2 eqn:eqf_S2.
    pose (n9_1 f_S2 Z) as n9_1.
    rewrite → eqf_S2 in n9_1. rewrite → eqf_S2.
    exact (n9_1 S2).
  }
  (** S4 **)
  assert (S4 : ∀ z : Prop, ∃ x y : Prop, (Phi x → Psi x) → Phi y → Psi z).
  {
    (* Unsatisfying. Not total forward reasoning. Still the only way works
      Maybe we can further assert the intermediate steps to produce better result
    *)
    intro z0.
    (* For each of the `exists` proposition, it just seems to be easier to firstly
    peel them off *)
    destruct S3 as [x S3_1]. exists x.
    destruct S3_1 as [y S3_2]. exists y.
    rewrite → Impl1_01. rewrite → Impl1_01 in S3_2.
    (* Coq reports "not covertible" for the following equivalent: *)
    (* remember (fun x' => (¬ (Phi x → Psi x)) ∨ (Phi y → Psi x')) as f_S3 eqn:eq_fS_3. *)
    (* We might use `rewrite`plus function equality for this case *)
    set (f_S3 := fun x' => (¬ (Phi x → Psi x)) ∨ (Phi y → Psi x')).
    change (¬ (Phi x → Psi x) ∨ (Phi y → Psi z0)) with (f_S3 z0).
    pose (n9_13 Z f_S3) as n9_13.
    exact (n9_13 S3_2 z0).
  }
  (** S5 **)
  assert (S5 : ∀ z : Prop, (∃ x : Prop, 
    (Phi x → Psi x) → (∃ y : Prop, Phi y → Psi z))).
  {
    assert (S4_i1 : ∀ z : Prop, ∃ x y : Prop, 
      ¬(Phi x → Psi x) \/ (Phi y → Psi z)).
    {
      intro z0. pose (S4 z0) as S4_1. 
      destruct S4_1 as [z1 S4_2]. exists z1.
      destruct S4_2 as [z2 S4_3]. exists z2.
      pose (n2_54 (¬ (Phi z1 → Psi z1)) (Phi z2 → Psi z0)) as n2_54.
      exact (n2_54 (fun x => S4_3 (n2_14 (Phi z1 → Psi z1) x))).
    }
    intro z0. pose (S4_i1 z0) as S4_i2.
    remember (fun y0 => Phi y0 → Psi z0) as f_S4 eqn:eqf_S4.
    destruct S4_i2 as [z1 S4_i3]. exists z1.
    pose (n9_06 (¬(Phi z1 → Psi z1)) f_S4) as n9_06.
    (* Peel down a level of `exists` *)
    destruct S4_i3 as [y1 S4_i4].
    (* TODO: try fun (P : Prop → Prop) => exists y, P y in the future *)
    pose (f_equal (fun (P : Prop → Prop) => P y1) eqf_S4) as eqf_S4_y1.
    rewrite <- eqf_S4_y1 in S4_i4.
    (* ...And wrap it back *)
    pose (ex_intro (fun y => ¬ (Phi z1 → Psi z1) ∨ f_S4 y) y1 S4_i4) as S4_i5.
    rewrite <- n9_06 in S4_i5.
    rewrite → eqf_S4 in S4_i5.
    pose (n2_53 (¬ (Phi z1 → Psi z1)) (∃ x : Prop, Phi x → Psi z0) S4_i5) as n2_53.
    pose (n2_12 (Phi z1 → Psi z1)) as n2_12.
    rewrite → eqf_S4.
    exact (fun y1 => n2_53 (n2_12 y1)).
  }
  assert (S6 : ((∃ x, ¬(Phi x → Psi x)) ∨ (∀ y, ∃ z, (¬ Phi z) ∨ Psi y))).
  {
    assert (S5_1 : ∀ z0 : Prop, ∃ x0 : Prop, 
      (~ (Phi x0 → Psi x0) \/ (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z0))
    ). 
    {
      intro z0. pose (S5 z0) as S5_i1.
      destruct S5_i1 as [z1 S5_i2]. exists z1.
      pose (Impl1_01 (Phi z1 → Psi z1) (∃ y : Prop, Phi y → Psi z0))
        as Impl1_01_1.
      rewrite → Impl1_01_1 in S5_i2.
      destruct S5_i2.
      { left. exact H. }
      { right.
        destruct H as [y H1]. exists y.
        pose (Impl1_01 (Phi y) (Psi z0)) as Impl_1_01_2.
        rewrite → Impl_1_01_2 in H1.
        exact H1. }
    }
    remember (fun x1 => ¬ (Phi x1 → Psi x1)) as f_S5_1 eqn:eqf_S5_1.
    remember (fun z1 => (∃ y0 : Prop, (¬ Phi y0) ∨ Psi z1)) as f_S5_2 eqn:eqf_S5_2.
    pose (n9_08 f_S5_2 f_S5_1) as n9_08.
    rewrite → eqf_S5_1.
    rewrite → eqf_S5_1 in n9_08.
    rewrite → eqf_S5_2 in n9_08.
    rewrite → n9_08.
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
    (* rewrite → eqf_S6_1 in S6. *)
    rewrite → n9_08. (* Alternatively, we can provide an exact instance for n9_08
    to form an exact equation, as comment above. But since 2 functions don't behave
    in the same way, this exact equation still needs some tunings *)
    rewrite → eqf_S6_1.
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
