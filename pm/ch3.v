Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.

Theorem Prod3_01 : ∀ P Q : Prop, 
  (P ∧ Q) = (¬(¬P ∨ ¬Q)).
Proof. intros P Q. 
  apply propositional_extensionality.
  split.
  specialize or_not_and with (P) (Q).
  intros or_not_and.
  specialize Transp2_03 with (¬P ∨ ¬Q) (P ∧ Q).
  intros Transp2_03.
  MP Transp2_03 or_not_and.
  exact Transp2_03.
  specialize not_and_or with (P) (Q).
  intros not_and_or.
  specialize Transp2_15 with (P ∧ Q) (¬P ∨ ¬Q).
  intros Transp2_15.
  MP Transp2_15 not_and_or.
  exact Transp2_15.
Qed.
(*This is a notational definition in Principia;
  it is used to switch between "∧" and "¬∨¬".*)

(*Axiom Abb3_02 : ∀ P Q R : Prop, 
  (P → Q → R) = ((P → Q) ∧ (Q → R)).*)
  (*Since Coq forbids such strings as ill-formed, or
  else automatically associates to the right,
  we leave this notational axiom commented out.*)

Theorem Conj3_03 : ∀ P Q : Prop, P → Q → (P∧Q). 
Proof. intros P Q.
  specialize n2_11 with (¬P∨¬Q). 
  intros n2_11a.
  specialize n2_32 with (¬P) (¬Q) (¬(¬P ∨ ¬Q)). 
  intros n2_32a.
  MP n2_32a n2_11a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_32a
    by now rewrite Prod3_01.
  replace (¬Q ∨ (P∧Q)) with (Q→(P∧Q)) in n2_32a
    by now rewrite Impl1_01.
  replace (¬P ∨ (Q → (P∧Q))) with (P→Q→(P∧Q)) in n2_32a
    by now rewrite Impl1_01.
  exact n2_32a.
Qed.
(*3.03 is permits the inference from the theoremhood 
    of P and that of Q to the theoremhood of P and Q. So:*)

Ltac Conj H1 H2 C :=
  let C := fresh C in match goal with 
    | [ H1 : ?P, H2 : ?Q |- _ ] =>  
      (specialize Conj3_03 with P Q;
      intros C;
      MP Conj3_03 P; MP Conj3_03 Q)
end. 

Theorem n3_1 : ∀ P Q : Prop,
  (P ∧ Q) → ¬(¬P ∨ ¬Q).
Proof. intros P Q.
  specialize Id2_08 with (P∧Q). 
  intros Id2_08a.
  replace ((P∧Q)→(P∧Q)) with ((P∧Q)→¬(¬P∨¬Q)) 
    in Id2_08a by now rewrite Prod3_01.
  exact Id2_08a.
Qed.

Theorem n3_11 : ∀ P Q : Prop,
  ¬(¬P ∨ ¬Q) → (P ∧ Q).
Proof. intros P Q.
  specialize Id2_08 with (P∧Q). 
  intros Id2_08a.
  replace ((P∧Q)→(P∧Q)) with (¬(¬P∨¬Q)→(P∧Q)) 
    in Id2_08a by now rewrite Prod3_01.
  exact Id2_08a.
Qed.

Theorem n3_12 : ∀ P Q : Prop,
  (¬P ∨ ¬Q) ∨ (P ∧ Q).
Proof. intros P Q.
  specialize n2_11 with (¬P∨¬Q). 
  intros n2_11a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_11a
    by now rewrite Prod3_01.
  exact n2_11a.
Qed.

Theorem n3_13 : ∀ P Q : Prop,
  ¬(P ∧ Q) → (¬P ∨ ¬Q).
Proof. intros P Q.
  specialize n3_11 with P Q. 
  intros n3_11a.
  specialize Transp2_15 with (¬P∨¬Q) (P∧Q). 
  intros Transp2_15a.
  MP Transp2_15a n3_11a.
  exact Transp2_15a.
Qed.

Theorem n3_14 : ∀ P Q : Prop,
  (¬P ∨ ¬Q) → ¬(P ∧ Q).
Proof. intros P Q.
  specialize n3_1 with P Q. 
  intros n3_1a.
  specialize Transp2_16 with (P∧Q) (¬(¬P∨¬Q)). 
  intros Transp2_16a.
  MP Transp2_16a n3_1a.
  specialize n2_12 with (¬P∨¬Q). 
  intros n2_12a.
  Syll n2_12a Transp2_16a S.
  exact S.
Qed.

Theorem n3_2 : ∀ P Q : Prop,
  P → Q → (P ∧ Q).
Proof. intros P Q.
  specialize n3_12 with P Q. 
  intros n3_12a.
  specialize n2_32 with (¬P) (¬Q) (P∧Q). 
  intros n2_32a.
  MP n3_32a n3_12a.
  replace (¬Q ∨ P ∧ Q) with (Q→P∧Q) in n2_32a
    by now rewrite Impl1_01.
  replace (¬P ∨ (Q → P ∧ Q)) with (P→Q→P∧Q) 
  in n2_32a by now rewrite Impl1_01.
  exact n2_32a.
Qed.

Theorem n3_21 : ∀ P Q : Prop,
  Q → P → (P ∧ Q).
Proof. intros P Q.
  specialize n3_2 with P Q.
  intros n3_2a.
  specialize Comm2_04 with P Q (P∧Q). 
  intros Comm2_04a.
  MP Comm2_04a n3_2a.
  exact Comm2_04a.
Qed.

Theorem n3_22 : ∀ P Q : Prop,
  (P ∧ Q) → (Q ∧ P).
Proof. intros P Q.
  specialize n3_13 with Q P. 
  intros n3_13a.
  specialize Perm1_4 with (¬Q) (¬P). 
  intros Perm1_4a.
  Syll n3_13a Perm1_4a Ha.
  specialize n3_14 with P Q. 
  intros n3_14a.
  Syll Ha n3_14a Hb.
  specialize Transp2_17 with (P∧Q) (Q ∧ P). 
  intros Transp2_17a.
  MP Transp2_17a Hb.
  exact Transp2_17a.
Qed.

Theorem n3_24 : ∀ P : Prop,
  ¬(P ∧ ¬P).
Proof. intros P.
  specialize n2_11 with (¬P). 
  intros n2_11a.
  specialize n3_14 with P (¬P). 
  intros n3_14a.
  MP n3_14a n2_11a.
  exact n3_14a.
Qed.

Theorem Simp3_26 : ∀ P Q : Prop,
  (P ∧ Q) → P.
Proof. intros P Q.
  specialize Simp2_02 with Q P. 
  intros Simp2_02a.
  replace (P→(Q→P)) with (¬P∨(Q→P)) in Simp2_02a
    by now rewrite <- Impl1_01.
  replace (Q→P) with (¬Q∨P) in Simp2_02a
    by now rewrite Impl1_01.
  specialize n2_31 with (¬P) (¬Q) P. 
  intros n2_31a.
  MP n2_31a Simp2_02a.
  specialize n2_53 with (¬P∨¬Q) P. 
  intros n2_53a.
  MP n2_53a Simp2_02a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_53a
    by now rewrite Prod3_01.
  exact n2_53a.
Qed.

Theorem Simp3_27 : ∀ P Q : Prop,
  (P ∧ Q) → Q.
Proof. intros P Q.
  specialize n3_22 with P Q. 
  intros n3_22a.
  specialize Simp3_26 with Q P. 
  intros Simp3_26a.
  Syll n3_22a Simp3_26a S.
  exact S.
Qed.

Theorem Exp3_3 : ∀ P Q R : Prop,
  ((P ∧ Q) → R) → (P → (Q → R)).
Proof. intros P Q R.
  specialize Id2_08 with ((P∧Q)→R).
  intros Id2_08a. (*This theorem isn't needed.*)
  replace (((P ∧ Q) → R) → ((P ∧ Q) → R)) with 
    (((P ∧ Q) → R) → (¬(¬P ∨ ¬Q) → R)) in Id2_08a
    by now rewrite Prod3_01.
  specialize Transp2_15 with (¬P∨¬Q) R. 
  intros Transp2_15a.
  Syll Id2_08a Transp2_15a Sa.
  specialize Id2_08 with (¬R → (¬P ∨ ¬Q)).
  intros Id2_08b. (*This theorem isn't needed.*)
  Syll Sa Id2_08b Sb.
  replace (¬P ∨ ¬Q) with (P → ¬Q) in Sb
    by now rewrite Impl1_01.
  specialize Comm2_04 with (¬R) P (¬Q). 
  intros Comm2_04a.
  Syll Sb Comm2_04a Sc.
  specialize Transp2_17 with Q R. 
  intros Transp2_17a.
  specialize Syll2_05 with P (¬R → ¬Q) (Q → R). 
  intros Syll2_05a.
  MP Syll2_05a Transp2_17a.
  Syll Sa Syll2_05a Sd.
  exact Sd.
Qed.

Theorem Imp3_31 : ∀ P Q R : Prop,
  (P → (Q → R)) → (P ∧ Q) → R.
Proof. intros P Q R.
  specialize Id2_08 with (P → (Q → R)).
  intros Id2_08a. 
  replace ((P → (Q → R))→(P → (Q → R))) with
    ((P → (Q → R))→(¬P ∨ (Q → R))) in Id2_08a
    by now rewrite <- Impl1_01.
  replace (¬P ∨ (Q → R)) with 
    (¬P ∨ (¬Q ∨ R)) in Id2_08a
    by now rewrite Impl1_01.
  specialize n2_31 with (¬P) (¬Q) R. 
  intros n2_31a.
  Syll Id2_08a n2_31a Sa.
  specialize n2_53 with (¬P∨¬Q) R. 
  intros n2_53a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_53a
    by now rewrite Prod3_01.
  Syll Sa n2_53a Sb.
  exact Sb.
Qed.

Theorem Syll3_33 : ∀ P Q R : Prop,
  ((P → Q) ∧ (Q → R)) → (P → R).
Proof. intros P Q R.
  specialize Syll2_06 with P Q R. 
  intros Syll2_06a.
  specialize Imp3_31 with (P→Q) (Q→R) (P→R). 
  intros Imp3_31a.
  MP Imp3_31a Syll2_06a.
  exact Imp3_31a.
Qed.

Theorem Syll3_34 : ∀ P Q R : Prop,
  ((Q → R) ∧ (P → Q)) → (P → R).
Proof. intros P Q R.
  specialize Syll2_05 with P Q R. 
  intros Syll2_05a.
  specialize Imp3_31 with (Q→R) (P→Q) (P→R).
  intros Imp3_31a.
  MP Imp3_31a Syll2_05a.
  exact Imp3_31a.
Qed.

Theorem Ass3_35 : ∀ P Q : Prop,
  (P ∧ (P → Q)) → Q.
Proof. intros P Q.
  specialize n2_27 with P Q. 
  intros n2_27a.
  specialize Imp3_31 with P (P→Q) Q. 
  intros Imp3_31a.
  MP Imp3_31a n2_27a.
  exact Imp3_31a.
Qed.

Theorem Transp3_37 : ∀ P Q R : Prop,
  (P ∧ Q → R) → (P ∧ ¬R → ¬Q).
Proof. intros P Q R.
  specialize Transp2_16 with Q R. 
  intros Transp2_16a.
  specialize Syll2_05 with P (Q→R) (¬R→¬Q). 
  intros Syll2_05a.
  MP Syll2_05a Transp2_16a.
  specialize Exp3_3 with P Q R. 
  intros Exp3_3a.
  Syll Exp3_3a Syll2_05a Sa.
  specialize Imp3_31 with P (¬R) (¬Q). 
  intros Imp3_31a.
  Syll Sa Imp3_31a Sb.
  exact Sb.
Qed.

Theorem n3_4 : ∀ P Q : Prop,
  (P ∧ Q) → P → Q.
Proof. intros P Q.
  specialize n2_51 with P Q. 
  intros n2_51a.
  specialize Transp2_15 with (P→Q) (P→¬Q). 
  intros Transp2_15a.
  MP Transp2_15a n2_51a.
  replace (P→¬Q) with (¬P∨¬Q) in Transp2_15a
    by now rewrite Impl1_01.
  replace (¬(¬P∨¬Q)) with (P∧Q) in Transp2_15a
    by now rewrite Prod3_01.
  exact Transp2_15a.
Qed.

Theorem n3_41 : ∀ P Q R : Prop,
  (P → R) → (P ∧ Q → R).
Proof. intros P Q R.
  specialize Simp3_26 with P Q. 
  intros Simp3_26a.
  specialize Syll2_06 with (P∧Q) P R. 
  intros Syll2_06a.
  MP Simp3_26a Syll2_06a.
  exact Syll2_06a.
Qed.

Theorem n3_42 : ∀ P Q R : Prop,
  (Q → R) → (P ∧ Q → R).
Proof. intros P Q R.
  specialize Simp3_27 with P Q. 
  intros Simp3_27a.
  specialize Syll2_06 with (P∧Q) Q R. 
  intros Syll2_06a.
  MP Syll2_06a Simp3_27a.
  exact Syll2_06a.
Qed.

Theorem Comp3_43 : ∀ P Q R : Prop,
  (P → Q) ∧ (P → R) → (P → Q ∧ R).
Proof. intros P Q R.
  specialize n3_2 with Q R. 
  intros n3_2a.
  specialize Syll2_05 with P Q (R→Q∧R). 
  intros Syll2_05a.
  MP Syll2_05a n3_2a.
  specialize n2_77 with P R (Q∧R). 
  intros n2_77a.
  Syll Syll2_05a n2_77a Sa.
  specialize Imp3_31 with (P→Q) (P→R) (P→Q∧R). 
  intros Imp3_31a.
  MP Sa Imp3_31a.
  exact Imp3_31a.
Qed.

Theorem n3_44 : ∀ P Q R : Prop,
  (Q → P) ∧ (R → P) → (Q ∨ R → P).
Proof. intros P Q R.
  specialize Syll3_33 with (¬Q) R P. 
  intros Syll3_33a.
  specialize n2_6 with Q P. 
  intros n2_6a.
  Syll Syll3_33a n2_6a Sa.
  specialize Exp3_3 with (¬Q→R) (R→P) ((Q→P)→P). 
  intros Exp3_3a.
  MP Exp3_3a Sa.
  specialize Comm2_04 with (R→P) (Q→P) P. 
  intros Comm2_04a.
  Syll Exp3_3a Comm2_04a Sb.
  specialize Imp3_31 with (Q→P) (R→P) P. 
  intros Imp3_31a.
  Syll Sb Imp3_31a Sc.
  specialize Comm2_04 with (¬Q→R) ((Q→P)∧(R→P)) P. 
  intros Comm2_04b.
  MP Comm2_04b Sc.
  specialize n2_53 with Q R. 
  intros n2_53a.
  specialize Syll2_06 with (Q∨R) (¬Q→R) P. 
  intros Syll2_06a.
  MP Syll2_06a n2_53a.
  Syll Comm2_04b Syll2_06a Sd.
  exact Sd.
Qed.

Theorem Fact3_45 : ∀ P Q R : Prop,
  (P → Q) → (P ∧ R) → (Q ∧ R).
Proof. intros P Q R.
  specialize Syll2_06 with P Q (¬R). 
  intros Syll2_06a.
  specialize Transp2_16 with (Q→¬R) (P→¬R). 
  intros Transp2_16a.
  Syll Syll2_06a Transp2_16a Sa.
  specialize Id2_08 with (¬(P→R)→¬(Q→¬R)).
  intros Id2_08a.
  Syll Sa Id2_08a Sb.
  replace (P→¬R) with (¬P∨¬R) in Sb
    by now rewrite Impl1_01.
  replace (Q→¬R) with (¬Q∨¬R) in Sb
    by now rewrite Impl1_01.
  replace (¬(¬P∨¬R)) with (P∧R) in Sb
    by now rewrite Prod3_01.
  replace (¬(¬Q∨¬R)) with (Q∧R) in Sb
    by now rewrite Prod3_01.
  exact Sb.
Qed.

Theorem n3_47 : ∀ P Q R S : Prop,
  ((P → R) ∧ (Q → S)) → (P ∧ Q) → R ∧ S.
Proof. intros P Q R S.
  specialize Simp3_26 with (P→R) (Q→S). 
  intros Simp3_26a.
  specialize Fact3_45 with P R Q. 
  intros Fact3_45a.
  Syll Simp3_26a Fact3_45a Sa.
  specialize n3_22 with R Q. 
  intros n3_22a.
  specialize Syll2_05 with (P∧Q) (R∧Q) (Q∧R). 
  intros Syll2_05a.
  MP Syll2_05a n3_22a.
  Syll Sa Syll2_05a Sb.
  specialize Simp3_27 with (P→R) (Q→S).
  intros Simp3_27a.
  specialize Fact3_45 with Q S R. 
  intros Fact3_45b.
  Syll Simp3_27a Fact3_45b Sc.
  specialize n3_22 with S R. 
  intros n3_22b.
  specialize Syll2_05 with (Q∧R) (S∧R) (R∧S). 
  intros Syll2_05b.
  MP Syll2_05b n3_22b.
  Syll Sc Syll2_05b Sd.
  clear Simp3_26a. clear Fact3_45a. clear Sa. 
    clear n3_22a. clear Fact3_45b. 
    clear Syll2_05a. clear Simp3_27a.
    clear Sc. clear n3_22b. clear Syll2_05b.
  Conj Sb Sd C.
  specialize n2_83 with ((P→R)∧(Q→S)) (P∧Q) (Q∧R) (R∧S).
  intros n2_83a. (*This with MP works, but it omits Conj3_03.*)
  specialize Imp3_31 with (((P→R)∧(Q→S))→((P∧Q)→(Q∧R)))
    (((P→R)∧(Q→S))→((Q∧R)→(R∧S))) 
    (((P→R)∧(Q→S))→((P∧Q)→(R∧S))).
  intros Imp3_31a.
  MP Imp3_31a n2_83a.
  MP Imp3_31a C.
  exact Imp3_31a.
Qed.

Theorem n3_48 : ∀ P Q R S : Prop,
  ((P → R) ∧ (Q → S)) → (P ∨ Q) → R ∨ S.
Proof. intros P Q R S.
  specialize Simp3_26 with (P→R) (Q→S). 
  intros Simp3_26a.
  specialize Sum1_6 with Q P R. 
  intros Sum1_6a.
  Syll Simp3_26a Sum1_6a Sa.
  specialize Perm1_4 with P Q. 
  intros Perm1_4a.
  specialize Syll2_06 with (P∨Q) (Q∨P) (Q∨R). 
  intros Syll2_06a.
  MP Syll2_06a Perm1_4a.
  Syll Sa Syll2_06a Sb.
  specialize Simp3_27 with (P→R) (Q→S). 
  intros Simp3_27a.
  specialize Sum1_6 with R Q S. 
  intros Sum1_6b.
  Syll Simp3_27a Sum1_6b Sc.
  specialize Perm1_4 with Q R. 
  intros Perm1_4b.
  specialize Syll2_06 with (Q∨R) (R∨Q) (R∨S). 
  intros Syll2_06b.
  MP Syll2_06b Perm1_4b.
  Syll Sc Syll2_06a Sd.
  specialize n2_83 with ((P→R)∧(Q→S)) (P∨Q) (Q∨R) (R∨S). 
  intros n2_83a.
  MP n2_83a Sb.
  MP n2_83a Sd.
  exact n2_83a. 
Qed.