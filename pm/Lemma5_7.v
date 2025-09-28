Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.

Axiom equiv_comm : forall (P Q : Prop), (P <-> Q) = (Q <-> P).

Theorem L5_7 (P Q R S : Prop) :
  ((P↔Q) ∧ (R↔S)) → ((P↔R) → (Q↔S)).
Proof.
  pose (n4_22 Q P R) as n4_22a.
  pose (n4_22 Q R S) as n4_22b.
  pose (Exp3_3 (Q↔R) (R↔S) (Q↔S)) as Exp3_3a.
  MP Exp3_3a n4_22b.
  Syll n4_22a Exp3_3a Sa.
  replace (Q↔P) with (P↔Q) in Sa 
    by now apply (equiv_comm P Q).
  pose (Imp3_31 ((P↔Q)∧(P↔R)) (R↔S) (Q↔S)) as Imp3_31a.
  MP Imp3_31a Sa.
  replace (((P ↔ Q) ∧ (P ↔ R)) ∧ (R ↔ S)) with 
    ((P ↔ Q) ∧((P ↔ R) ∧ (R ↔ S))) in Imp3_31a.
  replace ((P ↔ R) ∧ (R ↔ S)) with 
    ((R ↔ S) ∧ (P ↔ R)) in Imp3_31a.
  replace ((P ↔ Q) ∧ (R ↔ S) ∧ (P ↔ R)) with 
    (((P ↔ Q) ∧ (R ↔ S)) ∧ (P ↔ R)) in Imp3_31a.
  pose (Exp3_3 ((P ↔ Q) ∧ (R ↔ S)) (P↔R) (Q↔S)) as Exp3_3b.
  MP Exp3_3b Imp3_31a.
  apply Exp3_3b.
  apply EqBi.
  apply n4_32. (*With (P ↔ Q) (R ↔ S) (P ↔ R)*)
  apply EqBi. 
  apply n4_3. (*With (R ↔ S) (P ↔ R)*)
  replace ((P ↔ Q) ∧((P ↔ R) ∧ (R ↔ S))) with 
    (((P ↔ Q) ∧ (P ↔ R)) ∧ (R ↔ S)).
  reflexivity.
  apply EqBi.
  specialize n4_32 with (P↔Q) (P↔R) (R↔S).
  intros n4_32a.
  apply n4_32a.
  apply EqBi.
  apply n4_21. (*With P Q*)
Qed.