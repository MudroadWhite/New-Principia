(* PM.pm.lib - tools, libraries, and others to be used through the project *)

Require Import Unicode.Utf8.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import PropExtensionality.
Require Import String.

Export Unicode.Utf8.
Export Classical_Prop.
Export ClassicalFacts.
Export PropExtensionality.
Export String.

(* Experimental: A wrapper just to tag an real variable. This allows a freedom for creating them
throughout the proofs, as well as their easier identification *)
Definition Real (s : string) : Prop. Admitted.
Example var_0 := Real "x".
(* TODO: add an notation? *)

(* This is for `setoid_rewrite` only. Maybe in the future, we should rename this to
`make_equiv_for_setoid`. *)
Theorem eq_to_equiv : forall (P Q : Prop),
  (P = Q) -> (P <-> Q).
Proof.
  intros P Q H.
  split; try rewrite -> H; trivial.
Qed.
