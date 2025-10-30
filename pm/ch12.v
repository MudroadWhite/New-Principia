Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch9.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.

(* 
Starting from chapter 12, every variables being quantified at the rhs has to be
either an "Individual" or a "Predicate". For example, "forall P, P /\ Q" might 
never appear, and instead, it will be either "forall Individual P, P /\ Q" or 
"forall Predicate Phi, Phi (Individual P)" where Phi P = P /\ Q
*)