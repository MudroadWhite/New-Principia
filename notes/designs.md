# Design on Theorems and Propositions

## Definitions and Theorems
Definitions and theorems are being used, not because of their *literal meaning*, but because of their availability to nicely represent a proposition, just like a "class" or a "structure" in typical programming languages.

Definitions are used to define primitive propositions and "definitions" in Principia. As the `Definition` mechanic being interfering with the foundation for Principia, Principia's `Definition`s are immediately `Admitted` without any proofs. Whether we should provide definitions with proofs should be considered in the future.

Theorems are used to define theorems in Principia. You have to prove them and end with `Qed`s.

## Naming convention: functions, apparent variables and real variables

The convention below starts from chapter 9.

Functions are supposed to be named to keep in the same style with original text. They are either direct greek letters like `φ` or their upper-cased English equivalent like `Phi`.

By original text, apparent variables are quantified variables in `forall`, `exists` and so on. They're usually lower case literals like `x`.

Real variables are variables directly introduced into the propositions. They're usually upper case literals like `X`. In *theorems*, they are stated at the left hand side of the theorem's definition.

Extra real variables could occur in the theorem definitions, if there has been occurences for functions to be provided a variable, like `Phi x` without any quantifiers.

Orders of these variables are currently unspecified, and can be messy through the signatures.

## Proving theorems, by steps

TODO:
1. S1, S2, ...
2. assert
3. S1_i1, ...; S1_1, ...