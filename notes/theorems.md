# Design on Theorems and Propositions

## Definitions and Theorems
`Definition`s and `Theorem`s are being used, not because of their *literal meaning*, but because of their ability to nicely organize the data, just like a "class" or a "structure" in typical programming languages.

Rocq's `Definition`s are used to define primitive propositions and "definitions" in Principia. As the `Definition` mechanic being interfering with the foundation for Principia, Principia's `Definition`s are immediately `Admitted` without any proofs. Whether we should provide definitions with proofs should be considered in the future.

Similarly, `Theorem`s are used to define theorems in Principia, and are intended to be proven and `Qed`ed.

## Naming convention: functions, apparent variables and real variables

The convention below starts from chapter 9.

Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.

By original text, apparent variables are quantified variables in `forall`, `exists` and so on. As parameters, they're usually lower case literals like `x`.

Real variables are variables directly introduced into the propositions. They're usually upper case literals like `X`. In `Theorem`s, they are stated at the left hand side of the definitions.

Extra real variables could occur in `Theorem` definitions, if original text has occurrences for functions to be provided a variable, like `φx` without any quantifiers.

Orders of these extra variables are currently unspecified, and can be messy through the signatures.

TODO: maybe there is a much clearer way to carefully distinguish between apparent and real variables

## Proving theorems, by steps

TODO:
1. S1, S2, ...
2. assert
3. S1_i1, ...; S1_1, ...
4. forward reasoning: avoid changing the goal as much as possible; use theorems in the original text