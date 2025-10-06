# Design on Theorems and Propositions

The conventions below starts from chapter 9.

## Definitions and Theorems
`Definition`s and `Theorem`s are being used, not because of their *literal meaning*, but because of their ability to nicely organize the data, just like a "class" or a "structure" in typical programming languages.

Rocq's `Definition`s are used to define primitive propositions and "definitions" in Principia. As the `Definition` mechanic being interfering with the foundation for Principia, Principia's `Definition`s are immediately `Admitted` without any proofs. Whether we should provide definitions with proofs should be considered in the future.

Similarly, `Theorem`s are used to define theorems in Principia, and are intended to be proven and `Qed`ed.

## Naming convention: functions, apparent variables and real variables

Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.

By original text, apparent variables are quantified variables in `forall`, `exists` and so on. As parameters, they're usually lower case literals like `x`.

Real variables are variables directly introduced into the propositions. They're usually upper case literals like `X`. In `Theorem`s, they are stated at the left hand side of the definitions.

It sometimes happens though, even if the theorem itself doesn't involve any real variables, its proof needs to introduce some real variables. In that case, we use `set (X := Real "x")` to enable such usage during the proof. Theorem definitions are not supposed to suffixed with real variables more than only the variables appeared in the definition.

## Tactics for proving theorems

There are 4 types of tactics we use.

The first type is `MP` in chapter 1. It exposes the occurences where we need to perform a modus ponens.

The second type is `pose proof`. It instantiates a theorem to be deducted.

The third type is `rewrite`, for implementing the substitutions in the formal system of Principia. Unfortunately sometimes it doesn't work - and only in this case should more complicated tactics be appeared, like `replace`, `change`, `setoid_rewrite`, etc..

And last, `assert` is being useful for organizing the proofs, and providing much better readability for all the intermediate steps.
