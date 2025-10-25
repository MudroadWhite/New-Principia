# Design on Theorems and Propositions

The conventions below starts from chapter 9.

TODO: 
- move `assert`'s introduction into this chapter
- rename this chapter to `architecture`
- cover the file architecture a little bit


## 1. `assert` for intermediate steps
When proofs are "long enough", the first tactic that one should see is `assert` to specify intermediate steps. This tactic modularizes the proofs so that they usually have the following structure:

```Coq
Proof.
  assert (S1 : x + y = z).
  {
    (* subproof for S1, where "S" here stands for step *)
  }
  assert (S2 : x + y = z → x + y = z).
  {
    (* subproof for S2 *)
  }
  (* and so on... *)
  exact Sn.
Qed.
```

There are several reasons for organizing proofs like this. The most significant one is readability. Besides, we can have several equivalant forms for a proposition, i.e. `(fun x => x) x` is not very far from just `x` or `(fun y => y) x`. Switching between them requires delicate application with tactics for all different cases. If we set the desired form as a subgoal, we only need to use tactics to prove for a equivalent form to `x`, and skip the tedious transformations. One last thing for `assert` is that it limits the scope of theorems we use. When we leave the scope, these theorems are automatically cleared away, and only the intermediate steps as `S1` `S2` are being pertained. As a result, the proof window becomes extremely clean.

- If the original proof has been broken down into several steps, it's Rocq formalization is **required** to apply the `assert` template above.
- As it pertains a nice style, `exact` at the end of the proof is **not allowed** to be deleted or simplified.

By using `assert`, the propositions being asserted is introduced into the hypotheses.

### `TOOLS`
Ever before the first `assert`, there might be a small `TOOLS` section in the very beginning of thr proof. These tools are for (...)
TODO: introduce the `TOOLS` section for real variables and `eq_to_equiv`

## Definitions and Theorems
`Definition`s and `Theorem`s are being used, not because of their *literal meaning*, but because of their ability to nicely organize the data, just like a "class" or a "structure" in typical programming languages.

Rocq's `Definition`s are used to define primitive propositions and "definitions" in Principia. As the `Definition` mechanic being interfering with the foundation for Principia, Principia's `Definition`s are immediately `Admitted` without any proofs. Whether we should provide definitions with proofs should be considered in the future.

Similarly, `Theorem`s are used to define theorems in Principia, and are intended to be proven and `Qed`ed.

## Naming convention: functions, apparent variables and real variables

TODO: state clearly what are parameters at lhs; for substitution vs for inference/deduction

Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.

By original text, apparent variables are quantified variables in `forall`, `exists` and so on. As parameters, they're usually lower case literals like `x`.

Real variables are variables directly introduced into the propositions. They're usually upper case literals like `X`. In `Theorem`s, they are stated at the left hand side of the definitions.

It sometimes happens though, even if the theorem itself doesn't involve any real variables, its proof needs to introduce some real variables. In that case, we use `set (X := Real "x")` to enable such usage during the proof. Theorem definitions are not supposed to suffix with real variables more than only the variables appeared in the definition.

## Tactics for proving theorems

There are 4 types of tactics we use.

The first type is `MP` in chapter 1, `Syll` in chapter 2, *occasionally* with other `Ltac`s defined in chapter 3-5, directly inherited from the [old repository](https://github.com/LogicalAtomist/principia). They expose the occurences where we need to perform specific ways to *deduce* the propositions.

The second type is `pose proof`. It instantiates a theorem to be use. Sole `pose` should be *strictly forbidden*, as `pose proof` simplifies the proof window with no tradeoffs.

To perform *substitutions* on the propositions, we have another class of tactic to use. Usually this is `rewrite`, but unfortunately sometimes it doesn't work - and only in this case should more complicated tactics be appeared, like `replace`, `change`, `setoid_rewrite`, etc..

And last, `assert` is being useful for organizing the proofs, and providing much better readability for all the intermediate steps.

`tactics.md` dives a deeper level down into how these tactics are being used.
