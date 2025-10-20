# Tactics

This chapter describes the tactics we generally use in further detail.

## `assert` for intermediate steps
When proofs are "long enough", the first tactic that should come to one's view should be `assert` to specify the intermediate steps. This tactics modularizes the proofs so that they usually have the following structure:

```Coq
Proof.
  assert (S1 : x + y = z).
  {
    (* subproof for S1, where "S" here stands for step *)
  }
  assert (S2 : x + y = z -> x + y = z).
  {
    (* subproof for S2 *)
  }
  (* and so on... *)
  exact Sn.
Qed.
```

There are several reasons for organizing proofs like this. The most significant reason is readability. Besides, there might be cases where we have several equivalant forms to represent a proposition, i.e. `(fun x => x) x` is not very far from just `x` or `(fun y => y) x`. When we're using tactics to push on the proof, we might just get a result that is equivalent to `x`, but a further reorganization into `x` might be extremely tedious. One last thing for `assert` is that these subproofs help us limit the theorems to be within the step. When the subproofs have been proven, what you will see in the proof window is only the `S1` `S2` steps without those intermediate theorems being used, leaving the proof window extremely clean.

TODO:

1. If theorem is a `->`, only `Syll` and `MP` should be used (refer to SEP)

2. If theorem is `=`, only `rewrite` should be used

3. If `rewrite` doesn't work, alternatives includes `replace`, `setoid_rewrite`, `apply propositional_extensionality` ...etc; see `functions,md` for more info

4. Ltacs are bugged: the only safe way to perform `Syll`, `Comp`, etc. is setting up a intermediate goal and clear irrevalent hypotheses. Safely using `Conj`, `Syll`, and `MP` with `assert` and `clear`

Alternatives to mere deductions and substitutions, and how they works

TODO: 
- state that the goal is to simplify the proof
- collect alternatives that replaced `Syll` and `MP`
- explain whether they are safe or not

1. `replace` can be a safe alternative for `Syll`s, (with examples)
2. `setoid_rewrite`
3. `apply propositional_extensionality`
4. slight `intro` (in chapter 9? in chapter 10?)
5. others to be gathered in chapter 9...