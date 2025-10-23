# Tactics

This chapter describes the tactics we generally use in further detail.

## 1. `assert` for intermediate steps
When proofs are "long enough", the first tactic that should come to one's view should be `assert` to specify the intermediate steps. This tactic modularizes the proofs so that they usually have the following structure:

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

There are several reasons for organizing proofs like this. The most significant one is readability. Besides, we can have several equivalant forms for a proposition, i.e. `(fun x => x) x` is not very far from just `x` or `(fun y => y) x`. When we're using tactics to push on the proof, we might just get a result that is equivalent to `x`, but a further reorganization into `x` might be extremely tedious. By using `assert X` we're actually only require the proof ends at a proposition equivalent to `X`, and skip the tedious transformations into `X`. One last thing for `assert` is that it help us limit the scope of theorems we use. When we leave the scope, these theorems are automatically cleared away, and only the intermediate steps as `S1` `S2` are being pertained. As a result, the proof window becomes extremely clean.

- Proof for a theorem should be organized with `assert` with the template above.

By using `assert`, the propositions being asserted is introduced into the hypotheses.

## 2. What does it mean to use(deduce on) a theorem
`pose proof (thm x y z) as thm` should be almost the only way to *introduce* a theorem into the hypotheses. In Principia starting from chapter 9, propositions are further come with a special kind of "type", basically the order of the proposition, and at base case we're only allowed to use elementary propositions as parameters, for elementary functions. That being said,
- Whether the parameters of `thm` is a `forall` proposition *matters*. If no context is provided, theorems can only accept elementary propositions as parameters.
- `thm` cannot be applied to parameters more than the ones at lhs.
- Parameters at the rhs of the `thm` are supposed to be passed in via *modus ponens* rule.

## 3. How to use a `->` proposition(rewrite)
A `->` proposition means that we can derive a conclusion from its premise. Immediately from above, below are almost the only allowed form on `->` propositions:
- `MP p1 p2`, using the `MP` tactic, is allowed, where `p1` and `p2` are both propositions posed in the hypotheses.
- `Syll p1 p2 Sy` for deriving a new "composed" proposition `Sy`, by using `Syll` tactic, is allowed. This is a tactic similar to `MP` and its exact meaning is given in chapter 2.

## 4. How to use a `<->` proporition(rewrite)
Technically speaking, if we completely follow the deduction rules in PM's logic system, we need to
1. Apply `Equiv` rule to destruct `P <-> Q` into `P -> Q /\ Q -> P`
2. Use `Simp` to extract the direction that you want to use
3. Prove properties from the extracted theorem using `MP` or `Syll`
4. Optionally get the result as `R -> S` and `S -> R`
5. Apply `Conj`, `Equiv` sequencially to combine them into `R <-> S`

For just a single step on deduction, all the routine above seems pretty tedious. To simplify the procedure, we're allowed to use `rewrite` directly on theorems made up of `<->`s, providing that we can always expand these `rewrite` into a sequence of `Simp`, `MP`, `Conj` and `Equiv`.
- `rewrite -> thm` on `<->` is allowed
- `rewrite <- thm` on `<->` is allowed
- The `thm` for rewrite is recommended to provided its full parameter list, but can be omitted.

Some of the examples showing how they can be simplified, are provided through chapter 9 & 10.

## How to use a `=` proposition(rewrite)
Aka. the root of all evils. A clear way how `=` proposition interacts with other types of proposition is not clearly defined. By default, the best way to apply these propositions in Rocq is through `rewrite`.
- `rewrite ->` on `=` is allowed
- `rewrite <-` on `=` is allowed
- Same as above, providing the parameter list is optional

But when things become complicated, more problems will come to surface. `rewrite` only works on *elementary propositions*, and a `forall x` is enough to bring it down - it cannot identify the variable `x`. `setoid_rewrite` is a enhanced version of `rewrite` that can penetrate through `forall`s and `exist`s, with the only drawback that it works on `<->` relations. For this, we made the following rule:
- `=` propositions can be turned into `<->` propositions using `eq_to_equiv`
- `setoid_rewrite ->` on `<->` is allowed
- `setoid_rewrite <-` on `<->` is allowed
- Providing the parameter list is optional

## Rules for technical hacks 
Either for "historical reasons"(this project really doesn't have a history), or when we want to work thourgh a proof quickly, and we didn't figure out the correct way to write the proof, "technical hacks" arises for proof completions. The most common ones are listed below.
- `replace...with` is a valid and flexible substitution for rewriting, but it's too heavy. We should delete occurences of `replace...with` as much as possible.
- `apply propositional_extentionality` might occur inside `replace...with` blocks. Its purpose is to change the goal of `=` form into a goal of `<->` form for easier reasoning. It might work against original text and is not recommended.
- `intro` introduces the premise as a hypothesis. `intro Hp`, as utilized in chapter 5 & 10, has proven its harmlessness. Other from this usage directly sourced back to the text, it's not recommended to used. Their occurences are supposed to be eliminated.
- `now tactic thm ...` says that, if the `tactic` we use can directly provide a result that is not very far from the goal, then we prove the goal immediately. Typically it's very useful for saving a line of `exact thm`. Every line of `now tactic thm` can be turned back into `tactic thm` for readers to check if it does indeed generate a proposition that is exactly the same as the goal.

## Bugged Ltacs

TODO:
- Ltacs are bugged: the only safe way to perform `Syll`, `Comp`, etc. is setting up a intermediate goal and clear irrevalent hypotheses. Safely using `Conj`, `Syll`, and `MP` with `assert` and `clear`

Alternatives to mere deductions and substitutions, and how they works
