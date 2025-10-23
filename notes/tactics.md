# Tactics

This chapter describes the tactics we generally use in further detail.

Technically speaking, Principia's logic system is very simple, maybe much more simpler than most of the modern typs systems, cf. (SEP entry for Principia Mathematica)[https://plato.stanford.edu/entries/principia-mathematica/]. All it cares about is 1. deducing a theorem either directly or from Modus Ponens and 2. substitute/*rewrite* subparts of a proposition according to some rules. The tactics we use try to follow this flavor as much as possible while pertaining a reasonable level of simplicity.

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

There are several reasons for organizing proofs like this. The most significant one is readability. Besides, we can have several equivalant forms for a proposition, i.e. `(fun x => x) x` is not very far from just `x` or `(fun y => y) x`. Switching between them requires delicate application with tactics for all different cases. If we set the desired form as a subgoal, we only need to use tactics to prove for a equivalent form to `x`, and skip the tedious transformations. One last thing for `assert` is that it limits the scope of theorems we use. When we leave the scope, these theorems are automatically cleared away, and only the intermediate steps as `S1` `S2` are being pertained. As a result, the proof window becomes extremely clean.

- Proof for a theorem is **required** to be organized with `assert` with the template above.
- As it pertains a nice style, `exact` at the end of the proof is **not allowed** to be deleted or simplified.

By using `assert`, the propositions being asserted is introduced into the hypotheses.

## 2. How to use(deduce on) a theorem
`pose proof (thm x y z) as thm` should be almost the only way to *introduce* a theorem into the hypotheses. In Principia starting from chapter 9, propositions are further come with a special kind of "type", basically the order of the proposition, and at base case we're only allowed to use elementary propositions as parameters, for elementary functions. That being said,
- `pose proof` on a theorem is **allowed**.
- `pose` on a theorem is strictly **not allowed**.
- All parameters for the theorem at the *lhs* of its definition, are **required**.
- All parameters for the theorem are **required** to limit to the *lhs* of theorem's definition.
- All parameters for the theorem are **recommended**(a.k.a. optional) to limited their "type" to elementary propositions, as the default in chapter 9. Every chapter after chapter 9 enables a new class of proposition to be passed in as parameters. Fundamentally however, whether they starts with a `forall` matters. Restriction on parameters is something our current formalization failed to model on.
- If a goal can be solved immediately, it is **recommended** to just `apply` the theorem to end it.

## 3. How to use a `->` proposition(rewrite)
A `->` proposition means that we can derive a conclusion from its premise. Immediately from above, below are almost the only allowed rules on `->` propositions:
- `MP p1 p2`, using the `MP` tactic, is **allowed**, where `p1` and `p2` are both propositions posed in the hypotheses. This is also how we treat "parameters" at the *rhs* of a theorem.
- `Syll p1 p2 Sy` for deriving a new "composed" proposition `Sy`, by using `Syll` tactic, is **allowed**. This is a tactic similar to `MP` and its exact meaning is given in chapter 2.

## 4. How to use a `<->` proporition(rewrite)
Technically speaking, if we completely follow the deduction rules in PM's logic system, we need to
1. Apply `Equiv` rule to destruct `P <-> Q` into `P -> Q /\ Q -> P`
2. Use `Simp` to extract the direction that you want to use
3. Prove properties from the extracted theorem using `MP` or `Syll`
4. Optionally get the result as `R -> S` and `S -> R`
5. Apply `Conj`, `Equiv` sequencially to combine them into `R <-> S`

For just a single step on deduction, all the routine above seems pretty tedious. To simplify the procedure, we're allowed to use `rewrite` directly on theorems made up of `<->`s, providing that we can always expand these `rewrite` into a sequence of `Simp`, `MP`, `Conj` and `Equiv`.
- `rewrite -> thm` on `<->` is **allowed**.
- `rewrite <- thm` on `<->` is **allowed**.
- Using `at` to specify the subterm is **allowed**. Alternatively, we provide the full parameter list for `thm` to `rewrite`.
- The `thm` for rewrite is **recommended** to provide its full parameter list, but can be omitted.

Besides the construction procedure on `<->`, we also have destruction procedure on `<->`. `Equiv` theorem(not tactic) in this sense, changes `P <-> Q` back to `P -> Q /\ Q -> P`. For this proposition, we can use `Simp` to choose the direction we want to use. But a more convinient way is seamlessly use the Rocq's `destruct` tactic.
- `destruct` on `<->` is **allowed** to simplify this routine.

Explicit examples, sometimes with comments, on reducing these routines with Rocq native tactics, are provided through chapter 9 & 10.

## How to use a `=` proposition(rewrite)
Aka. the root of all evils. A clear way how `=` proposition interacts with other types of proposition is not clearly defined. On elementary propositions, Rocq's default preference `rewrite` works perfectly.
- `rewrite ->` on `=` is **allowed**
- `rewrite <-` on `=` is **allowed**
- Same as above, using `at` is **allowed**.
- Providing the parameter list is **recommended**.

But when things become complicated, more problems will come to surface. a `forall x` is enough to bring `rewrite` down - it cannot identify the variable `x`. `setoid_rewrite` is a enhanced version of `rewrite` that can penetrate through `forall`s and `exist`s, with the only drawback that it works on `<->` relations. For this, we made the following rule:
- `=` propositions is **allowed** to be turned into `<->` propositions using `eq_to_equiv`
- `setoid_rewrite ->` on `<->` is **allowed**
- `setoid_rewrite <-` on `<->` is **allowed**
- Similar to above, using `at` is **allowed**.
- Providing the full parameter list is **recommended**

WARNING: thanks to the `rewrite` tactic in Rocq, `<->` is usually more useful than `->` theorems - a `rewrite` on `<->` is way simpler than `MP` or `Syll` on `->`. We might *slightly overuse* the `<->` theorems. There exists cases original proof `MP`s on its single-direction version, but for simplicity we still apply the `<->` version with a `rewrite` or `setoid_rewrite` on a proposition.

## Rules for technical hacks 
Either for "historical reasons"(this project really doesn't have a history), or when we want to work thourgh a proof quickly, and we didn't figure out the correct way to write the proof, "technical hacks" arises for proof completions. The most common ones are listed below. Unless it gets a severe technical barrier, they are **recommended** to be taken down.
- `replace...with` is a valid and flexible substitution for rewriting, but it's too heavy. We should delete occurences of `replace...with` as much as possible.
- `apply propositional_extentionality` might occur inside `replace...with` blocks. Its purpose is to change the goal of `=` form into a goal of `<->` form for easier reasoning. It might work against original text and is not recommended.
- `intro` introduces the premise as a hypothesis. `intro Hp`, as utilized in chapter 5 & 10, has proven its harmlessness. Other from this usage directly sourced back to the text, it's not recommended to used. Their occurences are supposed to be eliminated.
- `now tactic thm ...` says that, if the `tactic` we use can directly provide a result that is not very far from the goal, then we prove the goal immediately. Typically it's very useful for saving a line of `exact thm`. Every line of `now tactic thm` can be turned back into `tactic thm` for readers to check if it does indeed generate a proposition that is exactly the same as the goal.

## Bugged Ltacs
Throughout chapter 1 - 5, there are several custom tactics defined to use the primitive ideas conveniently. However, their current design is bugged: when we're trying to use them, they might not find the exact propositions that we are referring to. If things has went very bad, here is the full routine just for applying such a tactic:
1. `assert` a subgoal for the desired proposition
2. `clear` every unrelated hypotheses
3. `move` the propositions `before` or `after`, into the right order. For example, if we want to `MP S2 S1`, then we have to `move S1 after S2`.
4. perform the tactic and immediately conclude the subproof.
Since we don't always need to go through the full routine, we're only requiring that
- Tactics above are **allowed** to use, when they are the necessary preparations to perform a custom Ltac.

## Debugging the proof
It happens that users might want to check the proofs in more detail. How to debug the proof is completely personal for completely personal purposes, but there are some tactics I commonly use:
- `simpl`s to simplify a hypothesis
- `Close Scope`/`Open Scope` to enable specific notations
