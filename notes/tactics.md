# Tactics

This chapter describes the tactics we generally use in further detail.

Technically speaking, Principia's logic system is very simple, maybe much more simpler than most of the modern type systems, cf. (SEP entry for Principia Mathematica)[https://plato.stanford.edu/entries/principia-mathematica/]. All it cares about is 1. deducing a theorem either directly or from Modus Ponens and 2. substitute/*rewrite* subparts of a proposition according to some rules. 

As a consequence, We don't need fancy tactics to formalize the theorems. We want the tactics to 1. follow the proof; 2. if the proof contains a tedious routine, simplify the proof without breaking the proof down. Since the following sections are roughly organized in "constructors" for each kind of propositions, within which we further add extra ways to simplify the proofs, it seems to be necessary to state beforehead, what do we concern for simplifications.

## 0. Rules to simplify routines
We can simplify a tedious rountine down, if
- The new tactic is general enough(why not) to apply the simplification
- We clearly identified the theorem used in original routine
- We clearly identified the types of parameters, for theorems in original routine. Parameters' types matters
- The tactic doesn't necessarily use theorems or parameters in its original routine - it just gets the work done

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

## 2. How to use(deduce on) a theorem
`pose proof (thm x y z) as thm` should be almost the only way to *introduce* a theorem into the hypotheses. Starting from chapter 9, propositions are further come with a special kind of "type", basically the order of the proposition, and at base case we're only allowed to use elementary propositions as parameters, for elementary functions. That being said,
- `pose proof` on a theorem is **allowed**.
- `pose` on a theorem is strictly **not allowed**.
- All parameters for the theorem at the *lhs* of its definition, are **required**.
- All parameters for the theorem are **required** to limit to the *lhs* of theorem's definition.
- All parameters for the theorem are **optional** to limited their "type" to elementary propositions, as the default in chapter 9. Every chapter after chapter 9 enables a new class of proposition to be passed in as parameters. Fundamentally however, whether they starts with a `∀` matters. Restriction on parameters is something our current formalization failed to model on.
- \[Simplification\]If a goal can be solved immediately, it is **allowed** to use `apply` to solve the goal immediately.

## 3. How to use a `→` proposition(rewrite)
A `→` proposition means that we can derive a conclusion from its premise. Immediately from above, below are almost the only allowed rules on `→` propositions:
- `MP p1 p2`, using the `MP` tactic, is **allowed**, where `p1` and `p2` are both propositions posed in the hypotheses. This is also how we treat "parameters" at the *rhs* of a theorem.
- `Syll p1 p2 Sy` for deriving a new "composed" proposition `Sy`, by using `Syll` tactic, is **allowed**. This is a tactic similar to `MP` and its exact meaning is given in chapter 2.

## 4. How to use a `↔` proposition(rewrite)
Technically speaking, if we completely follow the deduction rules in PM's logic system, we need to
1. Apply `Equiv` theorem to destruct `P ↔ Q` into `P → Q ∧ Q → P`
2. Use `Simp` to extract the direction that you want to use
3. Prove properties from the extracted theorem using `MP` or `Syll`
4. Optionally get the result as `R → S` and `S → R`
5. Apply `Conj`, `Equiv` sequencially to combine them into `R ↔ S`

It's straightforward that this routine is a lot just for a single step of deduction. To simplify the procedure, we're allowed to use `rewrite` directly on theorems made up of `↔`s, providing that we can always expand these `rewrite` into a sequence of `Simp`, `MP`, `Conj` and `Equiv`.
- \[Simplification\]`rewrite -> thm` on `↔` is **allowed**.
- \[Simplification\]`rewrite <- thm` on `↔` is **allowed**.
- \[Simplification\]Using `at` to specify the subterm is **allowed**, as it's original routine to get the subterm is straightforward. Beside using `at`, we can also provide the full parameter list for `thm` to `rewrite`.
- The `thm` for rewrite is **recommended** to provide its full parameter list.

Apart from the construction routine on `↔`, we also have destruction routine on `↔`. `Equiv` theorem in this sense, changes `P ↔ Q` back to `P → Q ∧ Q → P`. For this proposition, we can use `Simp` to choose the direction we want to use. But a more convinient way is seamlessly use the Rocq's `destruct` tactic.
- \[Simplification\]`destruct` on `↔` is **allowed**.
- \[Simplification\]If the routine is *destruct* a `↔` proposition to produce a branch to `MP` or `Syll` on, this `destruct` is **required** to be further simplified into a `rewrite` on `↔`.
- Otherwise, every `destruct`s are **required** to be immediately followed by a `clear` to select its branch.

Explicit examples, sometimes with comments, on reducing these routines with Rocq native tactics, are provided through chapter 9 & 10.

## 5. How to use a `=` proposition(rewrite)
Aka. the root of all evils. A clear way how `=` proposition interacts with other types of proposition is not clearly defined. On elementary propositions, Rocq's default preference `rewrite` works perfectly.
- `rewrite ->` on `=` is **allowed**.
- `rewrite <-` on `=` is **allowed**.
- Same as above, using `at` is **allowed**.
- Providing the parameter list is **recommended**.

But when things become complicated, more problems will come to surface. a `∀ x` is enough to bring `rewrite` down - it cannot identify the variable `x`. `setoid_rewrite` is a enhanced version of `rewrite` that can penetrate through `∀`s and `exist`s, with the only drawback that it works on `↔` relations. For this, we made the following rule:
- \[Simplification\]`=` propositions is **allowed** to be turned into `↔` propositions using `eq_to_equiv`
- \[Simplification\]`setoid_rewrite ->` on `↔` is **allowed**. Even for original `↔` theorems, this is a simplification.
- \[Simplification\]`setoid_rewrite <-` on `↔` is **allowed**.
- Similar to above, using `at` is **allowed**.
- \[Simplification\]`setoid_rewrite` on `=` is **allowed**, with `eq_to_equiv` set up on that proposition. If we need to derive the quantified version of a `=` proposition, this becomes a necessity.
- Providing the full parameter list is **recommended**

WARNING: thanks to the `rewrite` tactic in Rocq, `↔` is usually more useful than `→` theorems - a `rewrite` on `↔` is way simpler than `MP` or `Syll` on `→`. We might *slightly overuse* the `↔` theorems. There exists cases original proof `MP`s on its single-direction version, but for simplicity we still apply the `↔` version with a `rewrite` or `setoid_rewrite` on a proposition.

### 5.1. What routine does `setoid_rewrite` actually simplify?
It should be very worthwhile to discuss how we deal with rewriting for quantified ("∀ x") propositions, which also brings up the discussion on the viability for `setoid_rewrite` to simulate original proof. As we see, `setoid_rewrite` is only used in 2 situations: either the proposition is a `=`, or the proposition is a `↔`.

We first discuss the case for `↔`. As an opening, here is a question: how does a `∀` proposition appear? The basic idea for Principia is quite different from modern approach which uses a `∀` constructor. *Primitive propositions* in each chapter allow that
- If we have a proposition with the form of `φ X`, with `X` being a *real variable*,
- Then we can change `φ X` into `∀ x, φ x`. Here, `x` has become an *apparent variable* as it's in a `∀`.
If, say, we want to construct something like `(∀ x, φ x) → (∀ y, ψ y)`, then we further have some other rules to allow us to "split" the `∀` into half. `∀ x, φ x → ψ x` can even be turned into `(∃ x, φ x) → (∃ y, ψ y)`.

If we have a proposition having the form of `H : ∀ x, φ x`, and we only have a rewrite rule of `φ X ↔ ψ X`, we can 
1. Pick the rewrite rule `φ X ↔ ψ X` as our base
2. Use primitive propositions to change real variables into apparent variables. For example it will become `(∀ x, φ x) ↔ (∀ x, ψ x)`.
3. Now we can rewrite `H` as a whole into `∀ x, ψ x`.

As we can see, even without `setoid_rewrite`, "rewriting on quantified propositions" is always viable with a fixed routine and a fixed set of primitive propositions to perform, and this is what exactly we're trying to use `setoid_rewrite` to do.

For `=` case: how does `=` interact with others is mostly undefined. There doesn't exist a single *primitive proposition* in Principia explaining what does it do. We might either treat it as a `=` in Coq's type system. That means we're allowed to use whatever tactics just to perform the right substitution on a proposition. Or, as a common way, we can use `eq_to_equiv` or `apply propositional_extentionality` to change the `=` proposition into a `↔` one, but they are not a necessity. An exceptional case is when we want to lift a `P = Q` relation to `∀ x, P x = ∀ x, Q x`: we might use `f_equal` on generalization primitive propositions.

## 6. "Tools"
TODO: introduce the `TOOLS` section for real variables and `eq_to_equiv`

## 7. Rules for technical hacks 
Either for "historical reasons"(this project really doesn't have a history), or when we want to work thourgh a proof quickly, and we didn't figure out the correct way to write the proof, "technical hacks" arises for proof completions. The most common ones are listed below. Unless it gets a severe technical barrier, they are **recommended** to be taken down.
- \[Simplification\]`replace...with` is a valid and flexible substitution for rewriting, but it's too heavy. We should delete occurences of `replace...with` as much as possible.
- \[Simplification\]`apply propositional_extentionality` might occur inside `replace...with` blocks. Its purpose is to change the goal of `=` form into a goal of `↔` form for easier reasoning. It might work against original text and is not recommended.
- \[Simplification\]`intro` introduces the premise as a hypothesis. `intro Hp`, as utilized in chapter 5 & 10, has proven its harmlessness. Other from this usage directly sourced back to the text, it's not recommended to used. Their occurences are supposed to be eliminated.
- \[Simplification\]`now tactic thm ...` says that, if the `tactic` we use can directly provide a result that is not very far from the goal, then we prove the goal immediately. Typically it's very useful for saving a line of `exact thm`. Every line of `now tactic thm` can be turned back into `tactic thm` for readers to check if it does indeed generate a proposition that is exactly the same as the goal.

## 8. Bugged Ltacs
Throughout chapter 1 - 5, there are several custom tactics defined to use the primitive ideas conveniently. However, their current design is bugged: when we're trying to use them, they might not find the exact propositions that we are referring to. If things has went very bad, here is the full routine just for applying such a tactic:
1. `assert` a subgoal for the desired proposition
2. `clear` every unrelated hypotheses
3. `move` the propositions `before` or `after`, into the right order. For example, if we want to `MP S2 S1`, then we have to `move S1 after S2`.
4. perform the tactic and immediately conclude the subproof.
Since we don't always need to go through the full routine, we're only requiring that
- Tactics above are **allowed** to use, when they are the necessary preparations to perform a custom Ltac.

## 9. Debugging the proof
It happens that users might want to check the proofs in more detail. How to debug the proof is completely personal for completely personal purposes, but there are some tactics I commonly use:
- `simpl` to simplify a hypothesis
- `Close Scope`/`Open Scope` to enable specific notations
- `pose proof` another theorem to see how it looks like originally

