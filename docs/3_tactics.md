# Tactics

This chapter describes the tactics we generally use in further detail.

Technically speaking, Principia's logic system is very simple, maybe much more simpler than most of the modern type systems, cf. [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/). All it cares about is 1. deducing a theorem either directly or from Modus Ponens and 2. substitute/*rewrite* subparts of a proposition according to some rules. 

As a consequence, We don't need fancy tactics to formalize the theorems. We want the tactics to 1. follow the proof; 2. if the proof contains a tedious routine, simplify the proof without breaking the proof down. Since the following sections are roughly organized by "constructors" for each kind of propositions, within which we further add extra ways to simplify the proofs, it seems to be necessary to state beforehead, what do we concern for simplifications.

## 0. Rules to simplify routines
We can use a new tactic to simplify a tedious part of proof down, if
- The tactic is general enough(why not) to apply the simplification
- We clearly identified the theorem used in original routine
- We clearly identified the types of parameters, for theorems in original routine. Parameters' types matters
- Optionally, the tactic doesn't necessarily use theorems or parameters in Principia - it just gets the work done

## 1. How to use(deduce on) a theorem
`pose proof (thm x y z) as thm` should be almost the only way to *introduce* a theorem into the hypotheses, stating the existence of an already proven result. Also, starting from chapter 9, propositions are further come with a special kind of "type", basically the order of the proposition, and at base case we're only allowed to use elementary propositions as parameters, for elementary functions. That being said,
- `pose proof` on a theorem is **allowed**.
- `pose` on a theorem is strictly **not allowed**, because `pose proof` gets the proof window cleaner.
- Provided parameters are **required** to all and only the ones at the *lhs* of the theorem.
- Provided parameters are **optional** to limit their "type"s to elementary proposition, as the default of chapter 9. Every chapter after chapter 9 enables a new class of proposition to be parameterized. Fundamentally however, whether they starts with a `∀` matters.
- \[Simplification\]If a goal can be solved immediately, `apply` is **allowed** to use.

## 2. How to use a `→` proposition(rewrite)
A `→` proposition means that we can derive a conclusion from its premise. Immediately from above, here are almost the only allowed rules on `→` propositions:
- `MP p1 p2`, using the `MP` tactic, is **allowed**, where `p1` and `p2` are both propositions posed in the hypotheses. This is also how we treat "parameters" at the *rhs* of a theorem.
- `Syll p1 p2 Sy` for deriving a new "composed" proposition `Sy`, by using `Syll` tactic, is **allowed**. This is a tactic similar to `MP` and its exact meaning is given in chapter 2.

## 3. How to use a `↔` proposition(rewrite)
Technically speaking, if we completely follow the deduction rules in PM's logic system, we need to
1. Apply `Equiv` theorem to destruct `P ↔ Q` into `P → Q ∧ Q → P`
2. Use `Simp` to extract the direction that you want to use
3. Prove properties from the extracted theorem using `MP` or `Syll`
4. Optionally get the result as `R → S` and `S → R`
5. Apply `Conj`, `Equiv` sequencially to combine them into `R ↔ S`

It's straightforward that this routine is a lot just for a single step of deduction. To simplify the procedure, we're allowed to use `rewrite` directly on theorems made up of `↔`s, providing that we can always expand these `rewrite` into a sequence of `Simp`, `MP`, `Conj` and `Equiv`.
- \[Simplification\]`rewrite -> thm` on `↔` is **allowed**.
- \[Simplification\]`rewrite <- thm` on `↔` is **allowed**.
- \[Simplification\]The `at` variant to specify the targeted subterm is **allowed**, as refining the subterm is a finite repetition of `MP`s and `Syll`s. Beside using `at`, we can also provide the full parameter list for `thm` to `rewrite`.
- The `thm` for rewrite is **recommended** to provide its full (lhs) parameter list.

Now that we finished discussing the construction routine on `↔`, we come to destruction routine on `↔`. `Equiv` theorem changes `P ↔ Q` back to `P → Q ∧ Q → P`. `Simp` picks the branch we want to use later, or we use both branch at different places. A more convenient way is seamlessly use Rocq's `destruct` tactic.
- \[Simplification\]`destruct` on `↔` is **allowed**.
- \[Simplification\]If the `destruct`ed `↔` proposition branch is used for further `MP` or `Syll` on, this `destruct` is **required** to be further simplified into a `rewrite` on `↔`.
- Unless both branches are being used, an immediate `clear` after the `destruct` is **required**.

Explicit examples and comments on these simplifications are occasionally provided through chapter 9 & 10.

## 4. How to use a `=` proposition(rewrite)
Aka. the root of all evils. A clear way how `=` proposition interacts with other types of proposition is not clearly defined(until chapter 13). For elementary propositions, Rocq's default preference `rewrite` works perfectly.
- `rewrite ->` on `=` is **allowed**.
- `rewrite <-` on `=` is **allowed**.
- Same as above, `at` variant is **allowed**.
- Providing the parameter list is **recommended**.

But when things become complicated, more problems will come to surface. A `∀ x` is enough to block the `rewrite` - it cannot identify the variable `x`. `setoid_rewrite` is an enhanced version of `rewrite` that can penetrate through `∀`s and `∃`s, with the drawback that it only works on `↔` relations. Hence the following rule:
- \[Simplification\]`eq_to_equiv` is **allowed** turn a `=` proposition into its `↔` equivalent. If we need to derive the quantified version of a `=` proposition, this becomes a necessity.
- \[Simplification\]`setoid_rewrite ->` on `↔` is **allowed**. Even if the `↔` doesn't come from `=`, this is a simplification.
- \[Simplification\]`setoid_rewrite <-` on `↔` is **allowed**.
- Similar to above, `at` variant for `setoid_rewrite` is **allowed**.
- Providing the full parameter list is **recommended**.

WARNING: Since `rewrite` is too convenient, even more than `MP` and `Syll`, `↔` theorems appear to be more useful than `→` theorems. In Rocq, we might *slightly overuse* `↔` theorems. Sometimes when a `→` theorem is enough to finish the proof, we might still choose a `↔` alternative and `rewrite` or `setoid_rewrite` with it.

### 4.1. What routine does `setoid_rewrite` actually simplify?
It should be very worthwhile to discuss how we deal with rewriting for quantified ("∀ x") propositions, which also brings up the discussion on the viability for `setoid_rewrite` to simplify original proof. As we see, `setoid_rewrite` is only used in 2 situations: either the proposition is a `=`, or the proposition is a `↔`.

We first discuss the case for `↔`. As an opening, here is a question: how does a `∀` proposition appear? The basic idea for Principia is quite different from modern approach which uses a `∀` constructor. *Primitive propositions* in each chapter allow that
- If we have a proposition with the form of `φ X`, where `X` is a *real variable*, then
- We can change `φ X` into `∀ x, φ x`. Here, `x` has become an *apparent variable* as it's in a `∀`.
If, say, we want to construct something like `(∀ x, φ x) → (∀ y, ψ y)`, then we are supposed to have some other rules to allow us to "split" the `∀` into half. `∀ x, φ x → ψ x` can even be turned into `(∃ x, φ x) → (∃ y, ψ y)`.

Having a proposition with the form of `H : ∀ x, φ x`, plus a rewrite rule of `φ X ↔ ψ X`, we can 
1. Pick the rewrite rule `φ X ↔ ψ X` as our base
2. Use primitive propositions to generalize the base. For example it will become `(∀ x, φ x) ↔ (∀ x, ψ x)`.
3. Since the generalized rewrite rule rewrites `H` as a whole, we can rewrite `H` into `∀ x, ψ x`.

As we can see, even without `setoid_rewrite`, "rewriting on quantified propositions" is always viable with a fixed routine and a fixed set of primitive propositions to perform, and this is what exactly we're trying to use `setoid_rewrite` to do.

For `=` case: As stated above, how does `=` interact with others is mostly undefined(till chapter 13). We might treat it as a `=` in Rocq's type system, which means we're allowed to use whatever tactics just to perform the right substitution on a proposition. Or, as a common way, we can use `eq_to_equiv` or `apply propositional_extentionality` to change the `=` proposition into a `↔` one, but they are not a necessity. An exceptional case is when we want to lift a `P = Q` relation to `∀ x, P x = ∀ x, Q x`: we might use `f_equal` on generalization-related primitive propositions.

## 5. Rules for technical hacks 
Either for "historical reasons"(this project really doesn't have a history), or when we want to work through a proof quickly, and we didn't figure out the correct way to write the proof, "technical hacks" arises for proof completions. The most common ones are listed below, but they might never appear in the proofs. This is because: unless there is a severe technical barrier, they are **recommended** to be taken down.
- \[Simplification\]`replace...with` is a valid and flexible substitution for rewriting, but it's too heavy.
- \[Simplification\]`apply propositional_extentionality` might occur inside `replace...with` blocks. Its purpose is to change the goal of `=` form into a goal of `↔` form for easier reasoning. It might work against original text.
- \[Simplification\]`intro` introduces the premise as a hypothesis. `intro Hp`, as utilized in chapter 5 & 10, has proven its harmlessness. Other from `intro Hp`, other occurrences should be eliminated.
- \[Simplification\]`now tactic thm ...` says that, if the `tactic` we use can directly provide a result that is not very far from the goal, then we prove the goal immediately. Typically it's very useful for saving a line of `exact thm`. Every line of `now tactic thm` can be turned back into `tactic thm` for readers to check if it does indeed generate a proposition that is exactly the same as the goal, and this tactic is **recommended** to use.

## 6. Bugged Ltacs
Throughout chapter 1 - 5, there are several custom tactics defined to use the primitive ideas conveniently. However, their current design is bugged: when we're trying to use them, they might not find the exact propositions that we are referring to. If things has went very bad, here is the full routine just for applying such a tactic:
1. `assert` a subgoal for the desired proposition
2. `clear` every unrelated hypotheses
3. `move` the propositions `before` or `after`, into the right order. For example, if we want to `MP S2 S1`, then we have to `move S1 after S2`.
4. perform the tactic and immediately conclude the subproof.
Since we don't always need to go through the full routine, we're only requiring that
- Tactics above are **allowed** to use, when they are the necessary preparations to perform a custom Ltac.

## 7. Debugging the proof
It happens that users might want to check the proofs in more detail. How to debug the proof is completely personal, but here are some tactics I commonly use, just in case:
- `simpl` to simplify a hypothesis
- `Close Scope`/`Open Scope` to enable specific notations
- `pose proof` another theorem to see how it looks like originally
