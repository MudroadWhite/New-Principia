# Functions, not defined

Typically in type system, or when we design a programming language syntax theoretically, we usually state the following very clearly:
1. When to introduce a function?
2. How to compute/eliminate a function?

Started from chapter 9, Principia doesn't have it defined how function works formally. It doesn't have axioms for introduction rule or elimination rule for functions. Function looks like just a simple substitution tool after all, so what can go wrong?

(TODO: add concrete example)

## Tactics being used
TLDR: We use a mixture of multiple tactics to implement a single functionality.

Although the tactics might not be appearing in the proofs, but these alternatives are what might help you while developing the proof when you don't have a single clue! 

1. Inlining the application. rather than directly define a function, we just apply a theorem with a function instance provided, like `n9_000 (fun x => x)`. Alternatively, the belows involves independently introducing a new function into the hypothesis:
2. `set` to define a function directly. Pairs with `change` when it needs a `rewrite`. Doesn't work very well on `exists` propositions and more generally bound variables. `change` tactic doesn't even modify the underlying proof object.
3. `remember` that generates a equation of `f = P x` to use. Will be blocked by `exists` proposition and more generally bound variables, but better than `set` in general.
4. `setoid_rewrite`. For every axioms defined in the form of `f = P x`, we need to change them into the form of `f <-> P x` with `pm.lib.eq_to_equiv`. After this tedious manual work, it seems to work very well to "penetrate" through quantifiers in most case.

## Destructing and constructing quantifiers
(TODO: rewrite this section)(If everything doesn't work, here is the final take:) In practice, the "best" way to just make the proof run is
1. Destruct the quantifier in the hypothesis and in the goal. `forall` is easy to break and make, while `exists` involves the constructor `existT`.
2. Define the function in the defined context
3. Either wrap back everything up to proceed, or match the goal `exact`ly

## Partial evaluation for theorems, for function rewrites
It happens sometimes in the proof where we don't `rewrite -> X` on any of the hypothesis, but instead directly `rewrite` on the goal. This is when I mean by "partially evaluate" the theorems. You might find `rewrite <- X in H` doesn't work, but `rewrite -> X; exact H` works.
