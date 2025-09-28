# Functions, not defined

Typically in type system, or when we design a programming language syntax theoretically, we usually state the following very clearly:
1. When to introduce a function?
2. How to compute/eliminate a function?

Started from chapter 9, Principia doesn't have it defined how function works formally. It doesn't have axioms for introduction rule or elimination rule for functions. Function looks like just a simple substitution tool after all, so what can go wrong?

Since I haven't figured out a unified way to do, here are some different methods that the proofs use to make the functions working.

1. `set` tactic to define a function directly. Pairs with `change` when it needs a `rewrite`. Doesn't work very well on `exists` propositions and more generally bound variables.
2. `remember` tactic that generates a equation of `f = P x` to use. Will be blocked by `exists` proposition and more generally bound variables, but better than `set` in general.
3. `setoid_rewrite`. For every axioms defined in the form of `f = P x`, we need to change them into the form of `f <-> P x`. After this tedious manual work, it seems to work very well to "penetrate" through all the quantifiers.

Without `setoid_rewrite`, for a function to be defined for quantifiers, I feel that equations and functions flavor locality, while rewritting flavors globality. We want the variables to be as global as you can to perform the rewrite, the best being the whole proposition. Equations and functions on the other hand, the smaller the better. In practice, the "best" way to just make the proof run is
1. Destruct the quantifier in the hypothesis and in the goal. `forall` is easy to break and make, while `exists` involves the constructor `existT`.
2. Define the function in the defined context
3. Either wrap back everything up to proceed, or match the goal `exact`ly
