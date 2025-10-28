(* PM.pm.lib - tools, libraries, and others to be used through the project *)

Require Import Unicode.Utf8.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import PropExtensionality.
Require Import String.

Export Unicode.Utf8.
Export Classical_Prop.
Export ClassicalFacts.
Export PropExtensionality.
Export String.

(* cf.p.51: To instantiate variables appeared in a propositional function, we use 
the concept of "individual", designed as as wrapper just to tag an real variable. 
This allows easy identification on them and they are free to be created everywhere *)
Definition Individual (s : string) : Prop. Admitted.
Example var_0 := Individual "x".
(* TODO: add an notation? *)

(* cf.p.23: `=` propositions are allowed to be turned into `<->` propositions. An 
alternative tactic to this is `apply propositional_extensionality`. *)
Theorem eq_to_equiv : forall (P Q : Prop),
  (P = Q) -> (P <-> Q).
Proof.
  intros P Q H.
  split; try rewrite -> H; trivial.
Qed.

(* Experimental:
We might want to design an explicit `Asserted` and make notation as `[| |]`
to separate the parameters with the content inside
so that real variables doesn't pollute the `forall`s, `exists` at the rhs 
of the definition

`n9_13` in this way, will be written as
```
Definition n9_13 (Phi : Prop → Prop) (X : Prop) : 
  [| Phi X = (∀ y : Prop, Phi y) |]. 
Admitted.
```
which is significantly different and makes more sense over its original formation

Cons:
1. MP will be affected by this embedding
2. How do we perform all kinds of rewrites?
*)
Axiom Asserted : Prop -> Prop.

(* Draft, experimental: `^` support for a function/proposition, which works like a abstraction
Idea: 
Functions in Principia seems not to be a 1st class member. They are being abstracted from existing 
propositions with a operation `^` on these proposition's variables, even before these proposition
variables are being instantiated.

if we have a proposition `X /\ Y`, we can write something like
`^ X` on `X /\ Y` to abstract the proposition into a function, and also making 
it a function on `X`. p.15 of Principia says that we want `^X` on `X /\ Y` should 
be the same as `^Y` on `Y /\ X`. This is a different mechanics from the function system 
nowadays

In particular, `X` being hatted is still a variable being not instantiated, and determining
`X` is different from, and not the reversed procedure of hatting `X`.

Draft: 
  hat (P : Prop -> Prop) (X : Prop) :
    hat (P X) (X) = P
    where P has become the represesntation of a function
 *)

(* NOTE: 
~p.17:
- descriptive funstion is a special kind of propositional function, including examples like `x is blue`
- `~` is not a primitive idea. It is supposed to have a different definition on different types of proposition. 
For example, we might define `~` a typeclass, and `forall` propositions has an instance of implementation for 
this operator

~p.18:
apparent variable "appears to be" the only variables, while "real variables" include the actual variants to be concluded

~p.20: 
- (Ax, Px -> Q x) -> (Ax, Px) -> (Ax, Qx) requires that P Q takes arguments "of the same type". -> p.49
- formal implication are the `->` wrapped up in `forall`s. It bypassed the problem that `P -> Q = ~P \/ Q`, and restrict that we have to 
know `forall x, P x -> Q x` and `P X` to get `Q X`.

~p.22:
(TODO)`=` is not defined until chapter 13, and this is being explained in chapter 2/chapter II.

~p.40:
- a nice counterexample to test a function P is well typed is to see if `P P` can be formed
- `P P` is also an example that `P` is *impossible* to be a value of `P`
- P with "all possible values" are called `significant`. Significant = "well typed"

~p.47, beginning of chapter II:
- `forall x, Phi x` is considered as a function with `Phi` as one argument
- for `forall`, `Phi` can be a parameter but an individual `X` cannot be a parameter
- it is necesssary to make a distinction between passing in a `X` and passing in a `Phi`

~p.49:
- We can construct a function taking 2 arguments, and return either a function of function or a function of individual. 
It turns out that the return type is untyped. To enforce the return type with a fixed type, we have to enforce arguments
of a function taking the same type

~p.50:
- A propositional function could contain apparent variables
- We can eliminate apparent variables and source them back to real variables
- A function made up of no apparent variable is called a matrix, to generate a "matrix" of elementary propositions

~p.51:
- "Individual" is the best thing to instantiate a function's parameters
- (TODO)They are designed to be not propositions. Why?
- (TODO)Why we have to design the hierarchy for "functions" and "propositions " separately?
- Phi ! x has been explained. This notation has 2 variants in total, each case just to ensure its return type is fixed
- Name of the `!` notation is `predicate`
*)