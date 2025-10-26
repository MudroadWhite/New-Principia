# Project Architecture

## 1. What's under this project?
Currently, the project is divided into following parts:
- `./docs/` provides all necessary documentation for the proofs.
- `./Makefile` for building the project.
- `./pm/` being the actual show of this project. 

## 2. What's under `./pm`?
For each chapter in Principia, we have a corresponded `.v` file. If we can make it that far, we might further cluster the chapters with sections and parts.

Chapter 1 - 5, additionally with some sole proof pieces such as `Yuelin.v`, are directly inherited from [Landon's formalization of Principia](https://github.com/LogicalAtomist/principia).

In addition, we have a `lib.v` to provide experimental features or necessary tools for all chapters to use.

All conventions of sections below starts from chapter 9.

## 3. What's under a single `.v` file?
1. `Require Import` that cites other chapters and `lib.v`, so that you can use theorems and tools from these imported files.
2. Experimental feature `(* TYPE ANNOTATIONS *)` for manually check the allowed types of parameters in that chapter. Unfortunately, this does require manual checks and is not automated by the current (logic) model.
3. Occasional comments to explain what has been done here and there
4. `Notations` defined corresponded to the notations appeared in Principia. Each `Notation` comes with a `Scope`. To define a notation in a scope, we have to `Declare Scope`. To use the notation, we have to `Open Scope`. If we don't want the notation appear within proof, we command to `Close Scope`.
5. And eventually, everything left are the actual proofs, coming with `Definition`s and `Theorem`s.

## 4. What is `Definition` and `Theorem`?
As *vernacs* in the Rocq proof system, `Definition`s and `Theorem`s are being used, not because of their *literal meaning*, but because of their ability to nicely organize the data, just like a "class" or a "structure" in typical programming languages.

Rocq's `Definition`s are used to define *primitive propositions* and *definitions* in Principia. As the mechanic of `Definition` is interfering with the foundation of Principia, Principia's `Definition`s are immediately `Admitted` without providing any further proofs. Whether we should provide with proofs should be considered in the future.

Similarly, `Theorem`s are used to define *theorems* in Principia, and are intended to be proven and `Qed`ed.

Every `Definition` or `Theorem`, represents a proposition in Principia. They usually have both parameters on the left hand side of the `:`, plus a proposition that "has" parameters on the right hand side. But these parameters are different: *rhs* parameters are intended to be only filled through deductions, which will be mostly discussed in the [tactics](./3_tactics.md) chapter; and *lhs* parameters are the real ones to *set a proposition up*.

Say, if I have a parameter `P`, this parameter is supposed to be *instantiated* by a proposition. Principia's propositions come along with *types*, which is sadly much more refined than the `Prop` in `P : Prop`, and this is why these propositions' types require manual checking. We might only allow `P` to be instantiated by an elementary proposition; a first-order proposition, 2nd-order prop, etc.. If this project has been more mature, we might change `P : Prop` into something like `P : Elementary_Proposition` for a clearer distinction.

We have naming conventions for propositions. A proposition usually is named with `nxx_yyy`, with `xx_yyy` the number appeared in Principia for that proposition. A few of them are additionally come with their names in the text, and in that case we will adapt the `n` prefix to the name. For example, `Id2_08`. 

Now we come to naming conventions for (lhs) parameters.

Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.

Apparent variables are quantified variables in `forall`, `exists` and so on. As parameters, they're usually lower case literals like `x`.

Real variables are variables that can directly instantiate the proposition. They're usually upper case literals like `X`.

## 5. What's under a single proof?
If its correspondence in original text has separated the proof into several steps, rather than providing the related theorems for reference, we call this proposition is a "long proof". We don't enforce any architecture on short proofs.

For a long proof, it usually have thf following structure:
```Coq
Proof.
  (* TOOLS *)
  (* tools to set up... *)
  (* ******** *)
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

## 5.1 `TOOLS` section
- For every long proofs, if any tool is being used, a `TOOLS` section is **required** to be place at the beginning of the proof.

There are technical features that might require a setting up before they can be used, for example, introducing an extra real variable with the proof(with `set (X := Real "x")`), or prepare a modified version of a theorem for more convenient use. In this case, we set up these preparations in the `TOOLS` section.

## 5.2 `assert` the steps
- Every long proofs are **required** to adapt to the proof architecture specified below.

For long proofs, the first tactic we use always start with an `assert`. This tactic is used for specifying intermediate steps corresponded to ones in the original text. 

There are several reasons for organizing proofs with `assert`. The most significant one is readability. Besides, we can have several equivalant forms for a proposition, i.e. `(fun x => x) x` is not very far from just `x` or `(fun y => y) x`. Switching between them requires delicate application with tactics for all different cases. If we set the desired form as a subgoal, we only need to use tactics to prove for a equivalent form to `x`, and skip the tedious transformations. One last thing for `assert` is that it limits the scope of theorems we use. When we leave the scope, these theorems are automatically cleared away, and only the intermediate steps as `S1` `S2` are being pertained. As a result, the proof window becomes extremely clean.

- As it pertains a nice style, `exact` at the end of the proof is **not allowed** to be deleted or simplified.

By using `assert`, the propositions being asserted is introduced into the hypotheses.

## 6. What are the tactics we use for a single proof?

As introduced above, `assert` and `set`, sets up the general architecture to write the proof.

Beneath the architecture comes the details of how we prove a theorem. By referring to [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/), we can divide our tactics into 2 types.

`pose proof`, occasionally with `apply`, instantiates a existing theorem to use.

All other tactics are generally for rewriting to, and even a level down, deducing new propositions from existing propositions. This includes: `rewrite`, `setoid_rewrite`, also with custom defined Ltacs like `MP` `Syll` directly inherited from the [old repository](https://github.com/LogicalAtomist/principia).

[tactics](./3_tactics.md) goes into the details of these tactics.
