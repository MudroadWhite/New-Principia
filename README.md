# New-Principia
Continuation of [Principia Mathematica's formalization](https://github.com/LogicalAtomist/principia) by Landon Elkind.

This project is currently focused on the following parts:
- [x] Chapter 9 - Theorems now extend beyond propositions with "real variables", involving functions and quantified propositions(with single "apparent variable"). Basic support for a predicate called "IsSameType".
- [x] Chapter 10 - Added a special notation for `->` and `<->` with single apparent variable. One theorem seems to be unprovable
- [ ] Chapter 11 - Notations for quantified propositions now extend to multiple apparent variables

## Why working on it
- Principia Mathematica has a stable version
- Coq doesn't need a lot of version updates
- Formalizing PM feels like climbing a mountain
- Formalized PM is a good education material for verifiers

## Features
This project aims towards demonstration and addresses compatability. Readers are supposed to be able to read the code line by line modulo technical hacks. Future contributers should find it easy to continue for better works while pertaining the style. 
- Forward style reasoning, keeping the most flavor of original Principia's proof
- Clear proof architecture and clean, maybe beautiful proof window
- No 3rd party library involved, and instead, minimal, native and simple tactics
- Detailed comment to the best I can

## Can you make sure that the code/proof is 100% correct?
No. Here are the reasons:
- Some of the concepts are so fundamental that either they involve a brand new architecture, or I just cannot represent them as code. As a result, there are theorems being commented out and only written in natural language.
- The design of `Ltac` isn't good(to be more exact, `match` doesn't work as one might think), so that even successful `Qed`s are nevertheless false positives. Actually, I have caught several bugs in the repo from this issue.
- The rigor of the proofs relies heavily on how refined your proofs are and how you interpret the original text.
- I didn't examine the code in chapter 1 - 5.

## Running the code
Coq version: 8.20.0, installed with the `opam` environment:

```bash
opam update
opam pin coq add 8.20.0
```
Running the project:

```bash
make
```

The `Makefile` for `make` is supposed to automatically detect all `.v` files under the `pm` folder, generate the `_CoqProject` file and compile the whole folder.

## Running the code, line by line
IDEs for Coq/Rocq varies, but here is my preference:

- WSL instance: Ubuntu 18.04 on WSL 2
- VS Code version: 1.80.0
- Extension installed locally: WSL
- Extension installed on WSL instance: VSCoq v0.3.7 from [OpenVSX](https://open-vsx.org/extension/maximedenes/vscoq).

## To contribute
Although I have tried to organize the issues well to indicate the current progress, I am not used to collaborate with others. It's suggested to raise an issue for inquiries, and I'll see what I can give.
