# New-Principia
Continuation on [formalizing Principia Mathematica](https://github.com/LogicalAtomist/principia) by Landon Elkind.

This project is currently focused on the following parts:
- [x] Chapter 9 (optionally with "similar as above")
- [ ] Chapter 10 (optionally with "similar as above")

## Why working on it
- Principia Mathematica has a stable version
- Coq doesn't need a lot of version updates
- Formalizing PM feels like climbing a mountain
- Formalized PM is a good education material for verifiers

## Features
This project is for demonstration as well as compatability. Readers are supposed to read the code line by line besides technical hacks. Future contributers should find it easy to continue for better works while pertaining the style. 
- Forward style reasoning, pertaining the most flavor of original Principia's proof
- Clear proof architecture and clean, maybe beautiful proof window
- No 3rd party library involved, and instead, minimal, native and simple tactics
- Detailed comment to the best I can

## Can you make sure that the code/proof is 100% correct?
No. Here are the reasons:
- Some of the concepts are so fundamental that either it involves a brand new architecture, or I just cannot represent it as code. As a result, there are theorems being commented out and only written in natural language.
- The design of `Ltac` isn't good(to be more exact, `match` doesn't work as one might think), therefore you might end up with a successful `Qed` still with bad things happening under the hood. Actually, I have caught a bug in the repo from this issue.
- The rigor of the proofs relies heavily on how refined your proofs are and how you interpret the original text.

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

## To Contribute
Although I have tried to organize the issues well to indicate the current progress, I am not used to collaborate with others. It's suggested to raise an issue for inquiries, and I'll see what I can give.
