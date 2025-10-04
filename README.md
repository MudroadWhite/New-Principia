# New-Principia
Continuation on [formalizing Principia Mathematica](https://github.com/LogicalAtomist/principia) by Landon Elkind.

Added: Chapter 9 except the `Proof as above` theorems

## Why working on it
- Principia Mathematica has a stable version
- Coq doesn't need a lot of version updates
- Formalizing PM feels like climbing a mountain

## Features
- Forward style reasoning, pertaining the most flavor of original proof
- Nice proof architecture and clean, maybe beautiful proof window
- No 3rd party library involved so far, and instead, native and simple tactics
- Detailed comment to the best I can

## Running the code
Coq version: 8.20.0, installed with the `opam` environment:

```bash
opam update
opam pin coq add 8.20.0
```
Running the project:

```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

For any new files for the project, don't forget to add their paths into the `_CoqProject`.
