# New-Principia
Continuation on [formalizing Principia Mathematica](https://github.com/LogicalAtomist/principia) by Landon Elkind.

This project is planned to be limited to the following content:
- [x] Chapter 9 (optionally with "similar as above")
- [ ] Chapter 10 (optionally with "similar as above")

## Why working on it
- Principia Mathematica has a stable version
- Coq doesn't need a lot of version updates
- Formalizing PM feels like climbing a mountain

## Features
This project is for demonstration as well as compatability. Future contributers should find it easy to continue for better works while keeping the style. Readability for every line of code has been a great focus:
- Forward style reasoning, pertaining the most flavor of original Principia's proof
- Clear proof architecture and clean, maybe beautiful proof window
- No 3rd party library involved, and instead, minimal, native and simple tactics
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
