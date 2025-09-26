# New-Principia
continuation on [formalizing Principia Mathematica](https://github.com/LogicalAtomist/principia)

## Why working on it
- Principia Mathematica has a stable version
- Formalizing PM feels like climbing a mountain
- Coq doesn't need a lot of version updates

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
