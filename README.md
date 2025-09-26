# New-Principia
continuation on formalizing Principia Mathematica

## Why working on it
TODO

## Running the code

Coq version: 8.20.0, installed with the `opam` environment:

```bash
opam update
opam pin coq add 8.20.0
```

```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```
