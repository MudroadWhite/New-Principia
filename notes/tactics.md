TODO: 

1. If theorem is a `->`, only `Syll` and `MP` should be used (refer to SEP)

2. If theorem is `=`, only `rewrite` should be used

3. If `rewrite` doesn't work, alternatives includes `replace`, `setoid_rewrite`, `apply propositional_extensionality` ...etc; see `functions,md` for more info

4. Ltacs are bugged: the only safe way to perform `Syll`, `Comp`, etc. is setting up a intermediate goal and clear irrevalent hypotheses

Alternatives to mere deductions and substitutions, and how they works

TODO: 
- state that the goal is to simplify the proof
- collect alternatives that replaced `Syll` and `MP`
- explain whether they are safe or not

1. `replace` can be a safe alternative for `Syll`s, (with examples)
2. `setoid_rewrite`
3. `apply propositional_extensionality`
4. slight `intro` (in chapter 9? in chapter 10?)
5. others to be gathered in chapter 9...