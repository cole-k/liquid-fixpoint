# Rewrite Set/Bag sort annotations on bound variables in `elabFSetBagZ3`

## Summary

`elabFSetBagZ3` (in `Language.Fixpoint.SortCheck`) rewrites `Set_*`/`Bag_*`
operators to their array-based encodings (`arr_*`) when elaborating
expressions for Z3. However, it did **not** rewrite the sort annotations
attached to binders introduced by `ELam`, `PAll`, `PExist`, or explicit
`ECst` casts. This patch extends `elabFSetBagZ3` to rewrite those sort
annotations as well, mapping:

- `(Set_Set t)` → `(Array_t t bool)`
- `(Bag_t  t)` → `(Array_t t int)`

inside any `Sort` reachable from a binder.

## Why this matters

Consider an expression like

```
exists ((x (Set_Set int))) . (Set_cup x y) = z
```

After `elabFSetBagZ3` (pre-patch), the body becomes

```
exists ((x (Set_Set int))) . (arr_map_or x y) = z
```

`arr_map_or` has signature `forall a. (Array_t a bool) -> (Array_t a bool) -> (Array_t a bool)`,
but `x` is still annotated as `(Set_Set int)`. The subsequent sort
checker (`elabExpr`) then fails with

> Cannot unify `(Array_t int)` with `Set_Set` in expression: `arr_map_or ... x ...`

With this patch, the binder is rewritten to `(Array_t int bool)` at the
same time as the body operators, so the sort checker is satisfied.

## Why this hasn't surfaced before

Inside the normal fixpoint pipeline, `Set_*` operators appear in input
expressions but `Set_Set`-typed binders inside `PExist`/`PAll`/`ELam`
nodes are exceedingly rare in practice. `liquid-fixpoint`'s own front
ends and its standard horn-clause input encoding don't typically emit
`(exists ((x (Set_Set ...))) ...)` predicates directly: when the
internal solver performs kvar elimination via `cubePred`/`hypPred`
(`Language.Fixpoint.Solver.Solution`), the resulting cubes' existential
binders are taken from the *elaborated* bind environment, so their
sorts are already `(Array_t ...)` by the time `elabFSetBagZ3` sees
them. None of the existing test cases exercise the un-elaborated
`(Set_Set t)`-bound `PExist` shape.

The bug shows up when a *downstream* tool performs its own kvar
elimination — and therefore introduces its own `PExist` binders — and
emits the resulting constraint to fixpoint un-elaborated. That is the
situation in [Flux][flux] (a Rust verifier targeting liquid-fixpoint),
which is the context where I hit this. Flux's port of
`Solution.cubePred` runs on un-elaborated constraints and produces
`(exists ((x (Set_Set int))) ...)` cube bodies; fixpoint then crashes
during elaboration. With this patch, Flux's elimination output
elaborates cleanly.

[flux]: https://github.com/flux-rs/flux

## Scope of the fix

This patch fixes the **sort-annotation half** of the problem. There is
a related issue I'm not addressing here:

- `ECst e t` carries an explicit sort annotation. The patch *does*
  rewrite that annotation (so `(cast x (Set_Set int))` becomes
  `(cast x (Array_t int bool))`).
- However, types embedded in `ETApp`/`ETAbs` are still passed through
  unchanged. I haven't found a case where that matters in practice,
  but in principle the same rewriting should apply to be fully
  consistent.

A more thorough fix would lift the sort-rewriting helper (`goS`/`goS1`
in this patch) into a top-level `elabFSetBagZ3Sort :: Sort -> Sort`
that is used everywhere a sort appears in an expression node, and
applied consistently throughout the elaboration pipeline. The current
patch keeps the change local to `elabFSetBagZ3` to minimize blast
radius.

## Testing

- Existing test suite: all `native-pos`, `native-neg`, `elim-*`,
  `horn-*`, `z3-*`, `proof`, `rankN`, `saved.*` suites pass. The
  only pre-existing failure (`cvc5-pos.sets.fq`, which fails on
  unpatched `develop` too with the same `Symbol 'set.is_empty' not
  declared as a variable` error from CVC5) is unaffected.
- Targeted manual repro: a Flux test case (`pos/enums/list01`) that
  produced `(exists ((a (Set_Set int))) ...)` cube bodies and crashed
  fixpoint with `Cannot unify (Array_t int) with Set_Set in
  expression: arr_map_or ...` now elaborates and solves cleanly.

I haven't added a regression test inside this repo because the bug
requires input shapes (`PExist` with `Set_Set`-typed binders) that
none of the existing `.fq`/horn front ends emit, and adding a hand-
crafted `.fq` that exercises the path would itself depend on
infrastructure not exposed through the standard input grammars. If
desired, I'm happy to add one — let me know what shape you'd prefer.
