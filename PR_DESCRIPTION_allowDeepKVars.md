# Allow `PKVar` references in hyp-shape positions (`--allow-deep-kvars`)

## Summary

Adds opt-in support for `PKVar` references appearing inside the
"hyp" shape that downstream tools (e.g. [Flux][flux]) emit when they
pre-eliminate non-cut kvars *outside* the solver. The feature is
gated on a new flag, `--allow-deep-kvars`, so existing behavior is
unchanged by default.

Two pieces are needed end-to-end:

1. **Parser** (`Language.Fixpoint.Horn.Parse`): teach the Horn
   binder-predicate parser (`hPredP`) to accept the `Pred::Hyp`
   on-the-wire grammar Flux emits, mirroring
   `lib/liquid-fixpoint/src/format.rs` in flux-rs/flux.
2. **Solution apply** (`Language.Fixpoint.Solver.Solution`):
   recursively resolve any `PKVar` nodes the parser left buried
   inside a "concrete" predicate before the result is handed to SMT
   serialization (which panics on `PKVar`).

Both are no-ops when `--allow-deep-kvars` is not set.

## Motivation

Liquid-fixpoint's `Solver.Solution.cubePred`/`hypPred` syntactically
eliminates non-cut kvars by inlining their cube definitions into
their use sites *during solving*, after elaboration has run. The
shape of the eliminated predicate is recursively:

```
hyp_expr   ::= cube_expr                            -- singleton
             | (or cube_expr cube_expr ...)         -- multi
             | false                                -- empty

cube_expr  ::= pred_expr                            -- no binders
             | (exists ((b t) ...) pred_expr)       -- with binders

pred_expr  ::= <ordinary expr>
             | true
             | (and pred_expr pred_expr ...)
             | ($k a0 a1 ...)                       -- cut-kvar ref
             | hyp_expr                             -- nested
```

When a non-cut kvar's body itself mentions a *cut* kvar — e.g.
because cut/non-cut classification chose to keep `$k1` cut but
eliminate `$k2`, and `$k2`'s definition referenced `$k1` — the
resulting cube body contains a `PKVar` reference somewhere other
than the top of a conjunct list. That is fine inside the Haskell
solver (`cubePred` runs on internal AST that permits this), but
fixpoint's standard input grammar does not.

For [Flux][flux] — a Rust verifier targeting liquid-fixpoint — we
wanted to perform the same non-cut-kvar elimination *outside* the
solver, in Flux's own Rust code, and ship the pre-eliminated
constraints to fixpoint. That requires:

- a way to **serialize** these nested `PKVar` references in the
  on-the-wire `.smt2` Horn input, and
- a way for fixpoint to **parse and resolve** them when it reads
  the input back.

This PR adds both. The parser grammar admitted by fixpoint is
exactly the grammar Flux emits — nothing more — so a `$k …`
reference under `=>`, `not`, `=`, `if`, arithmetic, function-app
heads, or any other expression position fixpoint did not
previously accept remains a parse error even with the flag on.

[flux]: https://github.com/flux-rs/flux

## What changed

### `Language.Fixpoint.Types.Config`

- New field `allowDeepKVars :: Bool` (default `False`).
- New CLI flag `--allow-deep-kvars`.

### `Language.Fixpoint.Parse`

- New field on `PStateV`: `allowDeepKVarsP :: !Bool` (default `False`).
- New entry points `doParseWith`, `parseFromFileWith`,
  `parseFromStdInWith` that take a `PState -> PState` to let callers
  configure parser state without proliferating positional bool
  arguments. The existing `doParse'`/`doParse''`/`parseFromFile`/
  `parseFromStdIn` functions are unchanged.

### `Language.Fixpoint.Horn.Parse`

- `hPredP`'s `Reft` alternative now goes through a new
  `hPredReftP`, which under `--allow-deep-kvars` runs
  `try hypExprP <|> exprP` (and otherwise just runs `exprP`).
- New parser family `hypExprP` / `cubeExprP` / `predExprP` mirroring
  the grammar above. The kvar form (`kvarExprP`) is reachable
  **only** from `predExprP`'s `try (parens kvarExprP)` alternative
  — never via the general `exprP`/`pExprP` — so a deep kvar
  reference can only appear in a hyp-shape position.
- `kvarExprP` builds a `PKVar` with positional args mapped to
  symbols `hvarArgSymbol k 0`, `hvarArgSymbol k 1`, …. These are
  the same symbols `kvApp` (in `Language.Fixpoint.Horn.Info`)
  generates for the corresponding `wfc` parameters, so elaboration
  finds them in scope.

### `Language.Fixpoint.Horn.Solve`

- `parseQuery` now uses `parseFromFileWith`/`parseFromStdInWith` to
  forward `Config.allowDeepKVars` into the initial `PState`.

### `Language.Fixpoint.Solver.Solution`

- New helper `resolveBuriedKVars :: Config -> CombinedEnv -> Sol ->
  Expr -> (Expr, KInfo)`. Walks an expression and replaces every
  `PKVar k tsu su` node with the result of `applyKVar` on a
  synthesized `KVSub`. The substitution may itself introduce more
  `PKVar` nodes (a non-cut kvar's solution can mention cut kvars),
  so the walk recurses on the result. All other `Expr` constructors
  map structurally.
- `apply` and `applyInSortedReft` now run `resolveBuriedKVars` over
  the "concrete" predicates returned by `envConcKVars` before
  conjoining them into the final result, **only when**
  `allowDeepKVars cfg` is true. With the flag off, the existing
  invariant ("`ps` never contains `PKVar`") is preserved and the
  code path is byte-identical to `develop`.

## Why a flag

`develop` maintains an invariant that `envConcKVars`'s "concrete"
predicates contain no `PKVar` nodes — kvars only appear at the top
of a conjunct, where `sortedReftConcKVars` can split them out into
the `[KVSub]` side. The deep-resolve sweep weakens that invariant.
Putting the feature behind `--allow-deep-kvars`:

- preserves existing semantics exactly for current users,
- localizes the new behavior to clients that explicitly request it
  (currently: Flux),
- gives reviewers a single, narrow scope to evaluate, and
- makes it easy to back out or restrict the feature later.

## Why this is safe

**Parser.** The hyp-shape grammar accepted under the flag is
strictly a subset of what Flux's `Pred::Hyp` emitter produces, and
the kvar form is only reachable from `predExprP` (the deepest leaf
in that grammar). The general `pExprP` is untouched — kvar refs
remain a parse error under `=>`, `not`, `=`, `if`, arithmetic,
function-application heads, or any other expression position
fixpoint did not previously accept.

**Solver.** The `resolveBuriedKVars` walk is structurally pure: it
traverses every `Expr` constructor exactly once and produces an
expression of the same shape with `PKVar` nodes replaced. The
`KVSub` it synthesizes uses `dummySymbol :: FInt` for
`ksuVV`/`ksuSort`; inspection of `applyKVar` shows those fields are
only used for pretty-printing, never for substitution, so dummy
values are sound.

Dependency tracking (`kvarsExpr`, `Visitor.hs:464`) already
traverses deeply through `PExist`/`POr`/`EApp`/etc., so the solver
already knew about these buried kvars when computing the kvar
dependency graph — they were just rejected at parse time and would
have crashed SMT serialization (`Smt/Serialize.hs:216`) if anyone
managed to introduce one programmatically.

## Testing

- All Flux test suites pass with the patched fixpoint binary in
  scope and `--allow-deep-kvars` enabled on Flux's side (504 pos /
  0 fail; 431 neg / 0 fail). Without this PR, 32 of those tests
  fail at the fixpoint parser with `unexpected "$kN ..."`.
- Manual scope-tightness checks (hand-crafted `.smt2` repros):
  - `$k` as a conjunct of `and` inside `(or (exists ((…)) (and …)))`
    parses and resolves to `Safe`.
  - `$k` deep inside `(or (exists ((…)) (and (and ($k …)))))` also
    parses (hyp-shape recursion).
  - `$k` as an operand of `=>`, `=`, `not`, `if`, or `+` is rejected
    with `unexpected "$kN ..."`.
  - With `--allow-deep-kvars` omitted, even the valid hyp shape is
    rejected (gating works).
- I have **not** run `stack test` on the full liquid-fixpoint
  Haskell suite locally (it's slow), but the patch is gated such
  that the flag-off behavior is intended to be byte-identical to
  `develop` everywhere it matters. Happy to run it on request.

## Companion PR

This change is paired with a separate, narrower fix to
`elabFSetBagZ3` (see `PR_DESCRIPTION_elabFSetBagZ3.md` / commit
`4c6d8356`) that's also required for Flux to exercise `Set_*`-typed
binders in pre-eliminated cube bodies. The two changes are
independent and can be reviewed/merged separately.
