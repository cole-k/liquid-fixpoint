# W-Variable Implementation Plan (working notes)

**Status:** Draft, assembled from a design conversation that kept getting cut off
(possibly a safety-trigger issue, cause unknown). This file exists so the work can
be picked up in a fresh context without redoing the research. Anything marked
**GUESS** below is *my* inference, not something explicitly confirmed by Cole —
double check with him before committing to it.

Read `WVAR_ALGORITHM.md` first (the original algorithm sketch). This document
corrects/refines it based on:
1. A deep read of the current liquid-fixpoint codebase (file:line references
   throughout, so you can jump straight to the relevant code).
2. Clarifications from Cole that change the design in a few important ways from
   the original sketch (see "Key corrections" below) — **most importantly: a
   w-var is an applied, unknown *predicate* with arguments, exactly like a
   k-var, NOT a nullary boolean flag.** Earlier drafts of this plan (in the
   chat history) assumed the latter and are wrong; ignore any of my
   reasoning that treats `$w0` as argument-less.
3. Three real example queries Cole provided in `wvar_tests/` (`.smt2` / Horn
   format), which are the actual target syntax/test cases, not just
   illustrations. **Only the Horn/`.smt2` format matters — the old flat `.fq`
   format is explicitly out of scope (confirmed by Cole).**

---

## 1. Key corrections to `WVAR_ALGORITHM.md`

- **A w-var occurrence is an applied predicate, structurally identical to a
  k-var occurrence.** `$w0` takes positional arguments (`$w0[x:=e1][y:=e2]` in
  flat-file terms, `($w0 e1 e2)` in Horn terms) and appears literally inside a
  constraint's body — as a conjunct, or as a `forall`-binder's guard — exactly
  where a k-var occurrence can appear. It is **not** side-table-only metadata;
  `wGuards`-style bookkeeping (if we keep it) must be *derived from* occurrences
  in the constraint tree, not the sole source of truth.
- Confirmed real examples (`wvar_tests/`), e.g.:
  ```scheme
  (var $k0 (int int int int))
  (wvar wk$dotprod__dotprod$0 ((Adt0) (Adt0)))   ; declaration - same shape as (var ...)

  (forall ((_$ int) ((wk$dotprod__dotprod$0 reftgen$n$0 reftgen$m$1)))
    ...)                                          ; occurrence - applied, as a forall-guard
  ```
- **Only `.smt2`/Horn format matters.** Drop all flat-`.fq`-format plans
  (`Parse.hs`'s `defP`/`defsFInfo`, the `$`-sigil `kvarP`/`kvarPredP` in the
  *core* parser, etc.) — none of that needs touching. All work is in
  `src/Language/Fixpoint/Horn/*.hs` (plus whatever core `Types`/`Solver` code
  both formats already share, e.g. `Sol`, `refineC`, `lhsPred`).
- **AST representation decision (confirmed direction from Cole): reuse `PKVar`
  itself for w-var occurrences rather than adding a new `PWVar` Expr
  constructor.** Rationale discussed and agreed:
  - Avoids a large mechanical blast radius: I audited every exhaustive
    pattern-match over `Expr`/`ExprBV`'s 22 constructors in `src/` — exactly
    6 files / 17 exhaustive definitions would need a new equation for a new
    constructor (`Types/Refinements.hs` ×4: `mapBindExpr`, `debruijnIndex`,
    `Fixpoint`/`toFix`, `PPrint`/`pprintPrec`; `Types/Visitor.hs` ×5: `transE`,
    `foldExpr`, `mapExprOnExpr`, `mapMExpr`, `kvarsExpr`; `SortCheck.hs` ×2:
    `checkExpr`, `elab`; `Solver/Interpreter.hs` ×3; `Solver/Extensionality.hs`
    ×2; `Types/SMTPrint.hs` ×1 `toHornExpr`) — plus ~15 more partial-match
    sites elsewhere that would silently under-handle it (a couple of which
    (`Solver/Eliminate.hs:120`, `SortCheck.hs:509`) currently `error`/`panic`
    on an unrecognized fallback rather than silently no-op).
  - Reusing `PKVar` means **all of that machinery works for free**,
    unmodified: parsing (`kvSymP`/`hPredP`'s existing `H.Var` grammar, no new
    production needed at all — see §3), sort-checking, elaboration,
    defunctionalization, SMT serialization avoidance (kvars are always
    "expanded away" via `apply`/`applyKVar`/`qbPreds` in
    `Solver/Solution.hs` before anything reaches the SMT layer — confirmed:
    `Smt/Serialize.hs`'s `instance SMTLIB2 Expr` (lines 170-216) never
    mentions `PKVar` and panics if one ever reached it un-expanded — so
    reusing `PKVar` means we get "carry it around like a regular Expr during
    fusion, only fully expand/resolve later" for free, which is *exactly*
    the behavior Cole described wanting).
  - This directly matches what Cole said: *"We pretend like they're true
    initially (but then still carry them around as if they were regular
    Exprs when we do fusion), and then we solve for them afterwards."* — see
    §5 for exactly how "pretend true initially" is achieved with **zero**
    changes to `refineC`/`refine`/`filterValid`/`S.update`/`lhsPred`/`apply`.
  - Counter-concern Cole raised: reusing `KVar`/`PKVar` risks "accidentally
    doing something to a w-var that only should be done for k-vars."
    **Recommendation (GUESS, needs confirmation): split the difference.**
    - At the raw `Expr`/AST level: a w-var occurrence literally *is* a
      `PKVar` node (same `KVar`-wrapped `Symbol`, same `KVarSubst`). No new
      constructor.
    - At every other level (the actual "is this thing weak" bookkeeping,
      `GInfo`'s new fields, `Result`'s new field, the whole Phase 2/3
      algorithm's own types), keep a **separate, distinctly-named `WVar`
      type** (`newtype WVar = WV { wv :: Symbol }`, mirroring `KVar`'s own
      definition at `Types/Refinements.hs:220-221`) so every new function
      signature we write is explicit about "this operates on a weak var,"
      and it's impossible to accidentally pass a "real" random `KVar` into
      Phase 2/3 code. Convert at the boundary with trivial wrappers
      (`KV . wv`, `WV . kv`) exactly where a `WVar` needs to be looked up
      inside `ws`/`sMap`/etc. (which are keyed by `KVar`).
    - This means: **`ws :: HashMap KVar (WfC a)` gets entries for w-vars
      too** (see next point) — reusing `WfC`'s existing "declared scope +
      sorts" machinery — the *only* new bookkeeping is a small
      `wVars :: HashSet WVar` (or equivalently `HashSet KVar`, tagged)
      marking *which* of the `ws` entries are weak, used to (a) seed their
      solution to `true` instead of running normal qualifier instantiation,
      (b) exclude them from the iterative worklist, (c) validate they never
      appear as a constraint head, (d) drive Phase 2/3.
  - **Open naming collision question (not yet asked/answered):** since
    strong k-vars and weak w-vars would share one namespace/representation
    (`KVar`/`ws`), do we need to validate that a given symbol isn't declared
    as *both* `(var $x ...)` and `(wvar $x ...)`? Almost certainly yes, a
    cheap Sanitize-style check — flagging as a TODO, not yet discussed with
    Cole.
- **Confirmed: w-vars do have a "self"/distinguished value argument**,
  mirroring how a k-var's first declared sort doubles as its `WfC`'s
  value-variable (`Horn/Info.hs`'s `kvInfo`, `Misc.safeUncons` splitting off
  arg 0 — see condensed research notes in §8). Cole: *"they do have self
  arguments. Sometimes they don't have one as well, but I can fix that in the
  CHC generation code to just generate unit or something as the self
  param."* — i.e. CHC-generation-side concern, not ours; we can assume every
  `(wvar ...)` declaration's arg-sort list is non-empty and treat it exactly
  like a `(var ...)` declaration for `WfC`-construction purposes. Cole noted
  this only really matters once we've found a solution for the w-var
  ("punt on this as long as we track it") — i.e. don't over-invest in this
  detail for v1, just don't lose the information.
- **Confirmed: no bespoke, heavyweight `Sanitize`-style domain/scope
  validation needed for w-vars specifically for v1.** I'd asked about
  mirroring `Sanitize.hs`'s `restrictKVarDomain`/`badParams` (which are
  tightly, monomorphically coupled to concrete `KVar`/`WfC` — not a generic
  mechanism, would need real parallel code to reuse for a hypothetical
  separate `WVar`-keyed domain). Cole: *"probably not... we can trust that
  the CHC generation is valid if that's easier"* — confirms: since we're
  reusing `ws`/`WfC`/`KVar` directly (per the recommendation above), we
  likely get whatever basic checking already exists **for free**, and don't
  need to build anything new here for v1.

---

## 2. Confirmed decisions (quick-reference list)

| Question | Answer |
|---|---|
| Which surface format? | `.smt2`/Horn only (`Horn/*.hs`). Flat `.fq` is out of scope. |
| AST representation of an occurrence | Reuse `PKVar` (no new `Expr` constructor). |
| Declaration syntax | `(wvar <name> (<sort>*))` — same shape as `(var $k0 (<sort>*))`. Leading `$` on the name is fine (Cole: "You can syntactically distinguish them... leading with $ is fine" — the `wvar_tests/*.smt2` files can be edited to add `$`, they're not gospel on this particular detail). |
| Occurrence syntax | Same as k-var occurrences today: `($w0 arg1 arg2 ...)` (assuming we do give w-var names a leading `$`, this needs **zero** new parser code at the occurrence site — see §3). |
| Self/value argument | Yes, w-vars have one, mirroring k-vars (first declared sort = value var). May occasionally be missing from generated CHC today; that's a CHC-generation-side fix, not ours. Punt on edge cases for v1, just don't lose track of which declared sort is "self." |
| Domain/scope validation rigor | Light — trust CHC generation, don't build new bespoke validation beyond whatever we get for free by reusing `WfC`. |
| resWVars vs resStatus semantics | **Diagnostic only, and only populated on failure.** `resStatus` stays exactly what standard (w-vars-assumed-true) checking says. When it's `Safe`, report plain SAT, no w-var info at all. When `Unsafe`, additionally report, per failing constraint, a list of *multiple* candidate fix *bundles* to give the caller choices (see §5 point 3 for the exact shape: `M.HashMap SubcId [M.HashMap WVar Expr]`) — a bundle may involve more than one w-var cooperating; the bundle using the fewest distinct w-vars is the preferred/"best" one. Exact enumeration mechanism still needs designing (§5). |
| CLI flag | Explicit opt-in, default off (e.g. `--wvars`), following the `--eliminate`/`--ple` precedent. |
| Partitioning/multicore correctness (constraints sharing a w-var guard could land in different graph partitions, since `decompose`/`kvEdges` don't know about w-var guards) | Discussion started, not concluded — Cole pushed back on "why is this a problem" and I'd given a concrete scenario (one w-var guarding many kvar-disjoint call sites across a program); we hadn't picked a mitigation before getting cut off. **Still open**, see §6. |
| Guard-association mechanism (separate `wGuards` declaration vs. inline vs. embed-in-body) | **Superseded/resolved by the AST correction**: since w-var occurrences are literal `PKVar`-shaped nodes inside a constraint's body, "which constraint is guarded by which w-var" is *derived* by scanning constraint bodies for weak-`KVar` occurrences (reusing existing occurrence-scanning infra like `V.envKVars`/`V.kvarsExpr`, filtered to `wVars`), not separately declared. The old "inline field vs side-table" question is moot. |

---

## 3. Syntax and parsing plan (Horn/`.smt2` format only)

### Declaration

```scheme
(wvar $w0 (int int))
```

Should parse essentially identically to the existing k-var declaration
(`Horn/Parse.hs:232-233`):
```haskell
hVarP :: FParser (H.Var H.Tag)
hVarP = H.HVar <$> kvSymP <*> parens (some sortP) <*> pure H.NoTag
```
i.e. add a new alternative to `hThingP` (`Horn/Parse.hs:163-177`):
```haskell
<|> HWVar <$> (reserved "wvar" *> hVarP)   -- new HThing variant; hVarP itself is reusable as-is
```
(`hVarP`'s return type `H.Var H.Tag` — i.e. `HVar { hvName, hvArgs, hvMeta }`,
`Horn/Types.hs:56-61` — is exactly what we want for a w-var declaration too:
a name + list of arg sorts. No changes needed to `Var`/`HVar` itself.)

This needs:
- A new `HThing` constructor (`HWVar (H.Var H.Tag)`, alongside the existing
  `HVar`/`HCstr`/`HQual`/etc. at `Horn/Parse.hs`'s `HThing` sum type — find
  its definition near `hThingP`).
- A new field on `H.Query` (`Horn/Types.hs:196-209`), e.g. `qWVars :: [Var a]`,
  populated the same way `qVars` is (collect `HWVar v <- things`).
- **Reused as-is:** `kvSymP` (`Horn/Parse.hs:209-210`, `char '$' *> symbolP`)
  and `sortP` (`Horn/Parse.hs:291-308`, including its wrapped-vs-bare
  compound-sort convention — this is why `wvar_tests/pldi23...smt2`'s
  `((Adt0) (Adt0))` and `(int int)` both show up: it's just whatever the
  general sort grammar already does for nullary vs. applied type
  constructors, nothing w-var-specific).

### Occurrence

If w-var names get the same `$`-prefix as k-var names (confirmed acceptable
by Cole), then **occurrences need zero new parser code**: `hPredP`
(`Horn/Parse.hs:200-210`) already has
```haskell
hPredP = parens body
  where
    body =  H.Var  <$> kvSymP <*> some exprP
        <|> H.PAnd <$> (reserved "and" *> some hPredP)
        <|> H.Reft <$> exprP
```
and `($w0 e1 e2)` parses via the *existing* `H.Var <$> kvSymP <*> some exprP`
alternative exactly like a k-var occurrence would — `H.Var`'s `Symbol` field
doesn't know or care whether the name was declared via `(var ...)` or
`(wvar ...)`. Disambiguation ("is this really weak") happens later, when
`Horn/Info.hs`'s `predExpr`/`kvApp` (`Horn/Info.hs:101-113`) turns a `H.Var k
ys` into `F.PKVar (F.KV k) M.empty su` — at that point (or slightly
downstream, wherever we build `wVars`), cross-reference `k` against the set
of declared weak names.

**This is the payoff of reusing `PKVar`/the existing `$`-marker convention:
the entire "how do I parse a w-var occurrence" question, which looked like a
real design problem before Cole's correction, disappears — it's the exact
same grammar production already used for k-vars.**

### `Horn/Info.hs` — building `F.SInfo`/`GInfo`

`hornWfs`/`kvInfo` (`Horn/Info.hs:116-157`, condensed research in §8) already
does exactly the "turn a declaration's sort-list into a `WfC` + a
`KVEnv`/param-name cache" work we want for w-vars too — **plan is to run it
(or a trivial generalization of it) over `qWVars` as well as `qVars`,
producing `WfC` entries that get merged into the same `ws` map**, then
additionally record which of those `KVar`s are weak into a new `wVars ::
HashSet WVar` field. `kvApp` (`Horn/Info.hs:101-113`) needs no changes at all
— it already turns *any* `H.Var k ys` into a `PKVar`, regardless of whether
`k` is weak, as long as the combined `KVEnv` (built from `qVars ++ qWVars`)
has an entry for it.

---

## 4. Data model plan

`src/Language/Fixpoint/Types/Constraints.hs` (co-located with `Kuts`,
`Constraints.hs:662-680`, and `GInfo`, `Constraints.hs:744-760`):

```haskell
newtype WVar = WV { wv :: Symbol }
  deriving (Eq, Ord, Data, Typeable, Generic, IsString, ToJSON, FromJSON)
instance Hashable WVar   -- mirrors KVar's own standalone instance
```

Add to `GInfo` (`Constraints.hs:744-759`):
```haskell
, wVars :: !(S.HashSet WVar)   -- ^ which of the KVars in `ws` are weak/w-vars
```
(No separate `wGuards` field needed as a *parsed* thing — see §1/§2, it's
derived from occurrences when needed, e.g. by Phase 2/3 scanning each
constraint's environment for weak-kvar occurrences via the existing
`V.envKVars`/`V.kvarsExpr`-style helpers.)

Add to `Result` (`Constraints.hs:265-271`):
```haskell
, resWVars :: !(M.HashMap SubcId [M.HashMap WVar Expr])
  -- ^ Only non-empty when resStatus is Unsafe. For each failing constraint
  --   id (already paired with the caller's own per-constraint metadata/tag
  --   in resStatus's own Unsafe bad-list), a list of *multiple* candidate
  --   fix *bundles*, to give the caller choices — each bundle a map of
  --   one-or-more w-vars to solutions that, applied together, fix that
  --   failure (a singleton map is the "one w-var suffices" case). The
  --   bundle using the fewest distinct w-vars is the preferred/"best" one.
  --   See §5 point 3.
```

All the mechanical touch points from the original research (still accurate,
just now only **one** new `GInfo` field instead of two):

| Site | File:Line | Change |
|---|---|---|
| `GInfo` field decl | `Constraints.hs:744-759` | add `wVars` field |
| `fi` smart ctor | `Constraints.hs:699-714` | add named field (no callers exist repo-wide — verified, safe) |
| `Semigroup (GInfo c a)` | `Constraints.hs:770-785` | `wVars i1 <> wVars i2` |
| `Monoid (GInfo c a)` | `Constraints.hs:788-803` | `wVars = mempty` |
| `Parse.hs:1405` `defsFInfo` (only positional `FI` ctor call site in the repo) | N/A — **not applicable**, flat `.fq` format is out of scope, this path is untouched | — |
| `toFixpoint` printer | `Constraints.hs:813-846` | only matters if we ever want to round-trip back to flat `.fq` text (probably not needed since Horn format has its own printer, `ToHornSMT`) |
| `Result` Semigroup/Monoid/`safe`/`unsafe` | `Constraints.hs:325-339` | 5th field everywhere |
| `ToJSON (Result a)` (hand-written, not derived!) | `Constraints.hs:304-311` | add `"wVars" .= resWVars r` explicitly — confirmed new fields do **not** auto-serialize |
| `crashResult`/`crashResultOther` | `Solver.hs:196,209` | `Result res mempty mempty mempty` → add 5th `mempty` |
| `hornFInfo` | `Horn/Info.hs:20-33` | wire `qWVars`-derived `WfC`s into `ws`, and populate the new `wVars` field |

---

## 5. Solving algorithm plan (corrected/simplified)

### Phase 1 — "pretend true initially, carry through fusion" — turns out to need **no logic changes** to the core solve loop

Because a w-var occurrence is literally a `PKVar` node, and because k-vars are
always "expanded" via `Sol.lookup`/`applyKVar`/`qbPreds`
(`Solver/Solution.hs:349-367`) before anything reaches `filterValid`/SMT
(confirmed: `Smt/Serialize.hs`'s `instance SMTLIB2 Expr` never mentions
`PKVar` and panics on one — so an *unexpanded* `PKVar` never reaches the SMT
layer, by construction, today):

- **Seed every w-var's entry in the initial `Sol.Solution`'s `sMap` to
  `QB [trueEqual]`** (`trueEqual :: EQual`, already exists,
  `Types/Solutions.hs:237-238`) instead of running the normal
  qualifier-instantiation (`Solution.init`/`refineK`, `Solver/Solution.hs:57-64`)
  for them. This is a small, localized change to `solve`'s `s0` construction
  (`Solver/Solve.hs:87`: `s0 = (siSol sI) { Sol.sMap = S.init cfg fi ks }`) —
  compute `ks` to exclude weak kvars from the normal-init path, then union in
  `M.fromList [(KV (wv w), QB [trueEqual]) | w <- S.toList (F.wVars fi)]`.
- **Everything else is unmodified**: `refineC`/`refine`/`filterValid`/
  `S.update`/`lhsPred`/`apply`/`applyKVar`/`qbPreds` all work exactly as
  today. A w-var's `QBind` is `[trueEqual]` and *stays* `[trueEqual]` for the
  entire Phase 1 fixpoint, because `refineC`'s `rhsCands`/`predKs`
  (`Solve.hs:272-282`) only ever tries to shrink a KVar's QBind if that KVar
  appears on some constraint's `crhs` (RHS) — and a w-var, by construction/
  validation, never does. So it just sits there contributing `true` wherever
  referenced, exactly the desired "assume true" semantics, for free.
- **Validate (Sanitize-time, or wherever convenient) that no weak `KVar`
  ever appears in any constraint's RHS** — this is the actual enforcement of
  "w-vars appear only in constraint bodies, never as heads." If this
  invariant holds, the "exclude from worklist" property above is automatic
  (worklist population, `Worklist.init`, `Worklist.hs:87-110`, is driven by
  which *constraints* have a kvar-headed RHS, not by iterating kvars
  directly) — so there's likely nothing else to change in `Worklist.hs` at
  all.
- **New concern introduced specifically by the `PKVar`-reuse decision: the
  Eliminate/"Fusion" pass must treat every w-var as forced-cut (never try to
  eliminate/substitute it).** Cole's framing: *"do fusion and pretend like
  wvars aren't kvars at this point (probably a nonissue if we aren't doing
  the pkvar-reuse design)."* Concretely: `Graph/Deps.hs`'s `kvEdges`/
  `subcEdges` (lines ~213-231) extract dependency-graph edges from **any**
  `PKVar` occurrence found via `V.envKVars`/`V.rhsKVars`, with no notion of
  "weak" — so once w-vars are `PKVar`-shaped, they show up in this graph
  like any other kvar, with incoming edges (constraints that read them) but
  **zero outgoing edges** (since, by construction/validation, they never
  appear as an RHS, i.e. they never have a "defining constraint" to
  substitute in). `Solver/Eliminate.hs`'s elimination step assumes an
  eliminable (non-cut) kvar *has* defining constraints to build a
  substitution from; a w-var handed to that machinery would either produce
  a bogus/empty substitution (wrong — we want `true`, not "no valid
  instantiation") or hit a partial-function assumption. **Fix: force every
  w-var into the cut set** (add `F.wVars`-derived `KVar`s into whatever
  `cutVars`/`forceKuts` (`Graph/Deps.hs:316-322`) consumes, or filter them
  out of the eliminable-candidate set directly), so elimination always
  leaves w-var occurrences alone, and the seeded `[trueEqual]` `sMap` entry
  (previous bullet) is what actually resolves them, unmodified, during
  `refineC`. **Had we gone with a separate `PWVar` constructor instead of
  reusing `PKVar`, this whole concern would not exist** — `kvEdges`/
  `envKVars` specifically look for `PKVar` nodes and would simply never see
  a `PWVar`, so it'd be automatically invisible to the elimination graph.
  That's the tradeoff Cole flagged: reusing `PKVar` buys the "carried
  through fusion for free" property (previous bullet) at the cost of having
  to explicitly opt w-vars *out* of the one piece of "fusion" machinery
  (elimination) where being kvar-shaped is actively unwanted.
- **Removal tracking** (needed for Phase 2/3, same as originally planned):
  wrap `refineC`'s `S.update` call (`Solve.hs:250-270`) to also record, for
  each **non-weak** kvar `k`, which `EQual`s got dropped by this call
  (`qbEQuals oldQB \\ qbEQuals newQB`) and which constraint (`SubcId`) caused
  it. Thread as an explicit accumulator through `refine`'s existing loop
  (`Solve.hs:231-241`), gated by a `Bool` (`not (S.null (F.wVars fi))`) so
  there's zero overhead when the feature is unused. See the original
  (pre-correction) plan notes for the full mechanical detail — that part of
  the design is unaffected by the AST-representation correction.
- **"Which constraint is guarded by which w-var" is now a derived query, not
  parsed data**: for a given constraint, scan its environment/LHS for weak-
  KVar occurrences (reuse `V.envKVars`/`V.kvarsExpr`-shaped helpers,
  `Types/Visitor.hs`, filtering results against `F.wVars fi`). Do this
  on-demand inside Phase 2/3 rather than precomputing a `wGuards` map, unless
  profiling says otherwise.

### Phase 2/3 — simplified per Cole's latest guidance (this **supersedes**
`WVAR_ALGORITHM.md`'s Phase 2/Phase 3 description)

Direct quote (preserve verbatim, this is the actual spec now):

> The algorithm you were working with is probably **almost** correct. The
> basic idea is just that we need to check to see if we can WP each
> qualifier we want a wvar to guard to "save" it — OR we could naively
> expect that the wvar is capable of "saving" it and then WP the final
> solution after we do UNSAT Core to figure out what parts are needed. I
> think the latter is simpler. I care more about getting started with
> something and we can iterate and improve if need be.
>
> The slightly more general algorithm is one that checks when a head fails
> whether (a) (NEW) a single wvar can solve the failing head itself or (b)
> (previous) some strengthening of the kvars in its LHS can solve it (and
> then it goes and figures out which, minimizes, etc.)

**Priority for v1 (Cole, explicit): implement case (b) — k-var strengthening
— first; treat case (a) — direct w-var-solves-the-head — as a follow-up to
revisit afterwards.** *"the core algorithm we're developing is one where we
actually use the wvar to strengthen a kvar. So for a first pass we could just
focus on that and revisit the other case afterwards."* The two cases, for
each failing concrete constraint `c` (from `result_`'s `Unsafe` list,
`Solve.hs:340-348`):

1. **(v1 PRIMARY TARGET, case b) Can strengthening some k-var(s) in `c`'s LHS
   (by rescuing qualifiers that Phase 1 stripped due to assuming w=true) make
   `c` valid, where the rescue is justified by some w-var's weakest
   precondition?** — this is `WVAR_ALGORITHM.md`'s original Phase 2/Phase 3,
   simplified per Cole's preferred v1 strategy, and **generalized to allow a
   single failing head to need more than one w-var cooperating** (Cole:
   *"isn't the solving that we described more general than just a single
   (wvar, candidate solution) pair? ... the basic idea is that we find some
   sort of unsat core set of qualifiers we need to add back and we work
   backward to a wvar solution for them"* — confirmed: yes, and it falls out
   almost for free):
   - **v1 (simpler, recommended): "assume + UNSAT core" instead of "check
     each candidate qualifier up front."** I.e., don't do the doc's original
     Phase-2 monotone-fixpoint per-qualifier `lhs_enh => Q` checking loop,
     and don't restrict the assumption to one w-var at a time either.
     Instead: *optimistically* assume **every** qualifier that got stripped
     from k-vars appearing in `c`'s (transitive) LHS due to *any*
     w-guarded constraint can be rescued — pooling candidates from **all**
     w-vars together, not just one — build the single "enhanced" solution
     with all of them included, check that this enhanced LHS now implies
     `c`'s RHS (if it still doesn't, no combination of w-vars can fix this
     head; genuinely unfixable, move on), then run **UNSAT core
     extraction** over that one joint check to find which subset of the
     assumed-rescued qualifiers were actually load-bearing.
     - **The multi-w-var generalization is just a bookkeeping step on top
       of this, not a different algorithm:** each candidate qualifier in
       the pool is already tagged with which constraint stripped it, and
       (via `wGuards`-style lookup) which w-var guards that constraint. So
       after minimization, **group the surviving qualifiers in the core by
       their attributed w-var** (and, within a w-var, further by *which* of
       its guarded constraints produced them, since a single w-var may
       guard several constraints feeding different k-vars). If the group
       has exactly one w-var, that's the "single-wvar fix" case; if it has
       more, that's a genuine multi-w-var cooperative fix — same
       mechanism, no special-casing needed to support it.
     - **Nice side effect**: this also naturally lifts
       `WVAR_ALGORITHM.md`'s original stated limitation ("a qualifier
       needing BOTH omega_1 AND omega_2... we do not attempt cross-omega
       cooperation") — that limitation was an artifact of the *old*
       per-omega-isolated-checking design (`enhanced(*, omega_i)` computed
       and tested separately for each omega). Since the new approach builds
       *one* joint enhanced solution from all w-vars' candidates at once
       and only disentangles them afterward via the UNSAT core, cooperating
       w-vars are supported without extra work.
     - **Minimize w-var count, and enumerate multiple candidate solutions
       (Cole, explicit — promotes this from a caveat to a real design
       goal): "the overall best solution minimizes the number of wvars —
       but we also want to report multiple solutions to give choices."**
       So this is not just "one bundle, whatever the UNSAT core happens to
       give back": the intended behavior is to actually search for/report
       **several** distinct candidate bundles for a given failing head, and
       among them treat the one using the *fewest distinct w-vars* as the
       preferred/"best" one (with ties presumably broken some other way,
       e.g. fewest total qualifiers — not yet specified). A plain UNSAT
       core minimizes the *set of qualifier assumptions* handed to the
       solver, not the *number of distinct w-vars* those qualifiers happen
       to be attributed to — so naive "just take whatever core the solver
       returns" is not sufficient on its own to satisfy this goal; some
       amount of deliberate search/biasing is needed on top of it. Options
       to implement this (not yet decided, needs its own design pass when
       picked back up):
       - Bias the minimization to prefer dropping an entire w-var's
         contribution at once before touching another's (e.g. try
         minimizing per-w-var-group first, falling back to per-qualifier
         only within a group), which naturally tends toward
         fewer-distinct-w-vars solutions without a separate search.
       - Enumerate multiple candidates by finding one core, then blocking
         it (e.g. adding a clause forbidding that exact activation-literal
         assignment) and re-running core extraction to find a different
         one, repeating some bounded number of times; rank the results by
         distinct-w-var count afterward.
       - Some combination of both (bias first, then still enumerate a few
         alternatives around the biased-minimal one).
       This is real, not-yet-designed work — flagging it clearly rather
       than pretending "call `get-unsat-core` once" fully satisfies what
       Cole actually wants here.
     - **Needs investigation**: does the current SMT layer
       (`Smt/Interface.hs`/`Solver/Monad.hs`) support named/labeled
       assertions + `get-unsat-core`? I hadn't checked this before getting
       cut off — this is a prerequisite piece of research for implementing
       the v1 approach as Cole described it. If not supported, either add
       it (a real but bounded chunk of new SMT-layer plumbing) or fall back
       to the doc's original per-qualifier-check variant (which needs no
       UNSAT core support, just repeated `isValid`/`filterValid` calls, at
       the cost of being a bit more code/iteration up front instead of one
       assume-and-shrink pass — note the per-qualifier-check variant would
       need its own, more deliberate generalization to support multi-w-var
       cooperation, since its whole structure is "test one omega's
       enhancement in isolation"; the assume+UNSAT-core variant gets this
       for free, which is another point in its favor for v1).
   - Once the minimal (or full, if skipping minimization entirely for a
     first cut) rescued-qualifier set is known, partitioned by w-var (and,
     per w-var, by guarding constraint), compute **each involved w-var's own
     solution independently**: for w-var `$w`, for every constraint `c'`
     that `$w` guards, `WP_{c'} := lhsPred(c', enhanced) => pAnd(S_{c'})`
     where `S_{c'}` is just the subset of the minimal core attributed to
     `$w` via `c'` specifically, conjoined across all of `$w`'s guarded
     constraints that contributed. The resulting **bundle** for this
     failing head is the map of every involved w-var to its own computed
     solution. This part of the original doc's Phase 3 step 3 is otherwise
     unaffected by either simplification — it's pure syntactic construction
     (`PImp`/`pAnd`, already exist, no new SMT calls).
   - **Prune vacuous solutions before reporting them (Cole, explicit —
     confirmed OK to implement later, not a v1 blocker): "we also want to
     prune solutions which are vacuous (either being literally false or
     creating a contradiction in a head somewhere)."** A syntactically
     well-formed WP formula isn't automatically a *useful* one — two known
     degenerate cases to filter out once this is built:
     - The computed solution for some w-var in a bundle is (syntactically,
       or via a quick SMT equivalence check) just `PFalse`/unsatisfiable.
       Setting a w-var to always-false is a trivial, useless "fix" (it
       vacuously satisfies any `omega /\ L => Q` implication regardless of
       `Q`) and shouldn't be surfaced as if it were a meaningful answer.
     - Adopting a bundle's proposed w-var assignment(s) would create a
       contradiction somewhere else — i.e. some *other* constraint guarded
       by one of the bundle's w-vars becomes unsatisfiable/impossible to
       satisfy given that assignment. This needs a global
       plausibility/consistency check (does the proposed bundle, combined
       with *every* other obligation on its w-vars — not just the one
       failing head it was derived from — remain jointly satisfiable?)
       before a bundle is trustworthy to report.
     Explicitly deferred implementation-wise; just make sure this doesn't
     get lost — track it as a concrete post-v1 follow-up once bundles are
     being computed at all.
2. **(DEFERRED — implement after case (b) works, not part of the v1 cut)
   case a: can a single w-var directly solve this head, with no k-var
   strengthening at all?** I.e. `c`'s LHS contains an occurrence of some
   weak kvar `$w` such that plugging in *some* predicate for `$w` directly
   (computed via WP from `c`, no qualifier-rescue machinery involved) would
   make `c` valid. This is the **dot-product test case** — Cole: *"the
   dotproduct case is not officially covered by the algorithm we sketched —
   it is the simplest case, one where there is NO kvar-wvar interaction.
   This is one where we just need to do WP to figure out the solution on the
   wvar."* Revisit once case (b) is working; likely a strict simplification
   of the same machinery (no qualifier-set/UNSAT-core step needed, just a
   direct `WP($w) := lhs-minus-$w => rhs` check).
3. **Output shape (Cole, explicit — corrects the "diagnostic-only" wording
   below, and generalized per the multi-w-var discussion above):** if the
   query is solvable normally (Phase 1 alone succeeds), report **plain
   `Safe`/SAT as today, with no extra w-var info at all**. Only if `Safe`
   fails do we attempt case (b)/(a) above and report additional
   information: **for each failing constraint, a *list* of candidate
   *bundles*, where each bundle is itself a map of one-or-more w-vars to
   their solutions, and applying that whole bundle together — with every
   w-var *not* mentioned in it left at its default assumed-`true` value —
   would fix *that* failure.** Concretely:
   ```haskell
   resWVars :: M.HashMap SubcId [M.HashMap WVar Expr]
   ```
   (only ever non-empty when `resStatus` is `Unsafe`). A bundle with one
   entry is the "single w-var fixes it" case; a bundle with more is a
   genuine multi-w-var cooperative fix (§ above). **Revised v1 scope
   note (was previously "defer the outer list" — Cole corrected this):**
   the outer list is wanted, not deferred — report **multiple** candidate
   bundles per failing constraint so a caller can choose among them, and
   order/flag them so the bundle using the *fewest distinct w-vars* is
   identifiable as the preferred/"best" one (per the "minimize w-var count"
   goal above). What's still genuinely open/not-yet-designed is *how many*
   alternatives to search for and the exact enumeration mechanism (see the
   bulleted options in case (b) above) — that's real work to figure out
   when this is picked back up, not a "just call the API twice" change.
   Note `FixResult`'s existing `Unsafe Stats [a]`
   bad-list is already built as `[(SubcId, a)]` pairs via `ci c = (F.subcId
   c, F.sinfo c)` (`Solve.hs`'s `result` function) — i.e. the caller's own
   per-constraint metadata (for a real Horn/Flux query, this is the string
   `H.Tag` like `"0"` visible in the `.smt2` files' `(tag ... "0")`
   annotations) is *already* paired with `SubcId` there. So `resWVars`
   doesn't need to duplicate "tag" bookkeeping itself — it can just be
   keyed by the same `SubcId` already present in `resStatus`'s own
   bad-list, and callers (e.g. Flux) correlate the two by that shared key
   to get "for tag T, here are the candidate fix bundles." (Core
   `Types.Constraints` can't reference `H.Tag` directly — `Horn` depends on
   `Types`, not the reverse — so `SubcId` is the right currency for this
   field regardless.)
4. `resStatus` itself stays governed purely by the standard
   (w-vars-assumed-true) Phase-1-only check — finding w-var fixes in (b)/(a)
   does **not** flip `Unsafe` constraints to being counted as `Safe`; it's
   reported as extra, best-effort info alongside the unchanged verdict.

---

## 6. Still-open questions (pick up here when resuming)

1. **UNSAT core support** — does `Solver/Monad.hs`/`Smt/Interface.hs` already
   support labeled assertions + core extraction? Needs a research pass
   before committing to the "assume + UNSAT-core-minimize" Phase 2/3
   strategy Cole prefers. If genuinely absent, gauge how big a lift adding
   it would be vs. falling back to the doc's original per-qualifier-check
   loop for v1.
2. **Partitioning/multicore correctness** — `decompose`/`kvEdges`
   (`Graph/Deps.hs:195-231`) build the graph used to split a query into
   independent partitions (for `--parts`/multicore, on by default since
   `multicore cfg = cores cfg /= Just 1` and `defConfig`'s `cores = Nothing`)
   purely from k-var sharing. Since a single w-var can guard many
   constraints that share no k-vars with each other (very plausible: e.g.
   one w-var per "risky operation", used at many unrelated call sites across
   a program), those constraints could land in different partitions, and
   each partition's independently-computed w-var solution could be
   incomplete/wrong when only one survives `mconcat`'s left-biased
   `HashMap` union (`Result`'s `Semigroup`, `Constraints.hs:325-331`). We'd
   gotten as far as "what should v1 do about this" (options discussed:
   force single-partition when any w-var is present; validate-and-error
   post-partition if a w-var's occurrences got split; teach
   `decompose`/`kvEdges` about weak-kvar-sharing as a new connectivity edge;
   accept the risk and document it) but hadn't converged before getting cut
   off. Cole pushed back with "why should this be a problem" and I'd given
   the concrete scenario above — pick the conversation back up from there.
3. **Naming-collision validation** — should we reject a file where the same
   symbol is declared both `(var $x ...)` and `(wvar $x ...)`? (Leaning yes,
   not yet discussed.)
4. **Self-argument edge case** — what should we actually do (validate/error
   vs. silently tolerate) if a `(wvar ...)` declaration has an empty sort
   list, given Cole said this can currently happen from CHC generation and
   he might fix it upstream to always emit at least a "unit" self-arg? Punt
   per his guidance, but decide: hard error, or silently treat as "no self
   arg" and adjust whatever downstream code assumes arg-0-is-self?
5. **Multiple w-vars needing to cooperate** — doc's original text says this
   case is intentionally *not* handled (only single-w-var fixes are
   attempted per failing head); confirm this restriction still stands under
   the simplified Phase 2/3 approach (I believe yes, but wasn't explicitly
   re-confirmed after the simplification).
6. Work through Cole's `wvar_tests/*.smt2` files by hand against the
   simplified algorithm once implemented, as the first real integration
   tests (convert into `tests/` fixtures — likely `tests/horn/pos` or a new
   `tests/wvars/` subdirectory mirroring the existing `dirTests` wiring in
   `tests/test.hs:90-108,127-140`, which is 100% directory-driven — no other
   test-harness file needs touching to add a new directory).

---

## 7. Suggested order of work

1. `WVar` type + `GInfo.wVars` field + `Result.resWVars` field + all the
   mechanical `Semigroup`/`Monoid`/`ToJSON`/etc. touch-ups from §4. Get this
   compiling with Phase 2/3 as a total no-op stub.
2. `Horn/Types.hs` (`qWVars` field or equivalent), `Horn/Parse.hs`
   (`(wvar ...)` declaration parsing — reuse `hVarP`), `Horn/Info.hs`
   (populate `ws`/`wVars` from `qWVars`, reusing `hornWfs`/`kvInfo`/`kvApp`
   basically unchanged). Confirm `wvar_tests/*.smt2` (with `$`-prefixed
   w-var names added) parse successfully end to end, producing a `SInfo`
   with the right `ws`/`wVars` contents — good milestone/smoke-test before
   touching the solver at all.
3. Sanitize-time validation: weak kvars never appear as a constraint RHS;
   (maybe) no symbol declared both strong and weak.
4. Phase 1 seeding tweak in `Solve.hs`/`solve`'s `s0` construction (§5) +
   removal tracking instrumentation in `refineC`/`refine` + forcing every
   w-var into the cut set so Eliminate/"Fusion" never tries to substitute
   one away (§5's new bullet on this). Confirm existing k-var-only test
   suite (`tests/pos`, `tests/neg`, `tests/elim`, etc.) is fully unaffected
   (should be, since the whole point is zero logic changes for the
   k-var-only path).
5. Research UNSAT-core support (open question #1), then implement **case
   (b) only** (k-var strengthening via a w-var's WP) per the simplified
   "assume + minimize" strategy (or the doc's original per-qualifier-check
   strategy if UNSAT cores turn out to be a bigger lift than expected).
   Reasonable first cut within this step: get **one** bundle per failing
   constraint working end to end (single UNSAT core, no enumeration, no
   fewest-w-vars ranking yet) before layering on step 5b. Case (a) (direct
   w-var-solves-the-head, the dot-product scenario) is explicitly deferred
   past this milestone.
5b. Extend step 5 to actually satisfy Cole's stated goal (this is wanted,
    not deferred — see §5's "Minimize w-var count, and enumerate multiple
    candidate solutions" bullet): enumerate **multiple** candidate bundles
    per failing constraint and rank/flag the one using the fewest distinct
    w-vars as preferred. Needs its own design pass on the enumeration
    mechanism (bias minimization per-w-var-group vs. block-and-re-solve vs.
    both — options sketched in §5, not yet chosen).
6. Wire `resWVars :: HashMap SubcId [HashMap WVar Expr]` through end to end
   (JSON output, `--save`, etc.), including the "plain Safe/no extra info
   when nothing failed" short-circuit.
7. Turn `wvar_tests/*.smt2` into real regression tests. The two
   k-var-strengthening files (`failures.mwe-*.smt2`) should be usable as
   soon as step 5 lands. The dot-product file exercises case (a) only (no
   k-var interaction at all, per Cole) — it will not pass until that
   deferred case is implemented; track it as a known-failing/xfail fixture
   until then rather than expecting it to pass alongside the others.
8. Implement case (a) (direct w-var-solves-the-head) as a follow-up;
   un-xfail the dot-product test.
9. **(Explicitly OK to defer per Cole, but don't lose track of it)** prune
   vacuous bundles before reporting them: drop any bundle where a computed
   w-var solution is trivially `PFalse`/unsatisfiable, and drop any bundle
   that would create a contradiction in some *other* constraint guarded by
   one of its w-vars (a global consistency check across all of that
   w-var's obligations, not just the failing head the bundle was derived
   from). See §5's bullet on this for the two concrete degenerate cases to
   filter.
10. Partitioning question (§6.2) — resolve and implement whichever
    mitigation gets picked.

---

## 8. Condensed research notes (so a fresh context doesn't need to re-derive these)

- `KVar` type: `newtype KVar = KV { kv :: Symbol }`, `Types/Refinements.hs:220-231`.
- `GInfo`/`FInfo`/`SInfo`: `Types/Constraints.hs:744-760` (`FI` record),
  `FInfo a = GInfo SubC a`, `SInfo a = GInfo SimpC a` (`Constraints.hs:728-729`).
  Only **one** positional (non-record-syntax) construction site for `FI` in
  the whole repo: `Parse.hs:1405` (`defsFInfo`) — irrelevant now since flat
  `.fq` is out of scope. Everything else (`fi` smart ctor, `Semigroup`,
  `Monoid`, `Horn/Info.hs`'s `hornFInfo`, `Solver.hs`'s `parseFI`,
  `convertFormat`, `Defunctionalize.hs`, `EnvironmentReduction.hs`,
  `Graph/Partition.hs`, `Graph/Deps.hs`'s `slice`) touches `GInfo` only via
  record update/accessors, so adding `wVars` is safe/mechanical everywhere.
- `Result`: `Constraints.hs:265-271`. `ToJSON (Result a)` is **hand-written**
  (`Constraints.hs:304-311`), doesn't auto-include new fields — must add
  `"wVars" .= resWVars r` explicitly. 4 positional `Result` construction
  sites need a 5th arg: `Constraints.hs:326,334` (`Semigroup`/`Monoid`),
  `Solver.hs:196,209` (`crashResult`/`crashResultOther`).
- Core solve loop: `solve` → `solve_` → `refine` (worklist-draining loop) →
  `refineC` (single-constraint SMT-filter step) → `S.update`
  (`Solver/Solve.hs:62-282`, `Types/Solutions.hs:85-104`). `refineC`'s
  `rhsCands`/`predKs` (`Solve.hs:272-282`) is what determines which KVars
  get shrunk — driven entirely by `F.crhs c` (the constraint's RHS), never
  its LHS/environment. This is *why* seeding a weak kvar's QBind to
  `[trueEqual]` and never touching it again works for free, as long as we
  guarantee (validate) it never appears as an RHS.
- `Sol`/`QBind`/`EQual`: `Types/Solutions.hs`. `Sol { sMap :: HashMap KVar
  QBind, sHyp, sScp }` (line ~138). `trueEqual :: EQual` already exists
  (line ~237-238). `update :: Sol QBind -> [(KVar,QBind)] -> (Bool, Sol
  QBind)` (line ~95) only compares `QBind` *sizes* to report "changed" —
  actual removed `EQual`s are currently discarded, confirming removal
  tracking needs new (additive) instrumentation, nothing to reuse.
- `lhsPred`/`apply`/`applyKVar`/`qbPreds`: `Solver/Solution.hs:273-367`. This
  is the *only* place `PKVar` nodes get expanded/resolved (via `Sol.lookup`
  → either `Left cs` for non-cut/hypothesis kvars or `Right eqs` for
  cut-kvar `QBind`s) before an `Expr` is handed to `filterValid`/SMT.
  Confirmed via `Smt/Serialize.hs:170-216` (`instance SMTLIB2 Expr`) that
  `PKVar` is never handled there and panics (`smt2 e = panic (...)`) if an
  unexpanded one ever reached it — i.e. today's invariant is "every `PKVar`
  is fully resolved before touching the SMT layer," which is exactly what
  we get for free for weak kvars too by seeding them to `[trueEqual]`.
- `Solver/Monad.hs`: `SolveM ann = StateT (SolverState ann) IO`,
  `SolverState { ssCtx :: Context, ssStats, ssElabParam }` (lines 60-70).
  `runSolverM` (lines 77-93) opens exactly one SMT `Context` via `bracket`
  around the whole `solve_` call — any new Phase 2/3 code running inside
  `SolveM` reuses this same live SMT process, no new context needed.
  `filterValid`/`filterValid_` (lines 174-195) is the SMT-validity-check
  primitive (`assert p; assert (not q); check-sat`), reusable as-is for
  Phase 2/3's implication checks.
- `Worklist.hs`: worklist entries are *constraints* (not kvars directly),
  seeded from `M.toList cm` partitioned by `isConcC` (`Worklist.hs:87-110`,
  103-109) — i.e. only constraints whose RHS is a kvar go on the worklist at
  all. `push` (`Worklist.hs:148-160`) re-adds a constraint's *dependents*
  (from a precomputed `wDeps`/`CSucc` map) only when `refineC` reports a
  change. Nothing here needs to change for weak kvars, provided they never
  appear as an RHS (see validation point above).
- Horn front-end pipeline: `.smt2` text → `H.hornP` (`Horn/Parse.hs`) →
  `H.Query a` → (optional kvar elimination, `Horn/Transformations.hs`/
  `Horn/Solve.hs:83-93`) → `hornFInfo` (`Horn/Info.hs:20-33`) → `F.FInfo a` →
  (generic, Horn-agnostic) `convertFormat`/`subcToSimpc` → `F.SInfo a` →
  `Solver.solve`.
  - `H.Var`/`HVar { hvName :: Symbol, hvArgs :: [Sort], hvMeta :: a }`
    (`Horn/Types.hs:56-61`) — declaration, sorts only, no param names.
  - `H.Pred = Reft Expr | Var Symbol [Expr] | PAnd [Pred]`
    (`Horn/Types.hs:68-72`) — `Var` here is the **occurrence** node
    (unfortunate name clash with the declaration type `Var`/`HVar` above,
    same identifier different constructor/type).
  - `kvSymP = char '$' *> symbolP` (`Horn/Parse.hs:209-210`) — the `$`-marker
    parser, used identically at both declaration (`hVarP`) and occurrence
    (`hPredP`'s `H.Var <$> kvSymP <*> some exprP`, `Horn/Parse.hs:200-205`)
    sites. `$` is **lexically required** here (not just convention) because
    `symbolP`'s underlying `symbolR` (`Parse.hs:709-711`) requires an
    alpha/`_` first character, so a bare `symbolP` can never itself produce
    a `$`-leading name — only `kvSymP`'s manual `char '$' *>` prefix can.
    This is exactly why giving w-var names the same `$` marker means
    occurrence parsing needs zero new code (§3).
  - Naming/param-invention for positional→named substitution conversion:
    `hornWfs`/`kvInfo` (`Horn/Info.hs:116-157`) builds a `KVEnv = HashMap
    Symbol KVInfo` **once per query**, synthesizing formal parameter names
    via `hvarArgSymbol :: Symbol -> Int -> Symbol` (`Types/Names.hs:499-500`,
    produces names like `nnf_arg$##k0##0`), splitting off arg-0 as the
    distinguished "self"/value-variable for the `WfC`
    (`Misc.safeUncons`). `kvApp kve k ys = F.PKVar (F.KV k) M.empty (mkKVarSubst
    (zip (kvParams info) ys))` (`Horn/Info.hs:101-113`) is the actual
    positional-args → `PKVar` conversion, looking up cached names from
    `KVEnv`. **Plan: reuse this whole mechanism verbatim for `qWVars` too**
    (just also fold `qWVars` into the same `KVEnv`/`ws` construction).
  - `hornSubCs`/`goS'` (`Horn/Info.hs:49-99`) walks the `Cstr`/`forall` tree;
    a `Bind`'s guard predicate (of any shape — concrete, kvar-application,
    conjunction) becomes one `SortedReft`, inserted as one new `BindId` via
    `insertBindEnv`, whose id joins the `IBindEnv` threaded into the nested
    body. **Kvar-guards (and thus weak-kvar-guards) get no special treatment
    at all here** — they ride along purely because `SortedReft`'s
    refinement field is a plain `Expr` that happens to support `PKVar`.
    Confirms: no changes needed to `hornSubCs`/`goS'`/`IBindEnv`/`BindEnv`
    for weak kvars to "just work" structurally.
  - Sort grammar (`Horn/Parse.hs:291-308`, `sortP`): nullary type
    constructors (primitives like `int`/`bool`, or bare `UpperCaseIdent`)
    can be written unwrapped; the *only* production that consumes ≥1
    argument sorts requires parens, so a datatype like `Adt0` used with 0
    args can legally appear either bare or `(Adt0)`-wrapped — purely a
    stylistic/emitter choice, not w-var-specific, confirmed by existing
    `tests/horn/pos/*.smt2` fixtures showing both forms for ordinary k-var
    declarations too.
