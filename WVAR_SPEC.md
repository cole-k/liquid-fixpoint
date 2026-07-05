# W-Variables in liquid-fixpoint: Implementation Spec

**Audience:** someone with no prior context on this feature (and only passing
familiarity with liquid-fixpoint) who wants to understand what was built and,
if needed, reimplement it. It supersedes the exploratory notes in
`WVAR_IMPLEMENTATION_PLAN.md` / `WVAR_ALGORITHM.md` where they differ.

Read sections 0-2 for the mental model, 3-8 for the mechanics, 9 for the
worked example, 10 for the hard-won correctness lessons, 11 for the file map.

--------------------------------------------------------------------------------
## 0. Background: how liquid-fixpoint solving works (the parts you need)

liquid-fixpoint takes a set of **Horn constraints** and decides `Safe`/`Unsafe`.
Constraints contain unknown predicates called **k-vars** (`$k0`, `$k1`, ...).
A k-var is an applied predicate `$k0(e1, e2, ...)`; solving means finding a
concrete predicate for each k-var so that every constraint holds.

Key vocabulary and machinery (Haskell names in `src/Language/Fixpoint`):

- **Constraint** (`SimpC a`, a.k.a. "subc"): has a **left-hand side** (LHS /
  "body" / "environment": a conjunction of facts and k-var applications that are
  *assumed*) and a **right-hand side** (`crhs`, the **head**: what must be
  *proved*). A head is either a concrete predicate (e.g. `a0 = m`) or a k-var
  application (e.g. `$k0(a1, m)`). `subcId :: SubcId (= Integer)` identifies it.
  - `V.envKVars be c` = the k-vars occurring in `c`'s LHS.
  - `V.rhsKVars c`    = the k-vars occurring in `c`'s head.
  - `F.crhs c`        = the head expression.

- **Qualifier / `EQual`**: candidate atomic facts (`a0 = a1`, `a0 >= 0`,
  `a0 = 0`, ...) that a k-var's solution is built from. `(qualif ...)` lines in
  the input, plus auto-scraped ones. An `EQual` is a qualifier *instantiated for
  a particular k-var's formal parameters*; `Sol.eqPred :: EQual -> Expr` is its
  predicate.

- **Solution** (`Sol.Solution`): maps each (cut) k-var to a `QBind` = a list of
  `EQual`s; the k-var's meaning is the conjunction of their predicates. Helpers:
  `Sol.lookupQBind`, and `applyKVar`/`lhsPred` expand k-var applications in a
  constraint's LHS under the current solution.

- **The fixpoint** (`Solver/Solve.hs`): starts each k-var at the *strongest*
  candidate set (all qualifiers) and **weakens** it. `refineC` processes one
  constraint: for each k-var `k` in the head, it keeps only the qualifiers `Q`
  such that `lhsPred(c) => Q@head` (checked by SMT via `filterValid`). Qualifiers
  that fail are **dropped** ("stripped"). This repeats to a fixpoint. Then each
  concrete head is checked; if some fail, the result is `Unsafe`.

- **`lhsPred cfg scope bindings be sol c`** builds the constraint's LHS predicate
  as one `Expr`, expanding every k-var application under `sol`.

- **Cut k-vars / elimination**: for efficiency, non-"cut" k-vars are eliminated
  (substituted away) before solving. `Deps.hs` computes the cut set.

If any of the above is unfamiliar, skim `Solver/Solve.hs` (`solve`, `solve_`,
`refine`, `refineC`) and `Types/Solutions.hs` (`Sol`, `QBind`, `EQual`) first.

--------------------------------------------------------------------------------
## 1. What a w-var is, and the core idea

A **w-var** ("weak k-var", `$w`) is an unknown predicate declared with
`(wvar $name (arg-sorts))` — same shape as `(var $k ...)`. Semantically it should
be solved to the *weakest* predicate that keeps the system satisfiable. It is a
**guard**: it appears in constraint *bodies* (LHS), like `... /\ $w(x, y) /\ ... => head`.

The idea, in one paragraph:

> Pretend every w-var is `true` and solve normally. With the guard `= true` the
> w-guarded constraints are "fully on", which can **over-constrain** the k-vars
> and make some head fail (→ `Unsafe`). When a head fails, ask: *which
> qualifiers, stripped from the k-vars during solving by w-guarded constraints,
> would — if kept — make the head pass again, and can we hold the w-var
> responsible for keeping them?* If we strengthen `$w`, its guarded constraints
> fire less often, so those qualifiers can survive. We report, per w-var, a
> **weakest precondition (WP)**: the strongest thing `$w` may be, over its own
> arguments, that lets the needed qualifiers survive.

This is **diagnostic only**: the verdict stays `Unsafe`. We do not change the
solution; we report candidate w-var solutions the user (e.g. Flux) can adopt.

**AST representation decision:** a w-var occurrence is a plain `PKVar` node —
identical to a k-var. The *only* thing distinguishing weak from ordinary is
membership in a new set `GInfo.wVars :: HashSet WVar`. There is deliberately **no
new `Expr` constructor** (that would touch ~40 pattern-match sites). Everywhere a
w-var must behave differently from a k-var, the code consults `wVars`; everywhere
else "w-var = k-var" is correct.

Scope note: only the Horn/`.smt2` path is in scope; the flat `.fq` path is
untouched. A w-var is assumed to occur **only in body** position or **only in
head** position (not both); the "both" case (which arises from recursive
functions) is not handled — we warn and treat it as an ordinary k-var.

--------------------------------------------------------------------------------
## 2. Glossary (terms used below)

- **strip / drop a qualifier**: `refineC` removing a qualifier `Q` from a k-var
  because the current LHS doesn't imply it.
- **w-guarded constraint**: a constraint whose LHS contains a w-var occurrence.
- **`$w` saves `Q` (on constraint `c'`)**: strengthening `$w` can make `Q`
  survive on `c'` — formally, `$w`'s WP for `Q` on `c'` is non-vacuous.
- **WP (weakest precondition) of `$w` for `Q` on `c'`**:
  `∀(vars of `c'`'s LHS that are NOT `$w`'s arguments). LHS(c') => Q@head`.
  This is the *weakest predicate over `$w`'s argument scope* that forces `Q`.
- **vacuous**: a formula that is unsatisfiable (or only satisfiable by falsifying
  the guard on the whole reachable domain) — i.e. not a real fix.
- **`Q@head`**: the qualifier `Q` (over k-var formal params) instantiated at a
  particular head's actual argument expressions.

--------------------------------------------------------------------------------
## 3. Behavior and the `--wvars` flag

- **`--wvars`** (off by default) gates **only the diagnostic analysis** (Phase 2:
  finding and reporting candidate w-var solutions). It never changes the verdict.
- **Unconditionally** (flag on or off) a body-only w-var is treated as `true`
  (see Phase 1 below). Rationale: a w-var must not be accidentally *solved* like
  an ordinary k-var (which would make guarded constraints trivially satisfiable
  and give a wrong `Safe`). So the "pretend true" semantics is always on; only
  the extra analysis is gated.
- With `--wvars` and an `Unsafe` verdict, candidate solutions are computed, put
  in `Result.resWVars`, printed, and included in `--json`.

"Passing" the `wvar_tests/failures.mwe-*` fixtures means: they stay `Unsafe`
(exit 1) but `resWVars` is populated with the right rescue (verify via the
printed summary / `--json`), NOT that they flip to `Safe`.

--------------------------------------------------------------------------------
## 4. Data model  (`Types/Constraints.hs`, `Solver/Monad.hs`)

```haskell
newtype WVar = WV { wv :: Symbol }              -- mirrors KVar
wvarKVar :: WVar -> KVar ; kvarWVar :: KVar -> WVar   -- same underlying Symbol

data GInfo c a = FI { ...; wVars :: !(HashSet WVar) }  -- which ws-entries are weak

data WVarFix = WVarFix { wfSolution :: !Expr    -- candidate WP solution (may be quantified)
                       , wfDrops    :: ![Expr] } -- the per-drop WP conjuncts it was built from
type WVarResult = HashMap WVar WVarFix
data Result a  = Result { ...; resWVars :: !WVarResult }  -- diagnostic; only when Unsafe & --wvars

-- Phase-1 provenance, recorded in Solver/Monad.hs's SolverState (ssWDrops):
data WDrop = WDrop { wdWVars :: ![WVar]  -- w-vars guarding the dropping constraint
                   , wdCid   :: !SubcId  -- the dropping constraint
                   , wdKVar  :: !KVar    -- the k-var Q was dropped from
                   , wdHead  :: !Expr    -- Q instantiated at that head (Q@head)
                   , wdEQual :: !EQual } -- the raw qualifier (to re-add to the k-var)
```

All `Semigroup`/`Monoid`/`ToJSON`/`FromJSON`/`NFData`/`Store`/`PPrint` instances
for `WVar`/`WVarFix` and the new `GInfo`/`Result` fields; every positional
`FI`/`Result` construction site updated (search for them if reimplementing;
there are a handful, incl. `Parse.hs:defsFInfo`, `Solver.hs:crashResult*`,
`Solve.hs:result`).

--------------------------------------------------------------------------------
## 5. Parsing & lowering  (`Horn/{Types,Parse,Info}.hs`)

- `Query.qWVars :: [Var a]` — new field, populated like `qVars`.
- Parser: new `HThing` variant `HWVar`, alternative
  `<|> HWVar <$> (reserved "wvar" *> hVarP)` in `hThingP`. `hVarP` (the
  `(var ...)` parser) is reused verbatim. **Occurrences need no new grammar**:
  `($w e1 e2)` already parses via the existing `H.Var <$> kvSymP <*> some exprP`
  rule — a w-var name is just a `$`-prefixed symbol like any k-var.
- `hornFInfo` folds `qWVars` into the *same* `KVEnv`/`ws`/WfC construction as
  `qVars` (so w-var occurrences lower to `PKVar` nodes and get a WfC/scope), and
  records the weak names: `F.wVars = fromList [kvarWVar (KV (hvName w)) | w <- qWVars]`.

Fixture note: the CHC generator emits w-var names *without* a leading `$` and
occurrences with an extra paren pair. The `wvar_tests/*.smt2` fixtures were
edited to add the leading `$` (required by `kvSymP`) and use single-paren
`($w ...)` occurrences. If you regenerate fixtures, apply the same normalization
(or teach the parser the other forms).

--------------------------------------------------------------------------------
## 6. Phase 1: the real solve  (`Solver/Solve.hs`, `Graph/Deps.hs`, `Solver.hs`, `Solver/WVar.hs`)

All of this is about making a w-var behave as `true` and capturing the raw
material for Phase 2. None of it changes the verdict beyond "w-vars are true".

1. **Classify** (`Solver/WVar.hs`, `classifyWVars`): from the `SInfo`, split
   declared w-vars into `body-only` / `head-only` / `both` using
   `envKVars`/`rhsKVars`. `bodyOnlyWVars` = the ones we act on.

2. **Elide head-only, warn on both** (`Solver.hs`, `prepareWVars`, runs always):
   - head-only w-vars are never read, so their constraints are trivially
     satisfiable → strip their `PKVar` from heads and remove them from
     `ws`/`wVars` (they vanish).
   - both-position w-vars → print a `WARNING` (`Misc.colorStrLn Wary`) and leave
     them to behave as ordinary k-vars.

3. **Seed body-only w-vars to `true`** (`Solve.hs`, `s0` construction): set
   `sMap[k] = QB [trueEqual]`. Because `applyKVar` dispatches on "has a QBind"
   and `trueEqual`'s pred is `PTrue`, the w-var contributes `true` to any LHS.
   Since a body-only w-var never appears as a head, `refineC` (which only
   refines head k-vars) never touches it — it stays `true`.

4. **Keep them out of elimination** (`Deps.hs`, `edgeDeps`): union the w-vars
   into the forced cut set so kvar-elimination never tries to substitute them.
   (Purely a Phase-1 mechanism; it is *not* a claim that w-vars are cut vars —
   Phase 2 does not treat them as such.)

5. **Capture drops** (`Solve.hs`, `refineC` → `captureWDrops`, gated by
   `wvars cfg`): at the exact point `refineC` drops candidate qualifiers from a
   head k-var `k` on constraint `c`, for each dropped `(qPred, eq)` record a
   `WDrop` with the w-vars guarding `c` — **unless** the qualifier is *vacuous*
   at `c` (`lhs /\ qPred` unsat, i.e. `lhs => not qPred`): a `Q` that contradicts
   its own body can never be rescued by any strengthening of a guard, so it is
   not recorded. This is the only place the "responsible constraint" is known
   for free, so we capture it here.

--------------------------------------------------------------------------------
## 7. Phase 2: diagnostic w-var solving  (`Solver/WVarSolve.hs`)

Entry: `solveWVars cfg scope fi sFinal failCs`, called from `Solve.hs:solve_`
when `--wvars` and the verdict is `Unsafe`. `sFinal` is the final solution;
`failCs` are the failing (concrete-head) constraints. It returns a `WVarResult`.

### 7a. Seed the "reclaimed set"

```haskell
type RQual     = (KVar, EQual)              -- a qualifier attributed to a k-var
type Reclaimed = [(RQual, HashSet WVar)]    -- each qualifier tagged with the w-vars that *might* save it
```

Seed from the captured `WDrop`s (deduped by `(kvar, eqPred)`, savers unioned),
**restricted to k-vars that appear in some failing head's LHS** (only those can
matter for the report — this also keeps the work small).

### 7b. The reclaimed-qualifier fixpoint (`fixReclaimed`)

A reclaimed qualifier must "survive" the constraints where its k-var is a head,
the same way a normal qualifier must — **but with a relaxed rule**. For each
`(k, Q)` and each constraint `c'` with `k` in its head (`headConstraints k`),
let `Q@head` be `Q` instantiated at that head, and `lhs = lhsPred(sFinal, c')`:

- if `lhs => Q@head` (SMT `isValid`): survives here via the LHS; **all** its
  savers are still OK for this constraint.
- else: keep only the savers `w` that **can prove `Q` there** (`canSave`, below);
  a saver that can't is dropped from `Q`'s tag.
- a `Q` whose saver set becomes empty is removed from the reclaimed set.

`canSave w c' lhs qHead`: `w` must guard `c'` (occur in its LHS), and its WP
there — `mkWP` = `∀(LHS vars not among w's args). lhs => qHead` — must be
**non-vacuous** (satisfiable together with the domain `lhs`). This is exactly the
check that drops an *ambient* w-var: e.g. `$w_simplex(m)` guards the recursive
constraint but only sees `m`; its WP for `a1 = m` universally-quantifies `a1`
(∀a1. ... => a1=m), which is vacuous, so `$w_simplex` is dropped from that
qualifier's tag.

Two subtleties that are load-bearing (see §10):
- The survival LHS uses **`sFinal`**, *not* a solution enhanced with the
  reclaimed qualifiers. The reclaimed set is a *union of possibilities from
  different w-vars* and is often self-inconsistent; enhancing the LHS with it
  would make the LHS `false` and vacuously imply everything.
- Because the check depends only on the fixed `sFinal`, it is **idempotent — one
  pass is the fixpoint** (`fixReclaimed = stepReclaimed`; no iteration).

### 7c. Reporting (`reportCandidates`, `growHead`)

For each failing head `h` and each w-var `w`:
1. `quals` = reclaimed qualifiers `w` still saves whose k-var is in `h`'s LHS.
2. `growHead`: find a **consistent** subset of `quals` that, added to their
   k-vars, makes `h` valid. Greedy with backtracking: add a candidate only if it
   keeps the enhanced LHS *satisfiable* (`headLhsSat`) — never "prove" `h` by
   piling on contradictory qualifiers that make the k-var `false`
   (`headValid` = `lhsPred(enhanced, h) => crhs h`). Bounded by a solver-call
   budget (`IORef Int`, currently 2000) so a hard head cannot blow up the
   O(n²)-ish search; hitting the budget only loses the diagnostic, never affects
   the verdict.
3. For each qualifier in that subset, emit `w`'s WP at each guarded
   head-constraint (`wpAt`, using `mkWP`).

### 7d. QE-simplify and finalize

The reported WPs are generally quantified. Simplify each with Z3 quantifier
elimination (§8), then drop any conjunct that is *vacuous with its domain*
(satisfiable check). Group per w-var → `WVarFix` → `WVarResult`.

--------------------------------------------------------------------------------
## 8. Weakest precondition + quantifier elimination

### The WP and the scope-mismatch problem

A w-var `$w(x, y)` can only "see" its own arguments `x, y`. A qualifier we want
it to force may mention other variables — e.g. we need `$k0`'s qualifier
`arg0 = arg1` to survive the recursive constraint, which at that head means
`a1 = m`; but the constraint also binds `a0` (a `forall`-bound variable). So the
solution for `$w` must be the strongest predicate *over just `x, y`* that, given
the constraint's context, guarantees the qualifier — which requires
**quantifying out** the other (inner) variables. That is the WP:

```
mkWP w c' lhs qHead
  = ∀ (freeVars(lhs => qHead) \ argsOf(w in c'))_fresh . lhs => qHead
```

`argsOf(w in c')` = the actual argument variables of `w`'s occurrence in `c'`
(read off the `PKVar`'s substitution; `wvarArgSyms`). The quantified variables
are alpha-renamed to fresh names (`fresh x = suffixSymbol x "wvq"`) so they can
never capture `w`'s free argument variables — important because the non-vacuity
check conjoins the WP with the raw `lhs` (which still mentions those variables).

### QE plumbing (`Smt/Interface.hs`, new `Smt/Parse.hs`)

Z3 can eliminate the `∀`. But this needed new SMT plumbing (there was no way to
get a *formula* back from the solver; only sat/unsat/values):

- `qe :: Expr -> SmtM Expr` sends `(apply (then qe ctx-solver-simplify))` and
  parses the `(goals (goal <F> ...))` result back into an `Expr` via the new
  **`Smt.Parse`** attoparsec parser. The parser handles boolean/relational/
  arithmetic ops, function applications, integer literals (incl. negative
  `(- n)`), `let` (expanded by substitution), `true`/`false`, `as`/`_`, and
  **decodes `symbolSafeText`-encoded symbol names** back to raw `Symbol`s.
- `qeMany :: Config -> [Expr] -> IO [Expr]` runs `qe` per formula in a **fresh,
  isolated** Z3 context. This isolation is mandatory: Z3's `(apply qe)` operates
  on the *entire* assertion set, so running it in the live solver context would
  eliminate quantifiers over the solver's ambient assertions and produce garbage.
- `qeManyD :: Config -> SymEnv -> DefinedFuns -> [Expr] -> IO [Expr]` — the
  **datatype-aware** variant used by the w-var analysis. It populates the fresh
  context from the full `SymEnv` (+ `DefinedFuns`) so `declare-datatypes` is
  emitted and Z3's QE can reason about **ADT selectors** (e.g. dotprod's
  `fld0$0`). In this mode `qe` does **not** self-declare free symbols (the
  `SymEnv` already declares everything), avoiding "already declared" conflicts
  (a `qeWith' declareFree` flag toggles this).
- MBQI: the solver preamble disables MBQI (good for the QF Phase-1 checks). The
  diagnostic phase re-enables it (`smtEnablembqi`) because its checks are
  quantified. **But** the hot-path non-vacuity check avoids MBQI by doing
  QE-then-quantifier-free-sat instead (QE is ~ms; a quantified MBQI query was
  ~0.5s). If QE cannot eliminate the quantifier (genuinely uninterpreted
  functions), `canSave` conservatively keeps the saver.

--------------------------------------------------------------------------------
## 9. Worked example: `wvar_tests/failures.mwe-wkvar_kvar_interaction-simplex.smt2`

The single constraint (paraphrased), with two w-vars and one k-var `$k0(x0,x1)`:

```
  $w_simplex(m) /\ m>=0  =>            -- guards everything below
    $k0(m, m)                          -- (base)     head: k0(m,m)
    /\ ( $k0(a0, m)  =>                -- for all a0
           a0 = m                      -- (tag)      the FAILING concrete head
           /\ ( a1>=0 /\ $w_row_op(a1, m) => $k0(a1, m) ) )  -- (rec) head: k0(a1,m)
```

**Phase 1 (w-vars = true).** `$k0` gets weakened. The base wants `arg0=arg1`.
The recursive step concludes `$k0(a1,m)` from `$k0(a0,m) /\ a1>=0` (with the
guards = true) — so for `arg0=arg1` to survive there we'd need `a1=m`, but `a1`
only satisfies `a1>=0`. So `arg0=arg1` (and friends) are **stripped** from `$k0`
by the recursive constraint. `$k0` ends up too weak → the **tag** head
`$k0(a0,m) => a0=m` fails → `Unsafe`. Drops recorded: e.g. `arg0=arg1`,
`arg0>=arg1`, `arg0<=arg1` off `$k0`, each tagged with the w-vars guarding the
constraint that dropped them (`{$w_simplex, $w_row_op}` for the recursive one;
`{$w_simplex}` for base-case drops like `arg0>0`).

**Phase 2 — reclaimed fixpoint.** Consider `arg0=arg1` (recursive drop, savers
`{$w_simplex, $w_row_op}`). Re-check it on `$k0`'s head constraints:
- recursive constraint, `Q@head = (a1=m)`: `lhs => a1=m`? No. Can savers prove
  it? `$w_row_op(a1,m)` sees `a1` → WP `∀a0. lhs => a1=m` is non-vacuous → kept.
  `$w_simplex(m)` does NOT see `a1` → WP `∀a0 a1. lhs => a1=m` is vacuous →
  **`$w_simplex` dropped from this qualifier's tag.**
So the qualifiers that actually fix the tag end up saved only by `$w_row_op`.

**Phase 2 — report.** For the tag head and `$w_row_op`: a consistent subset of
`{arg0>=arg1, arg0<=arg1}` on `$k0` makes the tag valid (together they give
`a0=m`). WP of `$w_row_op` from the recursive constraint:
`∀a0. (a0>=0 /\ m>=0 /\ a1>=0) => a1=m`, which QE simplifies to `(a1>=0 /\ m>=0) => a1=m`.

**Output:** exactly
```
$w_row_op := (a1>=0 && m>=0) => a1=m
```
and *nothing* for `$w_simplex` (it was correctly pruned). This is the genuine
rescue: with `$w_row_op(a1,m) := a1=m`, the recursive step only fires for `a1=m`,
so `arg0=arg1` survives on `$k0` and the tag holds.

--------------------------------------------------------------------------------
## 10. Correctness lessons (things that are subtle — and that we got wrong first)

If you reimplement, these are the traps, each of which cost real debugging:

1. **A local "does this head prove?" check is NOT sound on its own.** Re-adding
   qualifiers to a k-var and checking only the *failing* head can accept a
   w-var solution that is globally invalid (e.g. `$w_simplex := m<=0`, which
   passes the tag locally but leaves the system unsat). The reclaimed fixpoint's
   *per-constraint saver check* (`canSave` across all head-constraints of the
   k-var) is what makes it sound. Do not skip it.

2. **Vacuity is not "is `Q` consistent with the domain".** `$w := m<=0` is
   satisfiable at `m=0`, so a naive "satisfiable with domain" check keeps it.
   The right notion is the *WP's* non-vacuity: quantify out the variables the
   w-var can't see; if that collapses to `false`, the w-var can't provide `Q`.

3. **Vacuity is a LOCAL property; check it at drop time.** A qualifier that
   contradicts its own constraint's body (`lhs /\ Q` unsat) can never be rescued
   by strengthening a guard (strengthening only shrinks the guard, never
   resolves a contradiction). Filter these when capturing drops.

4. **Don't enhance the survival-check LHS with the reclaimed set.** The reclaimed
   set unions possibilities across w-vars and is often self-inconsistent; adding
   it to the LHS makes the LHS `false`, which vacuously "implies" every
   qualifier. Use the real `sFinal` for the survival LHS.

5. **When building the maximal head-proving qualifier set, require the enhanced
   LHS to stay satisfiable.** Otherwise contradictory qualifiers make the k-var
   `false` and the head is "proved" vacuously.

6. **"Skip the saver check when there's only one saver" is UNSOUND.** It looks
   like a safe optimization (nothing to disambiguate) but it lets an ambient
   single-guard w-var carry qualifiers it can't actually provide. Keep the check
   for all savers; make it cheap via QE instead (lesson 7).

7. **QE, not MBQI, for the non-vacuity check** — and **QE must be
   datatype-aware.** MBQI on the quantified WP was ~0.5s/query. Eliminating the
   quantifier first, then a QF sat check, is ~ms. And the fresh QE context must
   be given the datatype declarations (`qeManyD`), or ADT selectors degrade to
   uninterpreted functions and QE can't eliminate.

8. **`--wvars` off must still pin w-vars to `true`.** If instead you let a w-var
   be solved as an ordinary k-var, guarded constraints become trivially
   satisfiable and you get a wrong `Safe`. Only the *analysis* is flag-gated; the
   "true" semantics is unconditional.

--------------------------------------------------------------------------------
## 11. File map (where everything lives)

| Concern | File(s) | Key names |
|---|---|---|
| `WVar` type, `GInfo.wVars`, `Result.resWVars`, `WVarFix` | `Types/Constraints.hs` | `WVar`, `wvarKVar`, `kvarWVar`, `WVarFix`, `WVarResult` |
| `--wvars` flag | `Types/Config.hs` | `wvars`, `opt0 "wvars"` |
| Parse `(wvar ...)` | `Horn/Types.hs`, `Horn/Parse.hs` | `qWVars`, `HWVar` |
| Lower to `ws`/`wVars` | `Horn/Info.hs` | `hornFInfo` |
| Classify / elide / warn | `Solver/WVar.hs` | `classifyWVars`, `bodyOnlyWVars`, `elideOnlyHeadWVars` |
| Seed-true + drop capture | `Solver/Solve.hs` | `s0`, `refineC`, `captureWDrops` |
| Drop provenance state | `Solver/Monad.hs` | `WDrop`, `ssWDrops`, `recordWDrops`, `getWDrops` |
| Elimination exclusion | `Graph/Deps.hs` | `edgeDeps` |
| Classify+warn at solve entry | `Solver.hs` | `prepareWVars`, `solveNative'` |
| Phase 2 analysis | `Solver/WVarSolve.hs` | `solveWVars`, `fixReclaimed`, `canSave`, `mkWP`, `reportCandidates`, `growHead` |
| QE + parser | `Smt/Interface.hs`, `Smt/Parse.hs` | `qe`, `qeMany`, `qeManyD`, `Parse.parseGoals` |
| Report printing / JSON | `Solver.hs`, `Types/Constraints.hs` | `printWVarFixes`, `ToJSON (Result a)` |
| Fixtures | `wvar_tests/*.smt2` | simplex, depart_var (both k-var-strengthening), dotprod (direct-WP) |

Commit history (`git log --oneline a34ed38c..HEAD`) walks the build in order:
data model → parse → flag+seed-true → capture+WP → QE → relevance/vacuity →
reclaimed fixpoint → perf → datatype-aware QE.

--------------------------------------------------------------------------------
## 12. Current results

- **simplex**: `$w_row_op := (a1>=0 && m>=0) => a1=m` (only).
- **depart_var**: `$w_depart_var := i0>0 && i0<m`.
- **dotprod**: quantifier-free
  `$w := (fld0(n)>=0 => fld0(m)>0) && (fld0(n)>=1 => fld0(m)>fld0(n))`.
- All three run in ~0.5s wall (see the perf note below).
- k-var-only queries and the `--wvars`-off path are unaffected (regression:
  `tests/horn/pos` 50/50, `tests/horn/neg` 19/19; QE unit tests 50/50).

### 12.1 Performance: batched QE (2026-07)

The Phase-2 analysis calls the SMT solver in three places: `isValid`/`satisfiable`
(cheap, reuse the *live* solver process, ~ms each) and quantifier elimination
(`qeManyD`, previously the whole cost). The old bottleneck was **process
spawning, not QE math**: `qeManyD` created a *fresh Z3 process per formula*
(`makeContextWithSEnv`/`cleanupContext`), and the reclaimed-fixpoint issued one
QE per `canSave` check — dotprod did ~54, i.e. ~54 spawns ≈ 0.75s. Two fixes,
both behaviour-preserving (identical reported solutions):

1. **`qeManyD` reuses one context** for all formulas (`Interface.hs`). Safe
   because each `qeWith'` is already push/pop-isolated (`smtBracket`) and, with
   `declareFree=False`, declares nothing per formula — all symbols/datatypes come
   from the shared `SymEnv` set up once at context creation. Per-formula errors
   are recovered with `catchSMT`.
2. **`canSave` is precomputed and batched** (`WVarSolve.precomputeCanSave`). The
   check `canSave w c' Q` depends only on `(w, c', Q)` and the *fixed* final
   solution — **not** on the reclaimed set — so all triples' WPs are eliminated
   in a *single* `qeManyD` call up front, and the fixpoint's `survive` becomes a
   pure `CanSaveTbl` lookup (no SMT during iteration).

Net: dotprod `qeBatch 0.75s -> 0.15s`, `fix 0.78s -> 0.18s`, wall `1.15s -> 0.5s`.
The residual ~0.15s is genuine QE work over the ~54 WP formulas (inherent to the
algorithm: one non-vacuity check per reclaimed-qualifier × head-constraint ×
guarding-w-var), plus ~0.3s of `stack exec`/parse/solve overhead unrelated to
w-vars. Reporting is ~2ms and is **not** a source of slowness.

--------------------------------------------------------------------------------
## 13. Known limitations / natural next steps

- **Genuinely uninterpreted functions + QE**: ADT selectors are handled
  (`qeManyD`). Truly uninterpreted functions still defeat QE; we conservatively
  keep such savers and leave the reported WP quantified. **Ackermannization**
  (replace each distinct application `f(a)`, `f(b)` with fresh constants
  `f_a`, `f_b` plus functional-consistency `a=b => f_a=f_b`) would extend QE to
  those cases.
- **Report search is bounded by a budget** (`growHead` backtracks). The intended
  replacement is an **UNSAT-core-based** minimal-subset search: assert the
  candidate qualifiers as named soft assertions plus `¬head`, take the core.
  This needs `get-unsat-core` + `:named`-assertion plumbing that does not exist
  yet (the serializer already supports `Assert (Just i)`, but nothing constructs
  it and there is no `get-unsat-core` command/response).
- **Single-w-var-per-fix model.** Cooperative fixes needing several w-vars
  together, reporting *multiple* candidate bundles, and ranking by fewest w-vars
  are not implemented.
- **Both-position w-vars** (recursive functions) are warned and treated as
  ordinary k-vars.
- **Minimality/noise**: `growHead` returns *a* consistent head-proving set, not a
  minimal one, so reported solutions can carry redundant conjuncts.

### 13.1 Notes for the next session (2026-07)

- **Committed this session**: the batched-QE perf work (§12.1) — `qeManyD`
  single-context reuse + `precomputeCanSave`. Diff is the two files
  `Smt/Interface.hs` and `Solver/WVarSolve.hs`; all profiling instrumentation was
  removed before committing (no `time` cabal dep, no `Debug.Trace`/`Data.Time`).
- **NOT re-run this session**: the full `stack test` suite (it was slow to run to
  completion). The 3 `wvar_tests` fixtures were verified by hand (correct
  solutions, clean build, no stray output). Before relying on this, run at least
  `horn-pos-na`/`horn-neg-na` (native, no cvc5) to confirm the `qeManyD` change
  didn't regress anything — `qeManyD` has one other caller (the report-stage QE at
  `WVarSolve.hs` ~line 100), which also now benefits from single-context reuse.
- **Further QE reduction (optional)**: the remaining ~0.15s is ~54 genuine QE
  runs. Two easy wins if it matters: (a) in `precomputeCanSave`, skip triples
  whose LHS already implies `Q` (currently the WP is built for them anyway — an
  `isValid` pre-filter would trim the batch); (b) de-duplicate identical
  `(wp, dom)` formulas before the batch (many head-constraints share structure).
  Neither changes results.
- **Correctness reminder** (do not "optimize" these away): the survival LHS must
  be the *real* `sFinal`, never enhanced with the reclaimed set; and "skip the
  saver check when a constraint has a single guarding w-var" is **unsound** (it
  reintroduced a bogus `$w_simplex`). The batching preserves both because it
  computes exactly the same per-triple non-vacuity check, just in one process.
