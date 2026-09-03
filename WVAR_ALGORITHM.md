# W-Variable Candidate Set Algorithm

## Overview

This document describes modifications to the liquid-fixpoint solver to support
"w-variables" (omega-vars): unknowns that appear only in constraint bodies (never
as heads) and should be solved to the **weakest** value that makes the overall
system satisfiable.

The algorithm has two phases:
1. **Phase 1:** Run the standard fixpoint (unmodified `refineC`), but record which qualifiers are removed from each k-var and by which constraint.
2. **Phase 2:** A separate, small monotone fixpoint that propagates "candidate" qualifiers — those that a w-var could rescue — through the dependency graph.

After Phase 2, failing concrete checks are analyzed: if adding a w-var's
candidate qualifiers would fix a failing head, a solution for that w-var is
computed via weakest precondition (WP).

## Problem Setting

Constraints come in two flavors:
- **Regular:** `L => kappa_j(x)` — standard, no w-var involvement.
- **W-guarded:** `omega_i /\ L => kappa_j(x)` — guarded by a w-var in the body.

W-vars appear only in constraint bodies, never as heads. The standard fixpoint
treats w = true, making w-guarded constraints fully active. This may
over-constrain k-vars, causing concrete checks to fail.

We want to find the weakest assignment to each omega_i such that the system
becomes satisfiable.

## Data Structures

### New types needed

```haskell
-- | Identifies w-variables (analogous to KVar but for greatest-fixpoint unknowns)
newtype WVar = WV { wv :: Symbol }
  deriving (Eq, Ord, Hashable, Show)

-- | Which constraints are w-guarded, and by which w-var
type WGuardInfo = HashMap SubcId WVar

-- | Record of a qualifier removed during Phase 1
data Removal = Removal
  { rmKVar       :: !KVar      -- ^ Which k-var it was removed from
  , rmQual       :: !EQual     -- ^ The qualifier that was removed
  , rmConstraint :: !SubcId    -- ^ Which constraint caused the removal
  } deriving (Show)

-- | Per-w-var candidate qualifiers for each k-var (Phase 2 output)
type CandMap = HashMap KVar (HashMap WVar [EQual])
```

### Modifications to existing types

**`GInfo` (in `Types/Constraints.hs`):** Add a field to declare w-variables and
which constraints they guard.

```haskell
data GInfo c a = FI
  { ...
  , wGuards :: !WGuardInfo     -- ^ Maps constraint ID -> guarding WVar
  , wVars   :: !(HashSet WVar) -- ^ Set of declared w-variables
  }
```

**`Result` (in `Types/Constraints.hs` or wherever Result is defined):** Add w-var
solutions to the output.

```haskell
data Result a = Result
  { ...
  , resWVars :: !(HashMap WVar Expr)  -- ^ NEW: computed w-var assignments
  }
```

## Phase 1: Standard Fixpoint + Removal Tracking

**No modifications to `refineC`.** The existing solver runs exactly as-is.

The only addition: a wrapper around `refineC` (or around `S.update`) that
records removals. When `S.update` detects that qualifiers were dropped from a
k-var, record each dropped qualifier along with the constraint ID that caused it.

### Implementation sketch

```haskell
-- In Solve.hs, wrap the existing refineC or modify solve_ to collect removals

-- Option A: Wrap S.update to also return removed qualifiers
updateTracked :: Sol QBind -> [(KVar, QBind)] -> (Bool, Sol QBind, [Removal])
updateTracked s kqs = (changed, s', removals)
  where
    (changed, s') = S.update s kqs
    removals = [ Removal k eq cid
               | (k, newQB) <- kqs
               , let oldQB = lookupQBind s k
               , eq <- qbEQuals oldQB \\ qbEQuals newQB
               ]

-- Accumulate removals across the entire fixpoint solve in a writer/state
type Removals = HashMap KVar (HashMap SubcId [EQual])
```

The output of Phase 1:
- `main :: Sol QBind` — the standard fixpoint solution (unchanged).
- `removals :: HashMap KVar [Removal]` — all qualifiers removed, tagged with which constraint did it.

## Phase 2: Candidate Propagation

A standalone function. Takes the fixed `main` solution and the removal records.
Produces `CandMap`.

### Algorithm

```
Input:
  main      : Sol QBind          -- fixed solution from Phase 1
  removals  : [Removal]          -- all qualifier removals from Phase 1
  wGuards   : WGuardInfo         -- which constraints are w-guarded
  constraints : [SimpC]          -- all constraints (for re-evaluation)

Output:
  cand : CandMap                 -- per-wvar candidate qualifiers per kvar

Procedure:

-- Step 1: Seed cand with direct w-guarded removals
for each removal (kvar=k, qual=Q, constraint=C):
  if C is w-guarded by omega_i:
    cand(k, omega_i) += Q

-- Step 2: Propagate through regular constraints (monotone upward fixpoint)
repeat until no changes:
  for each regular constraint C: L => kappa_j(x):
    for each omega_i:
      lhs_enh = lhsPred using enhanced(*, omega_i)   -- main + cand for omega_i
      for each removal (kvar=kappa_j, qual=Q, constraint=C') where Q not in cand(kappa_j, omega_i):
        if lhs_enh => Q:
          cand(kappa_j, omega_i) += Q                 -- Q can be rescued by omega_i
```

Where:
```
enhanced(kappa_j, omega_i) = main(kappa_j) ++ cand(kappa_j, omega_i)
```

### Key properties

- **cand only grows** in Phase 2 (qualifiers are added, never removed). This is
  because `enhanced` only grows (main is fixed, cand grows), which makes `lhs_enh`
  only strengthen, which can only cause MORE qualifiers to pass the check.
- **Monotone upward fixpoint:** converges in O(|removed qualifiers| * |constraints|)
  steps in the worst case. In practice, converges quickly (few propagation rounds).
- **No modification to main:** main is completely frozen during Phase 2.

### Implementation of `lhsPred` for Phase 2

Phase 2 needs a variant of `lhsPred` that expands k-vars using `enhanced(*, omega_i)`:

```haskell
lhsPredEnhanced
  :: Config -> IBindEnv -> BindEnv a -> Sol QBind -> CandMap -> WVar -> SimpC a -> Expr
```

This is identical to the existing `lhsPred` except: when expanding a k-var `k` in
the LHS environment, use `main(k) ++ cand(k, omega_i)` instead of just `main(k)`.

The simplest implementation: temporarily construct a Sol where `sMap` has the
enhanced QBinds, then call the existing `lhsPred`.

### SMT context reuse

Phase 2 can reuse the SMT context from Phase 1. The `filterValid` calls in Phase 2
use the same solver instance — just different LHS expressions and different
candidate qualifiers to check.

## Phase 3: Checking Failing Heads and Computing WP

After Phase 2 produces `cand`, check each failing concrete constraint.

```
for each failing constraint kappa_j(x) => P:

  -- 1. Check which omega can fix it
  for each omega_i:
    enhanced_j = main(kappa_j) ++ cand(kappa_j, omega_i)
    if enhanced_j => P:
      omega_i is a candidate fix

  -- 2. For the winning omega_i, minimize (optional but gives weakest w)
  S = minimal subset of cand(kappa_j, omega_i) such that main(kappa_j) ++ S => P
  (Use UNSAT core: assert main(kappa_j) /\ NOT(P) with cand quals as
   activation literals. Extract core for near-minimal S.)

  -- 3. Compute WP for omega_i
  For each w-guarded constraint (omega_i /\ L_c => kappa_j):
    omega_i_solution = L_c[enhanced] => conjunction(S)
  (If omega_i guards multiple constraints, conjoin requirements.)
```

## Soundness Guarantee

**Theorem:** If `Q` is in `cand(kappa_j, omega_i)` at convergence of Phase 2, and
we define `omega_i* = conjunction of (L_c[enhanced] => Q)` for each w-guarded
constraint on kappa_j, then the greatest fixpoint of the system with omega_i :=
omega_i* includes `enhanced(kappa_j, omega_i)` for all kappa_j.

**Proof sketch:** `enhanced` is a valid post-fixpoint of the system with omega_i
set to omega_i*:
- Regular constraints: satisfied because cand qualifiers survive the `lhs_enh`
  check (Phase 2's convergence condition).
- W-guarded constraints: satisfied because omega_i* is constructed to imply
  exactly what's needed.

By the greatest-fixpoint property, the actual GFP is at least as strong as any
valid solution. Therefore GFP >= enhanced, meaning every cand qualifier appears in
the actual solution. No verification rerun needed.

## Convergence

- Phase 1: standard fixpoint convergence (unchanged).
- Phase 2: monotone upward on a finite lattice (cand only grows, bounded by
  |removed qualifiers|). Terminates.

## Multiple W-Vars

Each omega_i gets its own independent cand set. Phase 2 propagation for omega_i
only uses `enhanced(*, omega_i)` = `main + cand(*, omega_i)`. No cross-omega
contamination.

- A qualifier rescued by omega_1 alone: in `cand(*, omega_1)`. Works.
- A qualifier rescued by omega_2 alone: in `cand(*, omega_2)`. Works.
- A qualifier needing BOTH omega_1 AND omega_2: fails all per-omega enhanced
  checks. Correctly dropped (we do not attempt cross-omega cooperation).

When checking a failing head: test each omega_i's enhanced independently. If
one works, use it. If none do individually, report that no single omega fixes it.

## Multiple Occurrences of the Same W-Var

If omega_i guards multiple constraints (on potentially different k-vars):

- All qualifiers stripped by any omega_i-guarded constraint seed `cand(*, omega_i)`.
- Phase 2 propagation for omega_i sees ALL of its contributions across all k-vars
  in the enhanced LHS.
- WP at the end: omega_i must satisfy requirements from ALL its guarded constraints.
  Take the conjunction of per-constraint WPs.

## Files to Modify

| File | Change |
|------|--------|
| `Types/Constraints.hs` | Add `wGuards :: WGuardInfo` and `wVars :: HashSet WVar` fields to `GInfo`. Add `WVar` type. Add `resWVars` to `Result`. |
| `Types/Solutions.hs` | Add `WVar` re-export if needed. No changes to `Sol` itself (cand is separate from the solution during solving). |
| `Solver/Solve.hs` | In `solve_`: after `refine` returns, run Phase 2 and Phase 3. Modify `result` to incorporate w-var solutions. Track removals during `refine` (wrap `S.update` or add state). |
| `Solver/Solution.hs` | Add `lhsPredEnhanced` that expands k-vars using enhanced solutions. Can be implemented by temporarily augmenting the Sol's sMap. |
| `Solver/Monad.hs` | No changes needed (filterValid is reused as-is). |
| `Solver/Worklist.hs` | No changes needed (Phase 2 has its own iteration, not the worklist). |
| `Types/Config.hs` | Add flag to enable w-var solving (e.g., `--wvars`). |
| `Solver.hs` | Thread w-var results through to the top-level API. |

## Implementation Order (suggested)

1. Add `WVar` type and `wGuards`/`wVars` fields to `GInfo`. Update `Monoid`/`Semigroup` instances, parsers, etc.
2. Add removal tracking to `solve_` (accumulate removed qualifiers during `refine`).
3. Implement Phase 2 as a standalone function (`propagateCand`).
4. Implement Phase 3 (check failing heads, compute WP).
5. Wire results into `Result`.
6. Add tests.

## Optimization Notes

- Phase 2 only processes REMOVED qualifiers (a small subset of all qualifiers).
  Qualifiers in main are guaranteed to survive with any omega value.

- Phase 2's per-omega propagation can be run concurrently (no shared mutable state
  between different omega_i computations).

- For the common case (few w-vars, few removed qualifiers): Phase 2 is very cheap
  compared to Phase 1.

- The UNSAT core minimization in Phase 3 is optional. Without it, omega gets
  assigned the WP for ALL cand qualifiers (valid but potentially stronger than
  necessary).
