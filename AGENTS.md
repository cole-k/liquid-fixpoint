# Fixpoint Investigation Guide

## DISCLAIMER:

This was written by an AI and should not be taken as authoratative or
comprehensive. It was not tasked with summarizing the code; only learning
enough to diagnos the problem.

The **only** trustworthy authority is the code itself.

## Solver Overview

Fixpoint proves implication constraints by inferring predicates for KVars. It
starts each cut KVar with candidate qualifiers, repeatedly removes candidates
that do not follow from a constraint LHS, then checks the resulting solution
against concrete constraints. Non-cut KVars are eliminated into delayed
hypothesis formulas rather than independently inferred.

## Main Path

`bin/Fixpoint.hs` dispatches `.smt2`/`.json` inputs to `Horn.Solve.solveHorn`;
other inputs go to `Solver.solveFQ`. The Horn frontend parses and flattens Horn
constraints, converts them to `FInfo`, and normally enables `--eliminate=some`.
Both paths then enter `Solver.solve` and, unless partitioning/minimization is
requested, follow these stages:

1. `Solver.solveNative` runs `simplifyFInfo`: simplify/reduce environments,
   convert to `SInfo`, sanitize and validate, uniquify KVars/bindings, rename,
   defunctionalize, elaborate sorts, and optionally expand extensionality.
2. `Solver.Solve.solve` computes cut/non-cut KVars and the constraint
   dependency graph, initializes the refinement worklist, and creates an SMT
   context with declarations, definitions, and global axioms.
3. `refine` pops non-concrete worklist constraints in SCC order. It expands the
   current LHS solution, asks SMT which RHS qualifier candidates are valid, and
   re-enqueues dependent readers when a cut KVar solution changes.
4. `result` checks concrete constraints against the completed solution. This
   also expands non-cuts that occur in those LHSs. If enabled, interpreter and
   PLE passes retry remaining failed constraints.
5. Fixpoint materializes cut and delayed non-cut results, optionally minimizes
   them, simplifies the final result, and prints `Safe` or `Unsafe`.

For Horn inputs, the frontend normally changes `--eliminate=none` to
`--eliminate=some`; use `--all-kvars-cut` to actually refine every KVar.

## Cuts And Non-Cuts

`Solver.Eliminate.solverInfo` classifies KVars before refinement. Cut KVars are
refined; non-cuts are stored lazily in `Solution.sHyp` as hypothesis cubes.
They are expanded when `Solution.lhsPred` builds an LHS containing them, both
for refinement worklist constraints and later concrete result checks. They are
not expanded by global axiom assertion.

## Progress And SCCs

The progress denominator is `1 + cNumScc`, over the constraint dependency
graph. Refinement ticks when it first enters an SCC. Concrete constraints are
not in the refinement worklist but still contribute to the denominator, so the
percentage is approximate. Worklist dependencies enqueue reader constraints
when a writer changes.

## Diagnostics

- `--trace`: coarse phases and worklist SCC entry/size.
- `--dump-kvars`: writes cut/non-cut classification before solving.
- `--dump-sccs`: writes a compact Graphviz KVar dependency graph for
  refinement worklist SCCs only.
- `--all-kvars-cut`: disables non-cut elimination.

## Reproducers

`slow-check/smallvec.multi-check.smt2` times out during refinement; the
all-cuts variant completes in about one minute. `slow-check/bytes.multi-check-self-args.smt2`
finishes refinement but times out during final validation. These show delayed
non-cut expansion/checking is implicated, but do not yet isolate Haskell
expansion/serialization from SMT work in every case.
