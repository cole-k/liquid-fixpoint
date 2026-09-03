# Non-Cut KVar Timeout Investigation

Non-cut KVars are represented lazily as hypothesis cubes. Their predicates are
not eagerly materialized during cut classification, but are expanded whenever a
constraint LHS needs them. A timeout can therefore occur while refinement uses
a non-cut in the LHS of a worklist constraint, or later while final validation
uses one in a concrete constraint. The current evidence shows that this is a
cost of forcing and checking delayed non-cut solutions; it does not yet
separate Haskell-side expansion/serialization from SMT assertion or solving in
every reproducer.

Reproduce with `fixpoint --trace FILE.smt2`. `smallvec.multi-check.smt2` stalls during
refinement; `bytes.multi-check-self-args.smt2` reaches final validation and
then stalls. `--dump-kvars` writes the cut/non-cut classification and
`--dump-sccs` writes the refinement SCC dependency graph. `--all-kvars-cut`
disables non-cut elimination for comparison; on Horn inputs it intentionally
overrides the frontend's usual `--eliminate=some` default. The corresponding
`smallvec.multi-check.allcuts.smt2` completes in about one minute.
