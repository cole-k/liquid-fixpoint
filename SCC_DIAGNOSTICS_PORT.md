# Observational diagnostics on the self-aware baseline

The `self-aware-scc-diagnostics` branch is based on upstream
69e585b4d0deaef8f1640d87fe1466efbb14aab1, the revision of the installed Flux
solver. Changes add `--trace`
logging and input-head origins. Upstream self-argument parsing/propagation and
qualifier generation remain unchanged. The older `incremental-scc-diagnostics`
branch is preserved; it lacks the newer upstream `:self` support.

Build: `stack build` from a checkout of `self-aware-scc-diagnostics`.

Consumer, documentation and regression driver: `../flux-replays/`:

```
python3 check_fixpoint_observational.py ../liquid-fixpoint \
  --results results/scc-self-preserved --flux-source ../flux
```

This checks unchanged inputs against the installed upstream solver and against
the port with trace off/on, comparing statuses and inferred solutions. The port
does not include old experimental skip-result, forced-KVar or all-cuts options.

Diagnostics use the same record names as the older SCC instrumentation, consumed
by flux-replays. The current port includes Horn conversion, preprocessing, setup,
candidate elaboration, SMT initialization/global axioms, refinement and validation
phase measurements; phase coverage is incomplete. NONCUT_QUERY records count AST
nodes and non-cut depth; their detailed timing fields are also present in
SCC_VISIT/CONCRETE_TIME. Tracing forces expressions and adds measurement overhead.
