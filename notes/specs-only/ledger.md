# The spec plan's change ledger

A spec defect that a proof (or a review, a test, a user's critique) finds in a spec of the spec plan
(`SpecPlan/Spec/`), or a divergence between a real spec (`Spec/`) and the plan's, is recorded here
**before** either spec is edited (CLAUDE.md, "The spec plan and convergence"). The ledger is how the
plan stays the target the real proofs converge toward: no silent edits.

One entry per defect, newest first, in this format:

```
## <date>: <spec> -- <one-line defect>

- **Spec.** The file and the declaration (`SpecPlan/Spec/<pkg>/<fn>.lean`, `<fn>.spec`; or a law,
  `<pred>_<law>.spec`), and the real spec it corresponds to (`Spec/<pkg>/<fn>.lean`), if any.
- **Defect.** What is wrong: unprovable (false of the Go code), too weak for a user, too strong (a
  premise no caller can meet), not local, vacuous, ...
- **Evidence.** What shows it: the proof step that fails (file:line, the goal), the Go path (a
  panic, an error the post omits), the user or snippet (`examples/specreq/<alias>/`) it breaks, a
  failing test.
- **Proposed change.** The new statement (or its delta), and what else it moves: the snippets, the
  callers' and callees' specs and proof sketches, the open questions it touches.
- **Decision.** Pending / accepted (by whom, date; the commit that applied it) / rejected (why).
```

A change that needs the user's approval (a spec's statement at the client boundary, new
client-visible ghost state, a trust-boundary spec) says so in **Decision** and waits for it.

(No entries yet.)
