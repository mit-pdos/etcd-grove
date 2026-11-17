# incomingof handoff

## START HERE (2026-11-17, Part A refuted; B0)

- Branch `incomingof-scope`, worktree /shared/etcd-grove-incomingof; lean 5fb716b5eb merged (5ef8f6520f).
- Part A (897f63a6e5) REFUTED by 03's independent attack (persistent-auth fresh world builds
  `incomingKept`): not linked; its Lean is reverted on the branch (the four files equal lean's). Record:
  `notes/axiom-review/incomingof.md` ("The refutation"), Go `examples/axiomcx/incomingof-attack/`, audit row,
  `notes/incomingof-crossworld.md`.
- Now: B0, the read-only inventory of the consumers of the client's KV error outcomes
  (`notes/incomingof-scope.md` §B.0, done), then STOP. Part B only after 03's go; its new texts must first be checked
  against the persistent-auth fresh-world attack in a soundness note (they get an independent attack).
- Pitfall (new): a persistent resource that is a wand from heap cells to a pure fact is buildable in a
  fresh world with `Auth DFrac.discard σ`; "only an uninterpreted call delivers it" does not protect it.

## History

### 2026-11-17, Scope

- Branch `incomingof-scope` (off lean 3cd4b72599), worktree /shared/etcd-grove-incomingof, no .lake/build.
  Notes only.
- Done: `notes/incomingof-scope.md`, Part A (the axioms `incomingOf_cancelCtx` and
  `v3rpc.incomingOf_cancellableContext`) and Part B (`ContextReadErrs.descs`, `ctxErrsErr`'s description
  conjunct). Go evidence in /shared/tmp/incomingof/gotest (all pass).
- State: **Scope hard stop**, waiting for etcd-grove-03 and the user on Q1-Q6 (Scope, last section).
- Next once approved: A1-A5 (about 160 lines, 1 day), then B0 (read-only inventory of the KV error-outcome
  consumers, STOP), then B1-B6.
- Pitfalls:
  - A law whose conclusion is a pure fact about `incomingOf`/`errDesc` must not be (1) an entailment from a
    resource that can be built on its own (`crossWorld`), or (2) a post over code with Lean semantics
    (adequacy plus nondeterministic `Alloc`).
  - Laws over `ctxValueFrom`/`valueAt`/`errorMsgIs` (WP forms) are refuted by a looping `Value`/`Error`. Use
    structural links (one parent cell).
  - Build with the slot wrapper and manifest-c6b (common-rules).
