# incomingof handoff

## START HERE (2026-11-17, Part B texts at the attack stop)

- Branch `incomingof-scope`, worktree /shared/etcd-grove-incomingof; lean 5fb716b5eb merged (5ef8f6520f).
- Part A refuted, not linked, Lean reverted (5dab7c3336; land the branch with it, decided). B0 done (Scope §B.0).
- Part B approved (Scope, top). Exact texts + soundness note: `notes/axiom-review/incomingof-b.md` (T1-T7);
  Go: `examples/axiomcx/incomingof/is_test.go`. **STOP: waiting for 03's independent attack.**
- Next after the go: implement T1-T7 (files listed in each T); merge lean (if the pin moved to 6d365ee1a use
  /shared/tmp/manifest-6d3.json and update .lake/package-overrides.json); full build via build-slot
  (LEAN_NUM_THREADS=4, retry); tcb-report --check (no axiom delta; trusted texts: ContextReadErrs,
  ctxErrsErr/ctxErrClient, IsStatusErr.spec); interfaces; gates under flock
  /shared/tmp/etcd-grove-full-build.lock; STATUS entry; STOP at the land stop with client_range_any old → new.
- Pitfalls: a persistent-auth fresh world makes every WP form true and any wand from cells to a pure fact
  buildable; only entailments (axioms, premise fields) are exposed: keep pure errDesc facts out of them.

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
