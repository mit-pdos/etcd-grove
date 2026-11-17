# incomingof handoff

## START HERE (2026-11-17, Part A in progress)

- Branch `incomingof-scope`, worktree /shared/etcd-grove-incomingof; lean 5fb716b5eb merged (5ef8f6520f).
  `.lake/build` was seeded from a stale main build: targeted builds rebuild a lot.
- Approved by the user 2026-11-17 via etcd-grove-03: Part A (A-C/C-ii, Q2/Q3/Q6 as recommended), then B0
  (read-only inventory of the consumers of `rangeErrΨ` & siblings), STOP; Part B only after 03's go.
- Done (Lean, Part A): `Incoming.lean` (axiom `incomingOf_cancelCtx` gone; def `metadata.incomingKept`),
  `InvGrpcStream.lean` `srvRawStreamIs` (+ `metadata.incomingKept ci`), `WrapperMd.lean` (axiom restated,
  `incomingOf_wrapper`/`field_unique` gone), `newStreamInterceptor.lean` (patterns, direct application).
  Go evidence copied: `examples/axiomcx/incomingof/` (own module; GOTOOLCHAIN=go1.27.3 GOWORK=off go test).
  Exact texts + cross-world argument: `notes/axiom-review/incomingof.md`.
- Next, in order: (1) STOP for 03's independent attack on the texts; (2) full build (build-slot, retry on
  cap kill, LEAN_NUM_THREADS=4); (3) `etc/tcb-report.py --check --update` + the 22 collections
  (`--collection etc/tcb-collections/X.txt --check --update`); (4) interfaces (none list these modules);
  audit row (`notes/audit.md:525`), `notes/incomingof-crossworld.md` status, axiom-review README row,
  STATUS; (5) gates under `flock /shared/tmp/etcd-grove-full-build.lock` with
  `LAKE_PACKAGES=/shared/tmp/manifest-c6b.json PERENNIAL_CHECKOUT=/shared/perennial-c6b39d4f8`, GOWORK
  unset; STOP at the land stop; (6) B0 read-only, STOP.
- Pitfalls: as in History below; never run go in the main checkout; `srvRawStreamIs` is unfolded at three
  places only (InvGrpcStream `srvRawStreamIsW_of_raw`, newStreamInterceptor :118 and :258).

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
