# incomingof handoff

## START HERE (2026-11-18, option (a) decided; T2' written; STOP for attack)

- Head 0e013c5ab0 (on dbb741dd80, WIP: kv__Get.lean fails). **Decided by etcd-grove-03 (2026-11-18): option (a)**
  of the blocker: (1) T2' narrows `ctxErrsErr`/`ctxErrClient`'s conjunct to `ctxErrMsg m` (Go's two context
  messages; trusted text claiming more); (2) proved `rpctypes.Error.spec`: no-`GRPCStatus` error with a stable
  non-key message comes back unchanged; (3) proved `ContextError.spec`: a context error comes back as one. M4
  stays a pre-existing hardening item (accepted). T2' text, checks and Go evidence: note
  `notes/axiom-review/incomingof-b.md`, section "Option (a)"; Go: `examples/axiomcx/incomingof-real/ctx_test.go`.
- **STOPPED** for a short independent attack on T2' before relying on it. Nothing implemented for (1)-(3) yet.
- Next after the attack: `ctxErrMsg` + `ctxErrMsg_not_handler` in `cache/v3/Base.lean`; T2' in InvGrpc/InvKVConn;
  producers (ErrorsNewOk `ctxErrClientAllW_of`, ChanCtx `chanCtx_ok`); (2), (3); kv__Get; the nil-case
  one-liners (below); decide `descDeadline`; merge lean; full build; tcb --check; interfaces; gates; STATUS; land stop.

## Earlier START HERE (2026-11-18, Part B implementation: BLOCKER at T4, stopped)

- Branch `incomingof-scope`, worktree /shared/etcd-grove-incomingof (lean 5fb716b5eb merged; lean had not moved
  at the last check; pin still c6b, manifest-c6b). Part A refuted/reverted; B0 done; Part B texts attacked,
  all survive (note `notes/axiom-review/incomingof-b.md`, MINORs folded).
- Implemented (WIP commit, last on the branch): T1 (`descDeadline`), T2 (`ctxErrsErr`/`ctxErrClient` message
  form; `ctxErrShape` in `cache/v3/Base.lean`, section `desc`), T3 (`IsStatusErr.spec`), T4 text
  (`ContextError.spec`, `rangeErrOut`, `kv.Do.specG`, `kv.Get.specG`), T5 (`rangeErrSound`, `readErrIs`,
  Client.Get/List, getList, listReadError), T6 (`ctxErrDescs` from `toGRPCErrorMap_init`), T7 (producers:
  `errorMsgIs_errorString`, `errorMsgIs_deadline`, `ctxErrClientAllW_of`, `canceledOk_of_init`, `chanCtx_ok`).
  Fixed after the first targeted build: `.1` of `IsStatusErr`'s post in shouldRefreshToken/isSafeRetry; the
  nil case `ileft; ipureintro; rfl` in InvClientAuth/InvServerKV.
- **BLOCKER (T4):** Go applies `ContextError` twice (`kv.Do` returns `ContextError(ctx, err)`, `kv.Get` returns
  `ContextError(ctx, err')` of that). `ContextError.spec`'s new post (`errDesc err'' = errDesc err' ∨ ctx-shaped
  err''`) does not carry a ctx-shaped `err'` through the second call: in the description-kept branch nothing
  says `err''` is still ctx-shaped (or what its description is). Options in the report / note ("Blocker").
- Remaining build errors at the stop: `kv__Get.lean` (the blocker, ~:80 and ~:128; also `%⟨…⟩` is not
  accepted in `$$`, use `%(And.intro …)`); unknown beyond the four link targets (build-b2 log:
  /shared/tmp/incomingof/build-b2.log). Other files that may need the nil case `ileft`: examples auth/authN/auth3
  run, watchGRPCStream__run, InvGrpc (grep `ipureintro; left; rfl`).
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build <the four Link targets>`
  (client v3 Link, LinkMembers, v3rpc Link, k8s etcd3 Link), LEAN_NUM_THREADS=4.

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
