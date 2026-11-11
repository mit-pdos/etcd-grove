# premise-fixes-8c handoff (client half: C1, C2, C3)

Scope: `/shared/tmp/premise-fixes-8/scope.md` (approved, "## Decisions"). Coordinator: etcd-grove-81.
Worktree `/shared/etcd-grove-pf8c`, branch `premise-fixes-8c` (cut from lean `da225483c9`). The
server half (S1/S2) is in `/shared/etcd-grove-pf8`; don't touch its files.
Decisions and forms: `questions.md` (worktree root, untracked).

## Done

- C1 (trust change, STOP for review of the old -> new text before building on it):
  - `Proof/context/LibKeysChain.lean`: `metadata.outgoingCtxOkC` (Perennial's `ctxValue` at
    `mdOutgoingKey{}`) and its laws `_background`, `_todo`, `_from`, `_valueCtx`, `_ownKey`, `_raw`,
    `_todoFrom`, `_bgFrom`, `outgoingCtxOk_of_C`, `context.keyEqOk_of_ty_ne`.
  - Stronger posts: `WithCancelTodo` (+ `ctxValueFrom todoCtxVal ctx'`), `WithTimeoutBackgroundMd`,
    `WithRequireLeader` (inner triple), `AppendToOutgoingContext` (+ `outgoingCtxOkC`).
  - `wait.channelContext.Deadline` spec + proof (translated; for C3's `chanCtx_ok`; not linked yet).
  - Go tests `examples/premisefix/ctxvalue/clientctx_test.go`: `TestClientCallCtxPanics` (the
    scratch file's four contexts, Invoke and NewStream, plus a `withVersion` copy) and
    `TestClientContexts`. Pass.

## Next, in order

1. C1 is built and gated at 9c032948fa (full build clean; tcb --check: 865 axioms, 5 sorries,
   unchanged; all 54 collections --check; the 5 interfaces --check; gen-init --check). Waiting on
   the coordinator's review of the trusted text (`/shared/tmp/premise-fixes-8c/c1-trusted.diff`)
   and its go for land.sh (merge lean first).
2. C2: the cascade (Scope C.3, list `/shared/tmp/premise-fixes-8/client-cascade.txt`).
3. C3: flip `ctxOk`/`ctxQuiet`/`ctxErrs` (N1-N3; STOP on the "no AfterFunc" text), `FromOutgoingContext`,
   `watchCtx`, `WithCancelValCtx`'s post (moved here from C1), `kaCtxOk`.

## Pitfalls

- Adding a conjunct to an axiom's post breaks `icases` patterns of its users: grep for the
  `wp_apply ... as` lines (`newClient`, `TimeoutCtx.wp_WithTimeout_bgMd`, auth `reqCtx`/`Work`).
- `ctxValue` needs `[context.Assumptions]`; `outgoingCtxOkC_ownKey` needs
  `[google_golang_org.grpc.metadata.Assumptions]` (struct key equality).

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`
(TMPDIR=/shared/tmp). Single files: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`.
