# Context sweep fixes: handoff (branch ctx-sweep-fixes, worktree /shared/etcd-grove-ctxfix)

Coordinator: etcd-grove-81. Notes: `notes/ctx-sweep-fixes.md`. Freeze package: `/shared/tmp/ctx-sweep/freeze.md`.

## Done
- `watchCtx` + `"#HCC"` (Value(&cancelCtxKey), isContext's form); producers `watchCtx_of_isContext`, `chanCtx_watch`;
  `WithCancelValCtx` justification corrected; Go test `examples/premisefix/watchctx`.
- `k8sctx.k8sCtxOk` + runtime/trace's key (`rtrace.traceKeyAny`, `rtrace.taskRes`); runtime/trace translated
  types-only in project k8s-apiserver; Go test `examples/premisefix/k8sctx/rtrace_test.go`.
- Full build green; tcb --check and all 55 collections match (no baseline change); axiom-tok, model-param,
  gen-interface (all etc/api), goose --check k8s-apiserver, gen-init: ok.

## Next
- STOP: the coordinator's axiom review of the Freeze package; then merge lean, add the STATUS.md "Last
  updated" entry (move the oldest to status-history, append-only), `etc/land.sh` when told.

## Build
`export TMPDIR=/shared/tmp; flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G
etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json`

## Pitfalls
- k8s 7f-4 (/shared/etcd-grove-k8s7f) also edits `etc/goose.py` (etcd project); expect a small merge.
