# otelSpan narrowing: handoff (branch otelspan-narrow, worktree /shared/etcd-grove-otel)

Done (approved by etcd-grove-81, 2026-11-13): `trace.otelSpan`'s trusted text narrowed (`Proof/context/LibKeys.lean`), `grpcRunCtx`'s and
`tracing.Start.spec`'s docstrings; Go evidence `examples/premisefix/k8sctx/otelprovider_test.go`;
`notes/otelspan-narrow.md`, `notes/ctx-sweep-fixes.md` updated. Freeze package
`/shared/tmp/otelspan/freeze.md`, stopped for etcd-grove-81's axiom review.

Next: landing via `etc/land.sh` (go given by etcd-grove-81); STATUS entry and decisions.md entry done.

Pitfalls: the LibKeys docstring rebuilds ~5600 modules (its olean changes). Build:
`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G etc/timed-build.py
--packages=/shared/tmp/manifest-ddc.json` (TMPDIR=/shared/tmp). Go tests: GOWORK=off, under
`systemd-run --scope -q -p MemoryMax=32G`.
