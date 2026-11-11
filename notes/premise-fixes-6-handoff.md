# premise-fixes-6: handoff

Scope: `/shared/tmp/premise-fixes-6/scope.md` (approved; read its "Decisions" and "Added by
etcd-grove-81 after round 3"). Order D6: part B (`errors.IsCtxErr`) first, its own landing; then A
(zap logger family), D (verb-aware `fmt.argOk`), C (audit/docs), after premise-fixes-5 lands, on
etcd-grove-81's separate brief.

## Done (part B)

- `Spec/errors/IsCtxErr.lean`: premise `context.isCtxErr err` (a pre conjunct) in place of
  `isTypedErr err`.
- `parseProposeCtxErr`, `LeaseRenew` proofs: `isCtxErr` from `isCtxErr_of_Canceled`/`_DeadlineExceeded`.
- `recvLoop.spec` post `⌜err = nil⌝ ∨ v3rpc.streamErr err`; its proof (EOF branch's error return
  shown unreachable).
- `watchServer.Watch`: `PE` carries `streamErr`; first `errors.Is` by `errors.Is.spec` (`hIsT`),
  second by `IsCtxErr` with `HErrDone`'s `isCtxErr`. Link: `etc/link-lean-first-v3rpc.txt`, v3rpc `Link.lean`.
- Go test `examples/premisefix/isctxerr` (in the examples module: gates step 9 picks it up).
- Notes: `decisions.md` "Premise fixes 6, part B", `axiom-review/isctxerr.md` "Repaired",
  `audit.md` rows, STATUS.

## Verified (checkpoint (a), 2026-11-11)

Full build (lock, 64G cap) clean at the part-B commit; `tcb-report --check` matches the baseline
(843 axioms, 5 sorries); all 54 collections `--check` ok; `gen-init --check`, `api-check` and
`gen-interface --check` (backend, bbolt, etcdstart, mvcc, raft) ok; `go test ./premisefix/isctxerr` passes.

## Next

- Part B accepted by etcd-grove-81 (2026-11-11), with the forms (recvLoop's post `streamErr` alone,
  `Watch` taking `errors.Is.spec`, `parseProposeCtxErr`'s unused premise kept) and the Go test's
  `LeaseRenew` fallback (gap noted in `isctxerr.md`).
- Landing order: premise-fixes-5, then this branch, then k8s-7e. WAIT for etcd-grove-81's "lean is
  free". Then: merge lean; rebuild what the merge touches (a full build under the lock and cap if
  pf5's changes reach B's files); `tcb-report --check`; then `etc/land.sh` directly with
  `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc`.
- Then A, D, C per the Scope's section F, on the coordinator's brief.

## Parts A, D, C (done, 2026-11-11)

- A: vocabulary, zap specs, family axioms (173a618ddd); client/concurrency (c258bcd99b, f18372b1f7);
  backend/storage/mvcc/traceutil (4d9a9dc281); auth/snap/membership/rafthttp (c7aa26a37d);
  txn/apply/read/v3rpc/v3compactor (97b391c3a4); etcdserver core (94b1d6a4ce); bootOk's
  `bv.lg' = cfg.Logger'` (4edc093cc5, approved by etcd-grove-81); examples and ServeFromStart
  (36015f1ad5); Go test `examples/premisefix/zaplogger` (c95275b5e0, 505a2ee91c).
- D: verb-aware `fmt.argsOk` (5cdd1a5b9e; `etc/gen-init.py` follows, 50c19406f0); Go test
  `examples/premisefix/fmtarg`.
- C: audit refresh, logger-family Repaired, docs (3b6c7d7d12).
- lean 8809f94d74 merged (3bd81a2afc).
- Notes: `decisions.md` "Premise fixes 6, parts A and D"; `axiom-review/zap-zero.md` "Repaired";
  STATUS entry and section.

## Verified (checkpoint (c), 2026-11-11)

Full build (lock, 64G cap) clean, 14015 jobs, 4m01s wall (incremental), peak 4.0 GiB;
`tcb-report --check` matches the baseline (866 axioms, 5 sorries); all 54 collections `--check` ok;
`gen-interface --check` and `api-check --check` (backend, bbolt, etcdstart, mvcc, raft) ok;
`gen-init --check`, `goose.py --check`, `issues-status --check`, `bounds-check --check` ok;
`go test ./premisefix/...` (9 packages) passes.

## Next

Ready to land after etcd-grove-81's go: merge lean if it moved (rebuild and re-check what the merge
touches), then land with `LAKE_PACKAGES=/shared/tmp/manifest-ddc.json
PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc etc/land.sh`. Follow-ups: D3 (`lgMu` slots, bounds),
D5 (`NewBackendQuota`), raft `Changer.apply`'s unused `ConfChangeType.String.spec` hypothesis.

## Build

`export TMPDIR=/shared/tmp`; targeted: `systemd-run --scope -q -p MemoryMax=64G lake
--packages=/shared/tmp/manifest-ddc.json build <modules>`; full: prefix `flock
/shared/tmp/etcd-grove-build.lock`. Scripts: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`.

## Pitfalls

- `notes/status-history.md` is append-only: check `wc -l` against lean's before committing.
