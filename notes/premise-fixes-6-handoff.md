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

## Parts A, D, C (in progress, 2026-11-11)

- Done and committed: A's vocabulary, zap specs, family axioms' text, trusted predicates (173a618ddd);
  client/concurrency (c258bcd99b, f18372b1f7); Go test `examples/premisefix/zaplogger` (c95275b5e0,
  passes); backend/storage/mvcc/traceutil + mvcc testers (4d9a9dc281; backend, mvcc interfaces
  regenerated); auth/snap/membership/rafthttp (c7aa26a37d); txn/apply/read/v3rpc/v3compactor
  (97b391c3a4); etcdserver core (94b1d6a4ce); part C notes and docs (3b6c7d7d12; mvccfull's Go doc
  comment changed, `Code/.../mvccfull.lean` regenerated).
- Order chosen (form decision): the zap specs changed first, then each package fixed once,
  bottom-up. Subagent brief: `/shared/tmp/premise-fixes-6/brief-A.md`; callers left between agents:
  `/shared/tmp/premise-fixes-6/callers-from-storage.md`.
- STOPPED (for etcd-grove-81): (1) `bootOk`'s `%Hraft` needs `bv.lg' = cfg.Logger'` (the raft wrapper
  logs through `bv.lg'`; Go: bootstrap.go:546,557 `lg: cfg.Logger`): ready patch
  `/shared/tmp/premise-fixes-6/A4/bootok-raft-logger.patch` (not applied; with it the etcdserver Link
  and Results and every client Link build); without it `NewServer.lean:541,1321` fail.
  (2) D's text: Scope "D text" (appended), draft `/shared/tmp/premise-fixes-6/d-text-draft.md`.
- Next after the answers: apply the patch (or the alternative), build the examples and k8s
  (etcdstart `Serve`'s `zapLoggerOk`, `restart/serveClient`, `ServeFromStart`, `grpcCfgOk` users,
  `examples/etcd/auth/MainServe.lean`), regenerate the etcdstart interface; then D; then merge lean,
  full build, tcb --check, collections, interfaces, gen-init --check; STATUS; checkpoint (c).

## Build

`export TMPDIR=/shared/tmp`; targeted: `systemd-run --scope -q -p MemoryMax=64G lake
--packages=/shared/tmp/manifest-ddc.json build <modules>`; full: prefix `flock
/shared/tmp/etcd-grove-build.lock`. Scripts: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`.

## Pitfalls

- `notes/status-history.md` is append-only: check `wc -l` against lean's before committing.
