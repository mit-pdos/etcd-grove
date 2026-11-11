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

## Next

- Checkpoint (a): report to etcd-grove-81, stop before `etc/land.sh`; merge lean (pf5) first.
- Then A, D, C per the Scope's section F, on the coordinator's brief.

## Build

`export TMPDIR=/shared/tmp`; targeted: `systemd-run --scope -q -p MemoryMax=64G lake
--packages=/shared/tmp/manifest-ddc.json build <modules>`; full: prefix `flock
/shared/tmp/etcd-grove-build.lock`. Scripts: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`.

## Pitfalls

- `notes/status-history.md` is append-only: check `wc -l` against lean's before committing.
