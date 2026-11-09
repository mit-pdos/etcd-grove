# Repair 2 (raft-core): RR-raft-core N3, S-e

- **N3** fixed. `Spec/go_etcd_io/raft/v3/raft__hasUnappliedConfChanges.lean`: the premise is now
  `⌜o.log.us.snap = none ∧ o.log.compactFloor ≤ o.log.applied⌝`. The only caller is `hup` (grep). It
  gets `us.snap = none` from `promotable`, which is `!hasNextOrInProgressSnapshot()` (`raft.go:1949`).
  That is `unstable.snapshot == nil` (`log.go:290`), so the premise is checked against the Go code.
  `hup`'s sketch now says this.
- **S-e** fixed. `ApiCore.lean` `coreIdle_floor`: the conclusion is now
  `floor ≤ applied ∧ (us.snap = none → base ≤ applied)`. The docstring gives the reason it holds in Go:
  `newLogWithSize` sets `applied = base` (`log.go:96`); `appliedTo` only grows `applied`; and
  `appliedSnap` (`raft.go:768-769`) clears the snapshot and sets `applied` inside a step, while the
  invariant is open. Only `coreIdle_floor` was touched in `ApiCore.lean`.
- **R3 snippet** fixed. `examples/specreq/raftlog/reads.go` `ReqScanConfChanges`: the Assumes line now
  states that no snapshot is pending, and the code returns early on `hasNextOrInProgressSnapshot()`.
  The snippet is gofmt-clean. `go vet` reports that build constraints exclude every file, because the
  files are `//go:build ignore`, as they were before this change.
- Changes lines: `Verify-round (RR-raft-core N3, S-e)` in `raft__hasUnappliedConfChanges.lean`
  and `raft__hup.lean`, and in `coreIdle_floor`'s docstring.
- Build: `etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3` passes (229 modules).
