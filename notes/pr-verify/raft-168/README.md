# Files of the raft#168 verification

Everything below was written for this PR. The report is `../raft-168.md`.

## Go reproductions

These run against the PR head `43f19c68a57c2317805c76d90351c07327c89ffa` (etcd-io/raft#168, gogoproto
`raftpb`). In a checkout of the PR head, with `CHECKOUT` its root:

```
git -C ~/etcd worktree add --detach /tmp/raft168-head 43f19c68a   # or: fetch pull/168/head
cp confchange/witness_restore_test.go $CHECKOUT/confchange/
cp quorum/witness_olq_test.go         $CHECKOUT/quorum/
cp witness_restart_test.go review_witness_test.go $CHECKOUT/
cd $CHECKOUT && GOTOOLCHAIN=go1.27.1 go test ./confchange -run TestWitnessRestoreJoint -v
GOTOOLCHAIN=go1.27.1 go test . -run 'TestWitnessRestartInJointConfig|TestReview' -v
GOTOOLCHAIN=go1.27.1 go test ./quorum -run TestOneLessThanQuorumSingleVoter -v
```

Every one of these tests **fails** at the PR head; each failure is the finding it demonstrates
(re-run 2026-10-16, outputs in `logs/`):

| file | test | shows (report finding) | output |
|---|---|---|---|
| `confchange/witness_restore_test.go` | `TestWitnessRestoreJoint` | `Restore(ConfState())` of `(1 2 3 4)&&(1 2 3)` with witness 3 in both halves gives `(1 2 4)&&(1 2 3)` (1) | `logs/TestWitnessRestoreJoint.txt` |
| `witness_restart_test.go` | `TestWitnessRestartInJointConfig` | `newRaft` panics on restart in that config (`ConfStates not equivalent`) (1) | `logs/raft-tests.txt` |
| `review_witness_test.go` (by the reviewer subagent) | `TestReviewLastEntryAfterSnapshot`, `TestReviewCandidateAfterSnapshotWitness` | `raftLog.lastEntry()` and a candidate asking the witness both panic when the log ends at a snapshot (2) | `logs/raft-tests.txt` |
| `review_witness_test.go` | `TestReviewLeaderMaybeCommitCompacted` | `maybeCommit` panics when the "quorum − 1" index is compacted (3) | `logs/raft-tests.txt` |
| `quorum/witness_olq_test.go` | `TestOneLessThanQuorumSingleVoter` | `OneLessThanQuorum` indexes out of range on a one-voter config (4) | `logs/TestOneLessThanQuorumSingleVoter.txt` |

The tests are written against gogoproto (value messages). At the fork branch
`pr-raft-168-goose-lean`, which has protobuf-go v2 pointer messages, they would need porting.

## Tools

- `tools/astdiff/` (`main.go`, `go.mod`) lists the Go functions that differ between two source
  trees. It produced the report's 76-function list:
  `cd tools/astdiff && GOTOOLCHAIN=go1.27.1 go run . <raft37-goose-lean tree, 509271dac> ~/etcd-pr/raft-168`
  (the second argument is the fork branch `pr-raft-168-goose-lean`, `9dbcc6487`).
- `tools/PrintAxioms.lean` prints the axioms of the new and re-proved results. Run it from this
  worktree after `lake build` of the imported modules:
  `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake env lean notes/pr-verify/raft-168/tools/PrintAxioms.lean`.
  The summary is in `logs/print-axioms-summary.txt`: no `sorryAx` and no proof axiom. The
  remaining axioms are the type-level axioms that every proof here has.

## Logs

- `logs/raft-link-build-failures.txt`: the 21 raft-package modules that fail in
  `lake build Proof.go_etcd_io.raft.v3.Link` on this branch (commit `a46e09464`).
- `logs/goose.txt`: the translation run (`etc/goose.py --project raft --src raft=~/etcd-pr/raft-168`).
