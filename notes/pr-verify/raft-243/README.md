# Files for the verification of etcd-io/raft#243

The report is `../raft-243.md`. Revisions:

- PR head: `800cd610d5b1bccae9350b950e8638689a14e664` (etcd-io/raft `pull/243/head`, gogoproto raftpb);
- PR base: upstream `main` at `d155efc8163bf355d3ddbbe18f0b5d7f076a3048`;
- the verified code: fork branch `pr-raft-243-goose-lean` of upamanyus/etcd at `119f42a00` (the PR on
  `raft37-goose-lean` `509271dac`, protobuf-go v2 raftpb; not pushed, local in `~/etcd`).

Go tests need `GOTOOLCHAIN=go1.27.1`. Each passes by asserting the bad behavior the report describes.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `pr243_repro_test.go` | `TestPR243SnapStatusRaisesMatchUnacked`: an unacknowledged report lets a 3-node leader commit entries only it holds (misuse input). `TestPR243SnapStatusZeroLowersMatch`: the zero report lowers `Match` to 0, `Next` to 1. `TestPR243AppRespInSnapshotResendsSnapshot`: a stale ack below `firstIndex` leaves `StateSnapshot` and sends a second snapshot. `TestPR243SnapStatusPastLastIndex`: a report past `lastIndex` puts `Match`/`Next` past the log, and the leader commits its unreplicated entry. | PR head | `cp pr243_repro_test.go <checkout>/ && go test -run TestPR243 -v .` |
| `pr243_review_test.go` | (the reviewer's) `TestReviewReportUnappliedPanicsFollower`: after a `SnapshotFinish` for a snapshot the follower never applied, the heartbeat carries `Commit = 11` and the follower panics in `commitTo`. `TestReviewZeroReportResendsSnapshot`, `TestReviewStaleReportLowersMatch`, `TestReviewSentCommitAboveNext`, `TestReviewWrap`: findings 3, 4 and 6 of the report. | PR head | `cp pr243_review_test.go <checkout>/ && go test -run TestReview -v .` |
| `head-800cd610d.log` | the output of both files at the PR head (all pass). | PR head | as above |
| `pr243_base_test.go` | `TestPR243AppRespInSnapshotResendsSnapshot` alone, on the base: it fails (no second snapshot), so the resend is the PR's. | PR base | `cp pr243_base_test.go <checkout>/ && go test -run TestPR243 -v .` |
| `base-d155efc81.log` | its output at the base (the expected failure). | PR base | as above |
| `regen-raftpb.sh` | how `raftpb/raft.pb.go` was regenerated on the fork branch (protoc 3.20.3, protoc-gen-go v1.36.11, gofmt, goimports v0.51.0); it reproduces both `509271dac`'s and `119f42a00`'s `raft.pb.go` byte for byte. | fork | `regen-raftpb.sh <raft checkout> [<tool dir>]` |
| `compare_axioms.py` | the trust-base comparison of the report: `#print axioms` of `Proof/go_etcd_io/raft/v3/Results.lean`, `lean` against this branch (no new axiom, 18 results gain `sorryAx`). | the two builds' `Results.trace` | `python3 compare_axioms.py <lean trace> <branch trace> stepLeader` |

A checkout of a revision: `git -C ~/etcd archive <rev> | tar -x -C <checkout>` (the PR head and base are
in `~/etcd` as `pr-raft-243` and its merge base with `raft-upstream/main`).
