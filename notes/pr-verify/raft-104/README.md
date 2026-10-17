# Files of the etcd-io/raft#104 verification

Referenced from `notes/pr-verify/raft-104.md`. Revisions:

- PR head: `d9c4b3582a42571b7e5bb9216a1a54707ccc3b82` (`~/etcd` branch `pr-raft-104`, fetched from
  etcd-io/raft `pull/104/head`); its merge base with upstream `main`: `89c97ed7f`.
- Fork: `pr-raft-104-goose-lean` `0997b9505` (the PR on `raft37-goose-lean` `509271dac`, raft v3.7
  with protobuf-go v2 messages), worktree `~/etcd-pr/raft-104`.

Go needs `GOTOOLCHAIN=go1.27.1`. Each `cp` is into a checkout of the named revision (e.g.
`git -C ~/etcd worktree add --detach <dir> <rev>`); remove the file afterwards.

| File | What it shows | Runs against | Command | Recorded result |
|---|---|---|---|---|
| `commit_regression_divergence_test.go` | `TestCommitToClampCommitsDivergentEntries`: after a heartbeat beyond its log, a follower with term-1 entries 2..3 commits and returns them from `nextCommittedEnts`. `TestCommitToClampNeverRepaired`: 50 rounds of heartbeats/appends with a term-2 leader whose `Match` for the follower is 5 leave entries 2..3 divergent | PR head `d9c4b3582`; also its base `89c97ed7f` | `cp commit_regression_divergence_test.go <checkout>/ && go test -run TestCommitToClamp -count=1 .` | `upstream-pr-head.log`: both fail as the report says. `upstream-base.log`: the first panics (`tocommit(5) is out of range`) |
| `no-clamp-upstream.diff` | Counterfactual (by the reviewer): the PR with `l.committed = l.lastIndex()` removed (warning kept) | PR head `d9c4b3582` | `git -C <checkout> apply no-clamp-upstream.diff`, then the command above | `upstream-no-clamp.log`: `TestCommitToClampNeverRepaired` passes (the follower is repaired), so upstream the clamp is what blocks the repair; the first test fails only on its own `committed == 3` assertion |
| `trace-upstream.diff` | The reviewer's tracing variant of the test above (logs leader/follower `MsgApp`/`MsgAppResp` of the first two rounds) | PR head `d9c4b3582` | `cp commit_regression_divergence_test.go <checkout>/ && git -C <checkout> apply trace-upstream.diff && go test -run TestCommitToClampNeverRepaired -v -count=1 .` | (trace only, not recorded) |
| `commit_regression_divergence_v37_test.go` | `TestForkClampNeverRepaired` (by the reviewer): the never-repaired scenario on raft v3.7 | fork `0997b9505` | `cp commit_regression_divergence_v37_test.go ~/etcd-pr/raft-104/ && go test -run TestForkClampNeverRepaired -count=1 .` | `v37-pr.log`: fails, follower committed 3, entries 2..3 divergent |
| `no-clamp-v37.diff` | The same counterfactual on v3.7 | fork `0997b9505` | `git -C ~/etcd-pr/raft-104 apply no-clamp-v37.diff`, then the command above | `v37-no-clamp.log`: still fails (committed 1): on v3.7 the probe floor `Next >= Match+1` blocks the repair with or without the clamp |
| `PrintAxioms.lean` | `#print axioms` of `raftLog.commitTo.wp_proof`, `wp_proof_new`, `spec_implies_old` | this branch, after `lake build Proof.go_etcd_io.raft.v3.raftLog__commitTo` | `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake env lean notes/pr-verify/raft-104/PrintAxioms.lean` | `PrintAxioms.log`: the three rest on the same axioms (axiomatized types only), no `sorryAx` |

Not kept (too large, reproducible): the outputs of `lake env lean Proof/go_etcd_io/raft/v3/Results.lean`
on this branch and on `lean` (5.4 MB each, byte-identical, no `sorryAx`), and the build log of
`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` (success, 1837 jobs).
