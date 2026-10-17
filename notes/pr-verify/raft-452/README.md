# Files for etcd-io/raft#452

The report is `../raft-452.md`. The PR has no Go test or probe written for it: its only code
change is one log level, and the fork worktree has no uncommitted files. What is here is the
check of what the proof rests on.

| File | What it shows | Revision | How to run |
|---|---|---|---|
| `Ax.lean` | `#print axioms` of `unstable.wp_stableTo`, `raftLog.wp_stableTo`, `raft.wp_Step` | this branch, `pr-verify/raft-452` (translation of fork branch `pr-raft-452-goose-lean`, `e8f2206f1` = PR head `a775bccb5` onto `509271dac`); also run on `lean` (`4d7404128`) | in the worktree root: `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake build Proof.go_etcd_io.raft.v3.Link && lake env lean notes/pr-verify/raft-452/Ax.lean` |
| `axioms-pr-branch.txt` | that output on this branch (294, 294 and 304 axioms; no `sorryAx`). The output on `lean` is byte-identical: sha256 `6cecd3b336af825529a7cf4e51043f860d26a2d6f7fd2ec567e911ec84a1a33a` for both | as above | as above, `> axioms-pr-branch.txt` |
| `build-excerpt.txt` | lines of the build of `Proof.go_etcd_io.raft.v3.Link` and `.Results` on this branch: the changed `Code` module and the stableTo/Step specs and proofs rebuilt, no error (the full log is 5.5 MB, not kept) | this branch | `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results` |

Rechecked 2026-10-16: the probe, rerun on this branch, gives `axioms-pr-branch.txt` byte for byte.
