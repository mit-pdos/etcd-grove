# Files for the verification of etcd-io/raft#292

These are the supporting files of `../raft-292.md`. No Go test or probe was written for this PR: it
is a refactor, and no PR bug was found to reproduce.

| File | What it shows | Revision | Command |
|---|---|---|---|
| `changed-impls.py` | Lists the 34 functions whose Goose translation the PR changes (the table in the report). | this branch's `Code/go_etcd_io/raft/v3.lean` (translated from fork `pr-raft-292-goose-lean` at `6e71bc940`) against `lean` | `python3 -I notes/pr-verify/raft-292/changed-impls.py [base]`, from the worktree |
| `changed-impls.out` | That script's output. | as above | |
| `go-test.out` | The touched packages' tests pass with the PR applied to the fork. | fork `pr-raft-292-goose-lean` at `6e71bc940` (PR head `1368b97ad` onto `509271dac`) | `cd ~/etcd-pr/raft-292 && GOTOOLCHAIN=go1.27.1 go test -count=1 . ./tracker ./quorum ./confchange` |
| `tcb-check.out` | The trust base matches `etc/tcb-baseline.txt` and the `raft` collection; the PR collection is written. | this branch, after a full `lake build` | `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true etc/tcb-report.py --check`, then `--reuse --collection etc/tcb-collections/raft.txt --check` and `--reuse --collection etc/tcb-collections/pr-raft-292.txt --check --update` |

The proof diff the reviewer read is `git diff lean -- Proof Spec` on this branch.
