# Files for the verification of etcd-io/raft#155

The report is `../raft-155.md`. Revisions:

- **new**: the fork `upamanyus/etcd` branch `pr-raft-155-goose-lean`, commit `9e87f483a`. This is
  the PR at head `85f43e65740047a9ff7301c9580d67b4b62b02df` applied to `raft37-goose-lean`.
- **old**: that commit's parent `509271dac`, the pinned raft v3.7.0 plus the read-index fix.

Run the Go commands with `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `log_malformed_append_test.go` | `raftLog.maybeAppend` on three malformed appends (duplicate index, gap, entry below `prev`). It logs the outcome instead of asserting, so the same test runs at both revisions. This is the report's "Findings" | new and old | `cp log_malformed_append_test.go <checkout>/ && go test -run TestMaybeAppendMalformed -count=1 -v .` |
| `output-new.txt` | that test's output at **new**: the duplicate case returns `(7, true)` with `lastIndex` 6 (the log is truncated); gap and below-prev panic | new (`9e87f483a`) | as above |
| `output-old.txt` | that test's output at **old**: the duplicate case returns `(7, true)` with `lastIndex` 10 (a no-op); gap panics through `Panicf`; below-prev returns `(3, true)` | old (`509271dac`) | as above, after `git checkout 509271dac` |
| `log_test.go.diff` | the PR's `log_test.go` change (`TestFindConflict`) ported to pointer entries (`[]*pb.Entry`); it is in commit `9e87f483a` | new | `go test -run TestFindConflict .` in the fork worktree at `9e87f483a` |
| `chk.sh` | the helper used during the proof work: elaborate one Lean file of the worktree with `lake env lean` and print its messages | this branch | `notes/pr-verify/raft-155/chk.sh <file.lean> [lines]` (edit the `cd` path for another worktree) |

All three Go outputs were re-checked on 2026-10-16 at the revision stated.
