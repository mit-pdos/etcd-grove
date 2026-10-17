# Files for etcd-io/raft#285

These are the files behind `notes/pr-verify/raft-285.md`. No Go test was written for this PR:
it is a refactor and no bug was found in it.

| File | What it shows | Revision | How to run |
|---|---|---|---|
| `astdiff/main.go` | A scratch program that lists the top-level declarations (functions, methods, types, vars) whose printed AST differs between two directories of Go files, ignoring `_test.go` files and comments. This gave the report's table of changed functions. | Old: the fork's `509271dac` (`raft37-goose-lean`). New: the fork's `e3670378d` (`pr-raft-285-goose-lean`, the PR applied). | `git -C ~/etcd archive 509271dac \| tar -x -C /tmp/old`, then `cd astdiff && for d in . confchange quorum tracker; do go run main.go /tmp/old/$d ~/etcd-pr/raft-285/$d; done` |
| `astdiff.log` | The output of that program. | As above. | |
| `vet-pr-head.log` | `go vet ./...` at the PR's head reports three "quorum.JointConfig struct literal uses unkeyed fields" (`tracker/tracker.go:108`, `:134`, `rawnode_test.go:733`). | Upstream PR head `aa1073bb101b9cc22b035a0d9a9c0019dbbb6ecd`. | `git -C ~/etcd fetch raft-upstream pull/285/head:pr-raft-285`, then in a checkout of it: `GOTOOLCHAIN=go1.27.1 go vet ./...` |
| `vet-base.log` | `go vet ./...` at the PR's merge base is clean (exit 0). | Upstream `8fa0e55daaf70c766fdbbff1e8598b07e5b73588`. | The same command at that revision. |

Two limitations of `astdiff.log`:

- The program keys declarations by name only. In `state_trace.go` the `with_tla` and
  `!with_tla` files declare the same names, so every `trace*` entry under `.` is noise from that
  collision. Of those, the PR changes only `traceEvent` and `traceConfChangeEvent`, both in the
  `with_tla` file.
- `changed ` with an empty name is the import declarations.
