# Files for the verification of etcd-io/etcd#22485

The report is `../etcd-22485.md`. The fork branch is `mit-pdos/etcd-grove` branch
`pr-etcd-22485-goose-lean` (commit 0d8894d1d: the PR's `raft.go` change at its head ef57d9843,
applied cleanly onto the Goose fork's `goose-lean` at 09669450f).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `raft_order_test.go` | The PR's `TestProcessMessagesKeepsReadyOrder` (commit 501702689), alone in a file: `processMessages` returns the kept messages in the `Ready`'s order, the same pointers, with the inputs unchanged | any checkout of `server/etcdserver` (it uses the package's test helpers `newNopReadyNode`, `newNopTransporter`) | `cp raft_order_test.go <checkout>/server/etcdserver/ && cd <checkout>/server && GOTOOLCHAIN=go1.27.1 go test ./etcdserver/ -run TestProcessMessagesKeepsReadyOrder -count=1` |
| `base.log` | The test **fails** on the code before the PR (all three cases: `got[0] is not the Ready pointer`, the messages come back reversed); the `expected`/`actual` message dumps are cut | the fork's `goose-lean` at 09669450f (the pinned etcd revision of `etc/goose.py`), same code as upstream `main` for this function | as above |
| `fork.log` | The test, and the existing `TestProcessDuplicatedAppRespMessage`, **pass** with the PR applied | fork branch `pr-etcd-22485-goose-lean` (0d8894d1d) | as above, `-run 'TestProcessMessagesKeepsReadyOrder\|TestProcessDuplicatedAppRespMessage' -v` |

The PR's own tests (`go test ./etcdserver/` of `server/`, with the PR's `raft_test.go` hunk applied)
also pass on the fork branch.
