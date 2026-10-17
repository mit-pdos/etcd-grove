# PR etcd-io/raft#88: probes

Go tests (package `raft`, internal) against the PR's head `ddd5443cdbc9ebab0dda6a315b19043d193b0b62`
(etcd-io/raft, by-value `pb.Message` callback). Each **fails** when the problem it shows is present.

Run: in a checkout of etcd-io/raft at the PR head (`git fetch https://github.com/etcd-io/raft
pull/88/head && git checkout FETCH_HEAD`), copy the file into the repository root and

    GOTOOLCHAIN=go1.27.1 go test -count=1 -run 'TestPR88' -v .

| File | What it shows | Result at the PR head |
|---|---|---|
| `pr88_reentry_probe_test.go` | A callback that consults the node (`n.Status()`, a natural "am I still leader?" check) wedges the node: the callback runs on `node.run` inside `Step`, and `Status` waits for that same loop. `Propose` times out, and `Status` from any goroutine never returns. | FAIL: `node wedged ...` |
| `pr88_review_mutation_test.go` (written by the review subagent) | The callback gets the message by value, but `Entries` and each entry's `Data` share storage with the proposal raft forwards (and the caller's slice): an edit there, with `false` returned, changes the forwarded proposal; edits of scalar fields are silently lost. | FAIL: `forwarded: ... ents="mutated","Xbc"` |

Neither is excluded by the `Config` documentation the PR adds; the verified contract (`pfcbSpec`,
`Proof/go_etcd_io/raft/v3/InvRaftPhys.lean`) excludes both (no access to raft's state, the message
given back unchanged), and a hang is outside what a partial-correctness triple excludes.
