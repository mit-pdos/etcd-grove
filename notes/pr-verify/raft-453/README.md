# Files for the verification of etcd-io/raft#453

The report is `../raft-453.md`.

| File | What it shows |
|---|---|
| `pr453_findings_test.go` | Two Go tests of the PR's behavior (package `raft`, file goes at the root of etcd-io/raft). `TestPR453BatchWithRejectedConfChange`: a `MsgProp` of a normal entry and a refused conf change returns `ErrConfChangeRejected`, yet both entries (the normal one, and the empty replacement) are appended (finding 2). `TestPR453NodeProposeConfChangeRejectedReturnsNil`: `Node.ProposeConfChange` of a refused change returns `nil` (the error is dropped, finding 1), while `RawNode.ProposeConfChange` returns `ErrConfChangeRejected`. Both tests pass, which confirms the behavior. |
| `pr453_findings_test.out` | Their output at the PR head (`go test -count=1 -run TestPR453 -v .`, filtered to the result lines). |

Revision: PR head `d6e469644a172b0deb311205780639cb49e207c9` (etcd-io/raft, `git fetch https://github.com/etcd-io/raft pull/453/head`), whose upstream base is `3f4062b3c`. The tests also apply to the fork branch `pr-raft-453-goose-lean` (`1f4e8492e`). They do not compile before the PR, because `ErrConfChangeRejected` does not exist there.

Run:

    cp pr453_findings_test.go <etcd-io/raft checkout at d6e469644>/
    cd <checkout> && GOTOOLCHAIN=go1.27.1 go test -count=1 -run TestPR453 -v .
