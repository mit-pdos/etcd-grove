# etcd-io/etcd#22291: files the report relies on

The report is `notes/pr-verify/etcd-22291.md`. Revisions: the PR head is etcd-io/etcd
71d57990be7323b6457b3d5fdcedbeba41ae8d28 (upstream base f744d457f484e9f748a0700b48ef96dcf792df33);
the verified fork code is `mit-pdos/etcd-grove` branch `pr-etcd-22291-goose-lean` (commit 69abb3c0a =
the fork pin 09669450f, `etc/goose.py`'s etcd pin, plus the PR); the pin itself is 09669450f.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `lease_requireleader_pairing_internal_test.go` | `closeRequireLeader` pairs a kept channel with another subscription's context (`ka.ctxs[newIdx]`, etcd#22081): after one leader loss a plain subscriber's channel carries the require-leader context, and a second leader loss closes it. Fails on all three revisions; with the PR, the second loss also deletes the entry (the plain subscriber's lease is no longer renewed). | the pin 09669450f, upstream f744d457f, the PR head 71d57990b | `cp lease_requireleader_pairing_internal_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -run TestLessorCloseRequireLeader -v .` |
| `lease_review_internal_test.go` (the reviewer's) | `TestReviewFromOutgoingContextNotDeterministic`: grpc's `metadata.FromOutgoingContext` is not a function of the context value (mutating the `MD` given to `NewOutgoingContext` changes later results; keys equal up to case merge in map order), why its axiom here takes the premise `metadata.outgoingStable`. `TestReviewDeletedEntryDonecNotClosed`: the PR's delete path leaves `ka.donec` open, so the deleted subscriptions' `keepAliveCtxCloser` goroutines stay blocked until their contexts end (as before the PR, behind the orphan). `TestReviewMixedCase`: etcd#22081 at work (after a leader loss, cancelling the plain subscriber's context does not close its channel; a second leader loss closes it, and with the PR deletes the entry). The tests pass; they print what they observe. | the PR head 71d57990b and upstream f744d457f | `cp lease_review_internal_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -race -v -run 'TestReview' .` |
| `review-tests.log` | that file's output at the head and at the base, then the PR's test failing at the base | as above | as above |
| `pairing-fork-pin.log` | that test's output on the pin 09669450f (the entry left with no channel, `&{[] [] ...}`: the orphan of etcd#22094 as well) | the pin | as above |

The PR's own test, `TestLessorCloseRequireLeaderRemovesOrphanedKeepAlive`
(`client/v3/lease_requireleader_internal_test.go` at the PR head, also on the fork branch), fails on
upstream f744d457f and passes on the PR head and on the fork branch (`go test -count=1 -race -run
'Lease|Lessor|KeepAlive' .` in `client/v3`).
