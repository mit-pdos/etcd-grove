# etcd-io/etcd#21126: files the report relies on

The report is `notes/pr-verify/etcd-21126.md`. Revisions:

- the PR head: etcd-io/etcd 15e720e9cca16b3abfad782a5eedfdc98b347304 (upstream base
  34141c24b113de5a8f0c375bafdcc572975a5c03);
- the verified fork code: `mit-pdos/etcd-grove` branch `pr-etcd-21126-goose-lean`, commit
  ee79336e9 (the fork pin 09669450f plus the PR, including its `tests/integration/clientv3/lease/lease_test.go`).

The three `_test.go` files are copied verbatim from `pr-verify/etcd-22087`
(`notes/pr-verify/etcd-22087/`), where they were written for etcd#22291/#22087; they test the same
function and bugs.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `lease_requireleader_internal_test.go` | (etcd#22291's test) etcd#22094: an entry all of whose subscriptions required a leader must leave `l.keepAlives`. Fails at the base, passes at the PR head and on the fork branch. | 34141c24b, 15e720e9c, ee79336e9 | `cp lease_requireleader_internal_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -count=1 -v -run TestLessorCloseRequireLeader .` |
| `lease_requireleader_pairing_internal_test.go` | etcd#22081: after one leader loss a plain subscriber's channel is paired with the require-leader subscriber's context, and a second leader loss closes it. Fails at the base, passes at the head and on the fork branch. | same | as above |
| `lease_requireleader_ctxcloser_review_internal_test.go` | (the etcd#22087 reviewer's) `TestReviewCtxCloserAfterCloseRequireLeader`: cancelling the require-leader subscriber's context after a leader loss closes the plain subscriber's channel at the base; `TestReviewOrphanReapedOnlyByCtxCloser`: an emptied entry stays in the map at the base. Both fail at the base and pass at the head and on the fork branch. | same | `... go test -count=1 -v -run TestReview .` |
| `tests.log` | the output of the three files on the three revisions (`GOTOOLCHAIN=go1.27.1` on the fork, `go1.25.5`, the `go.mod` toolchain, upstream), and of the PR's integration test `TestLeaseKeepAliveAndExpirationWithNoLeader` at the base with the PR's `lease_test.go` copied in: subtest "lease expires when both keepAlives require leader" fails there (TTL=8, the lease still renewed), the mixed subtest passes | | `cd <checkout>/tests && go test -count=1 -v -run TestLeaseKeepAliveAndExpirationWithNoLeader ./integration/clientv3/lease/` |
| `fork-gotest.log` | on the fork branch: `go build ./...`, `go test -race -run 'Lease\|Lessor\|KeepAlive\|CloseRequireLeader' .` in `client/v3`, and the PR's integration test, all passing | ee79336e9 | as in the log |
| `lease_closerequireleader_review21126_internal_test.go` (this run's reviewer) | `TestReview21126MixedSecondLeaderLoss` (a second leader loss leaves the plain subscriber open), `TestReview21126MixedCancelPlain` (cancelling the plain subscriber's context closes its channel and removes the entry), `TestReview21126AllRequireLeaderDeleted` (the all-require-leader entry is removed), `TestReview21126DeletedThenResubscribe` (after the delete, a new `KeepAlive` for the same id is not disturbed by the old subscription's `keepAliveCtxCloser`). The first three fail at the base and pass at the head and the fork branch; the last passes on all three. The first two exercise the `ctxs[i]` fix, which the PR's own integration test does not. | 34141c24b, 15e720e9c, ee79336e9 | `cp lease_closerequireleader_review21126_internal_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && go test -count=1 -v -run TestReview21126 .` |
| `review-tests.log` | that file's output on the three revisions | | as above |
