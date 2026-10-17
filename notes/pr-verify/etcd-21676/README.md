# Files for `notes/pr-verify/etcd-21676.md`

Revisions: PR head = etcd-io/etcd `64514520baeb6996c968f73eb8b0cd40a270b103`; upstream base =
`e775342652a19f92f10202c576efbe9ffc33989e` (the PR's merge base with `main`); fork branch =
`mit-pdos/etcd-grove` branch `pr-etcd-21676-goose-lean` (`96f3da8d6`: the fork's `goose-lean`
`09669450f` plus the PR, its `ringbuffer_test.go` included). The tests use the helpers of the
PR's `cache/ringbuffer_test.go` (`setupRingBuffer`, `makeEventBatch`, `collectRevisions`), so
they run only next to it: on the PR head or the fork branch. Go toolchain `go1.26.4` (the PR
head's `go.mod`); the fork branch builds with `go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `ringbuffer_pr21676_probe_test.go` | `TestReplaceLatestBreaksOrdering`: `ReplaceLatest` with a revision below the previous entry's (5, 10 → 5, 3) is accepted, after which `AscendGreaterOrEqual(4)` visits revision 3 and `RemoveLess(4)` keeps it. `TestEnsureCapacityOverflowHangs`: `ensureCapacity(1<<62 + 1)` on a ring of length 1 does not return (the doubling overflows to 0 and loops) | PR head (both fail) | `cp ringbuffer_pr21676_probe_test.go <checkout>/cache/ && cd <checkout>/cache && go test -count=1 -run 'TestReplaceLatestBreaksOrdering\|TestEnsureCapacityOverflowHangs' .` |
| `probe-output.txt` | the output of the command above on the PR head | PR head | as above |
| `ringbuffer_pr21676_review_huge_test.go` | (reviewer) `TestReviewEnsureCapacityHugeNonPow2`: with a non-power-of-two length (3), the same `minCapacity` makes `make` panic (`makeslice: len out of range`) rather than hang; the test passes, logging the panic | PR head | `cp ringbuffer_pr21676_review_huge_test.go <checkout>/cache/ && cd <checkout>/cache && go test -count=1 -v -run TestReviewEnsureCapacityHugeNonPow2 .` |
| `ringbuffer_pr21676_review_model_test.go` | (reviewer) `TestReviewRingBufferModel`: 2000 random runs of `Append` and the four new methods against a list model, callers keeping the verified premises; contents, `Len`, the peeks and head/tail/size consistent after every step (passes) | PR head | `cp ringbuffer_pr21676_review_model_test.go <checkout>/cache/ && cd <checkout>/cache && go test -count=1 -run TestReviewRingBufferModel .` |
| `review-tests-output.txt` | the output of both reviewer tests (`-run TestReview -v`) on the PR head | PR head | as above |

On the fork branch, `go build ./...`, `go vet .` and `go test .` in `cache/` (the PR's tests
included) pass.
