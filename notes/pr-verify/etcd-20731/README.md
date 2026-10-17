# Files for the verification of etcd-io/etcd#20731

Each test is a file of package `clientv3` (`client/v3/`), to copy into a checkout and run there.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `backoff_pr20731_test.go` | the PR's findings 1-4 (report, "Findings"): a `BackoffWaitBetween` above 5s capped to 5s with the default exponent (`TestPR20731DefaultExponentCapsLargeWaitBetween`, fails); the first wait is generation 1 (`TestPR20731FirstBackoffIsGenerationOne`, logs); `BackoffMaxWaitBetween = math.MaxInt64` gives a negative, i.e. no, wait once capped (`TestPR20731HugeMaxWaitBetweenGivesNegativeBackoff`, fails on amd64); an exponent below 1 shrinks the wait (`TestPR20731ExponentBelowOneShrinks`, logs) | the PR head `58e2a6a28` (upstream checkout) | `cp backoff_pr20731_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && GOTOOLCHAIN=go1.26.4 go test -v -run PR20731 .` |
| `pr-head.log` | that test's output at the PR head (linux/amd64) | `58e2a6a28` | as above |
| `backoff_base_test.go` | before the PR, a 10s `BackoffWaitBetween` gives a 10s wait (`TestBaseLargeWaitBetweenNotCapped`, passes) | the PR's base `374dd8087` | `cp backoff_base_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && GOTOOLCHAIN=go1.26.4 go test -v -run TestBase .` |
| `base.log` | that test's output at the base | `374dd8087` | as above |
| `review_pr20731_test.go` | the reviewer's tests (report, findings 5-7 and the notes): jitter applied after the cap gives waits above `BackoffMaxWaitBetween` (`TestReviewJitterExceedsMax`); a max of 9e18 ns (below `MaxInt64`) already overflows in `jitterUp` (`TestReviewLargeMaxJitterOverflow`); exponent 0.5 reaches a 0 wait by attempt 25 (`TestReviewSmallExponentZeroWait`); infinite exponent/jitter (`TestReviewInfInputs`); the quorum changing with the endpoints mid-sequence (`TestReviewQuorumChange`); a nil logger panics, as before the PR (`TestReviewNilLoggerPanics`). All log and pass | `58e2a6a28` | `cp review_pr20731_test.go <checkout>/client/v3/ && cd <checkout>/client/v3 && GOTOOLCHAIN=go1.26.4 go test -v -run TestReview .` |
| `review.log` | that test's output (linux/amd64) | `58e2a6a28` | as above |
