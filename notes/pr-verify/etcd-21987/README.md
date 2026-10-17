# etcd#21987: tests and logs

Revisions: the base is the etcd pin of `etc/goose.py` (`09669450f`, the fork's `goose-lean`); the
PR is `mit-pdos/etcd-grove` branch `pr-etcd-21987-goose-lean` (commit `2fc9e9d30`: etcd#21987's
head `fa9871b07`, `tx_buffer.go` and its `tx_buffer_test.go`, applied onto the base). Each test goes in `server/storage/backend/` of a checkout; run from `server/` with
`GOTOOLCHAIN=go1.27.1 go test -count=1 -v -run <Name> ./storage/backend/`.

| File | What it shows |
|---|---|
| `tx_buffer_test.go` | The PR's test file at its head `fa9871b07` (`TestWritebackDedupesIntraBatchDuplicateForNonSeqBucket`: two `put`s of `k` in one write buffer, a read bucket holding `a`, `writeback`, then `txr.Range(k, nil, 1)` must give `NEW`). Fails at the base (returns `OLD`), passes at the PR. |
| `stale_read_test.go` | Copied verbatim from `notes/pr-verify/etcd-22298/`: `TestReadTxStaleAfterDuplicatePut`, the reproduction of `issues/etcd-backend-duplicate-put-stale-read.md` through the public `BatchTx`/`ReadTx` API. Fails at the base, passes at the PR. |
| `review_dup_put_test.go` | Copied verbatim from `notes/pr-verify/etcd-22298/` (that PR's reviewer's `TestReviewDupPut`). At the base the duplicate-put cases fail; at this PR only the last check, `after commit range`, fails: the separate `ConcurrentReadTx` cache bug `issues/etcd-backend-read-buffer-cache-stale-after-commit.md`, which the PR does not touch. |
| `test-base-09669450f.log` | Output at the base of `-run 'TestReadTxStaleAfterDuplicatePut\|TestWritebackDedupesIntraBatchDuplicateForNonSeqBucket\|TestReviewDupPut'` with the three files above copied in, bbolt's debug lines dropped. |
| `test-pr-2fc9e9d30.log` | The same at the PR. |
| `review_extra_test.go` | This PR's reviewer's tests. `TestReviewOverlapManyDups`: 11 puts of `k00` among 20 keys, into a bucket whose read buffer overlaps, so `merge` dedupes, but at the base `sort.Sort` (unstable beyond 12 entries) has already reordered the duplicates and the older `v0` survives; fails at the base, passes at the PR. `TestReviewSeqBucket`: a `putSeq`-only bucket over two batches stays sorted; passes at both. `TestReviewMixedAndReuse`: `put` and `putSeq` into one bucket, reused over later batches; at the base the read buffer is left with `m` twice; passes at the PR. |
| `review-base-09669450f.log`, `review-pr-2fc9e9d30.log` | `-run 'TestReview(OverlapManyDups\|SeqBucket\|MixedAndReuse)'` with `review_extra_test.go` copied in, at the base and at the PR. |
