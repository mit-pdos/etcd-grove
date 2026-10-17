# etcd#22298: tests and logs

Revisions: the base is the etcd pin of `etc/goose.py` (`09669450f`, the fork's `goose-lean`); the
PR is `mit-pdos/etcd-grove` branch `pr-etcd-22298-goose-lean` (commit `01a459f07`: etcd#22298's
head `586e7a5ac` applied onto the base, `tx_buffer.go` and the PR's `tx_buffer_test.go`). Each
test goes in `server/storage/backend/` of a checkout; run from `server/` with
`GOTOOLCHAIN=go1.27.1 go test -run <Name> ./storage/backend/`.

| File | What it shows |
|---|---|
| `stale_read_test.go` | `TestReadTxStaleAfterDuplicatePut`, the reproduction of `issues/etcd-backend-duplicate-put-stale-read.md`: two `UnsafePut`s of one key in one lock session, into a bucket whose read-buffer entry survived the last commit; `ReadTx` reads the older value. Fails at the base, passes at the PR. |
| `review_dup_put_test.go` | `TestReviewDupPut` (the reviewer's): duplicate puts into an emptied and into a non-empty read bucket, `UnsafeSeqPut` and `UnsafePut` of one key mixed in one session, a range over a safe-range bucket with a key put twice, through `ReadTx` and `ConcurrentReadTx`. At the base the first, third and fourth cases fail (older value, or the key twice in a range); at the PR all pass but the last check, `after commit range`, which is the separate `ConcurrentReadTx` cache bug `issues/etcd-backend-read-buffer-cache-stale-after-commit.md` (not touched by the PR). |
| `test-base-09669450f.log` | The output at the base of `-run 'TestReadTxStaleAfterDuplicatePut|TestWritebackDedupesExistingBucket|TestReviewDupPut'` (with the PR's `tx_buffer_test.go` copied in), bbolt's debug lines dropped. |
| `test-pr-01a459f07.log` | The same at the PR. |
