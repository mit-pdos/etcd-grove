# Files for `notes/pr-verify/etcd-22515.md`

Go tests for the verification of etcd-io/etcd#22515, all in package
`go.etcd.io/etcd/server/v3/storage/mvcc`. To run one against a checkout `<co>` (an etcd-io/etcd
checkout at the revision named, or the fork branch `mit-pdos/etcd-grove` branch
`pr-etcd-22515-goose-lean`):

```
cp <file> <co>/server/storage/mvcc/ && cd <co>/server && GOTOOLCHAIN=go1.27.1 go test -count=1 -run <Name> ./storage/mvcc/
```

Revisions: the fork pin `09669450f` (etcd `goose-lean`), #22515's head `de2627f9f`, #22562's head
`e35b5916f`.

| File | Test | What it shows | Results |
|---|---|---|---|
| `hash_physical_compaction_22515_test.go` | `TestHashByRevAcrossPhysicalCompaction` | #22515's own test, verbatim (copied from `pr-verify/etcd-22562`): `HashKV` the same during and after a physical compaction, and after it equal to the hash older versions return | passes at #22515's head and on `pr-etcd-22515-goose-lean`; at the pin the cases "every key deleted at/after the compact revision" fail; at #22562's head "every key deleted after the compact revision" fails (hash after the compaction changed) |
| `hash_empty_keep_test.go` | `TestHashByRevEmptyKeepMatchesCompactionHash` | (from `pr-verify/etcd-22562`) a key put at 2, compacted at 2, deleted at 3: `HashByRev(3)` before compacting at 3 vs the hash the compaction at 3 stores: symptom 1 of `issues/etcd-hash-empty-keep.md` | fails at the pin, at #22515's head and on `pr-etcd-22515-goose-lean` (`fork_tests.log`); passes at #22562's head |
| `hash_review_test.go`, `hash_review.log` | `TestReviewHashProgressAndRestart`, `TestReviewHashRestartMidCompaction` | (the #22562 reviewer's, from `pr-verify/etcd-22562`) randomized: two queued compactions, `HashKV` at every stage of the deletions, the stored hash of `c1` vs `HashKV(c1)`, restarts mid-compaction | at #22515's head: 164/3000 fail without delete-then-put, all "stored hash of c1 != HashKV(c1)" (symptom 1); restart 0/3000. Same on the fork branch (`fork_tests.log`) |
| `fork_tests.log` | the three files above plus `hash_fuzz_22562_test.go` (#22562's `FuzzCompactionHash`, from `pr-verify/etcd-22562`) | run on `pr-etcd-22515-goose-lean` (`9b2831b97`): the fork rewrite gives the PR head's results | as above; `FuzzCompactionHash` seed#1 fails (symptom 1) |
| `hash_review_22515_test.go`, `hash_review_22515.log` | `TestR22515Dump`, `TestR22515Progress`, `TestR22515Concurrent`, `TestR22515Symptom1` | this PR's reviewer: finished-compaction hashes identical to the pin's over 3000 random histories (`R22515_OUT=<file>` writes the dump, diff the two runs); no progress dependence (random/prefix partial deletions, and a real concurrent `Compact` with hashing goroutines); symptom 1 unchanged | pin vs PR dumps identical; progress 0/3000 at PR vs 1037/3000 at the pin; concurrent 0/300 vs 78/300; symptom 1 at both |

(Do not copy `hash_review_22515_test.go` and `hash_review_test.go` into a checkout together
unless their helper names do not clash; run them one at a time.)
