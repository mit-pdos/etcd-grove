# Files for `notes/pr-verify/etcd-21202.md`

Go tests for the findings of the verification of etcd-io/etcd#21202. Revisions: the PR head
`a9522b154` (an etcd-io/etcd checkout; `GOTOOLCHAIN=go1.25.5`, its `go.mod`'s), the fork branch
`mit-pdos/etcd-grove` branch `pr-etcd-21202-goose-lean` (`8c2a55fc5`; `GOTOOLCHAIN=go1.27.1`), and the
pin `09669450f` (the fork's `goose-lean`). Each test is expected to FAIL where it shows a finding.

```
cp <file> <co>/server/storage/mvcc/ && cd <co>/server && go test -count=1 -run <Name> -v ./storage/mvcc/
cp review_21202_etcdutl_test.go <co>/etcdutl/etcdutl/ && cd <co>/etcdutl && go test -count=1 -run TestReview -v ./etcdutl/
```

| File | Test | What it shows | Results |
|---|---|---|---|
| `hash_compactrev_21202_test.go` | `TestHashByRevWithCompactRevBelowStoreCompaction` | finding 1: a store compacted at 10 answers `HashByRevWithCompactRev(5, 3)` with a hash, no `ErrCompacted` (`HashByRev(5)` is `ErrCompacted`) | fails at the PR head and the fork branch; log `hash_compactrev_21202.pr-head.log` |
| same | `TestHashByRevWithCompactRevBelowStoreCompactionDiffers` | finding 1: `(rev 15, compactRev 3)` on a snapshot compacted at 10 and an uncompacted one of the same history: different hashes, no error | fails (PR head, fork) |
| same | `TestHashByRevWithCompactRevAtStoreCompactionAgrees` | control: with `compactRev` = the compacted snapshot's (10) the two agree (the PR's use case) | passes |
| same | `TestHashByRevWithCompactRevEmptyKeepDisagrees` | finding 3: the same with every key deleted at the hashed revision: different hashes (`issues/etcd-hash-empty-keep.md`) | fails (PR head, fork); passes with #22562's one-line filter change applied to the PR head |
| same | `TestHashByRevWithCompactRevAboveRev` | finding 2: `compactRev` above the current revision: `ErrCompacted` with `rev` = current, accepted with `rev` 0 (`CompactRevision` 121 > `Revision` 21) | fails (PR head, fork) |
| same | `TestHashByRevDetailedTotalMatches` | the detailed mode's total hash equals the plain one on decodable data | passes |
| `review_21202_test.go` (reviewer) | `TestReviewDetailedDropsUndecodableValue` | finding 5: a value that does not decode is left out of `--detailed`'s total hash and list (total differs from the plain hash) | fails (PR head, fork); logs `review_21202.mvcc.pr-head.log`, `review_21202.mvcc.fork.log` |
| same | `TestReviewCompactRevMaxInt64Overflow` | finding 6: `compactRev = MaxInt64`, `rev = 0`: `compactRev + 1` wraps, the kept-set filter is off (same hash as `compactRev` 0), reported `CompactRevision` > `Revision` | fails |
| same | `TestReviewCompactRevNotIgnored` | finding 7: the flag's help text ("revisions less than or equal to this value will be ignored") is not what is hashed | fails |
| same | `TestReviewDetailedTombstoneAmbiguous` | finding 8: a txn deleting and putting a key gives two indistinguishable per-key entries (no sub-revision, no tombstone flag) | fails |
| same | `TestReviewUnsafeHashErrorFields` | on an `UnsafeForEach` error `unsafeHashByRevDetailed` returns all-zero fields, `unsafeHashByRev` keeps them (the first statement of the `unsafeHashByRevDetailed` axiom was false; fixed) | fails |
| same | `TestReviewHashCache` | the hash cache's lookup with `compactRev` 0, equal, different | passes |
| `review_21202_etcdutl_test.go` (reviewer) | `TestReviewDetailedStdoutMixed` | finding 9: `hashkv --detailed -w json` writes two JSON documents to stdout | fails; logs `review_21202.etcdutl.pr-head.log`, `review_21202.etcdutl.fork.log` |
| same | `TestReviewOutputFile` | finding 10: `--output` is written 0644, overwritten, and ignored without `--detailed` | passes (shows it) |
| `hash_negative_rev_test.go` | `TestHashByRevNegativeRevision` | `issues/etcd-hashkv-negative-revision.md`: `HashByRev(-5)` returns a hash of nothing, no error | fails at the pin 09669450f; log `hash_negative_rev.log` |
| `existing-hash-tests.pr-head.log` | — | the PR head's own tests: `go test -run Hash ./storage/mvcc/`, `-run 'Check|Hash' ./etcdserver/`, etcdutl | pass |
