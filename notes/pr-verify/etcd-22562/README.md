# Files for `notes/pr-verify/etcd-22562.md`

Go tests for the findings of the verification of etcd-io/etcd#22562, all in package
`go.etcd.io/etcd/server/v3/storage/mvcc`. To run one against a checkout `<co>` (an etcd-io/etcd
checkout at the revision named, or the fork branch `mit-pdos/etcd-grove` branch
`pr-etcd-22562-goose-lean`):

```
cp <file> <co>/server/storage/mvcc/ && cd <co>/server && GOTOOLCHAIN=go1.27.1 go test -count=1 -run <Name> ./storage/mvcc/
```

| File | Test | What it shows | Results |
|---|---|---|---|
| `hash_empty_keep_test.go` | `TestHashByRevEmptyKeepMatchesCompactionHash` | a key put at 2, compacted at 2, deleted at 3: `HashByRev(3)` before compacting at 3 must equal the hash the compaction at 3 stores (same `Revision` 3, `CompactRevision` 2) | fails at the fork pin 09669450f (`0x53cd23ab` vs stored `0xb08e9997`) and at #22515's head de2627f9f; passes at #22562's head e35b5916f and on `pr-etcd-22562-goose-lean` |
| `hash_fuzz_22562_test.go` | `FuzzCompactionHash` | #22562's fuzz test verbatim (needs `hashTestCase` of `hash_test.go`, present at all three revisions); its seeds, `go test -run FuzzCompactionHash` | seed#1 fails at the pin and at #22515's head ("hash changed at revision 7"); passes at #22562's head |
| `hash_physical_compaction_22515_test.go` | `TestHashByRevAcrossPhysicalCompaction` | #22515's test verbatim: `HashKV` the same during and after a physical compaction, and after it equal to the hash older versions return | at the pin: the cases "every key deleted at/after the compact revision" fail ("hash during the compaction"); at #22562's head (and the fork branch): "every key deleted after the compact revision" fails ("hash after the compaction": `0xa934d75d`, older versions `0x4803ce7`); passes at #22515's head |
| `hash_review_test.go` | `TestReviewHashProgressAndRestart`, `TestReviewHashRestartMidCompaction` | the reviewer's randomized check (3000 seeds, keys `a`,`b`,`c`): compactions at `c0` then `c1` queued; `HashKV` with nothing deleted, part of `c0`'s deletions, after `c0`, after `c1`, after a restart; `c1`'s stored hash against `HashKV(c1)` at `c0`; with and without txns that delete and put a key in one revision (`delPut`); and a restart with a prefix of a compaction's deletions done | log `hash_review.log`: at #22562's head 0 of 3000 fail without delete-then-put, 69 with it (`issues/etcd-compaction-delete-then-put.md`), restart 0; at #22515's head 164 without (all "stored hash != HashKV"), 200 with |

(Do not copy `hash_fuzz_22562_test.go` into #22562's own checkout: its `hash_test.go` already
defines `FuzzCompactionHash`.)
