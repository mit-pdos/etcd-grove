# Files for the verification of etcd-io/etcd#22475

The report is `notes/pr-verify/etcd-22475.md`. Revisions: the PR head is `8771861579db6a2b4e635fa56abbc4eb7c7d33e1`
and the upstream merge base is `88235ecd0c1031cc0293f3887ef11dab64b14758`. The verified fork commit is `6c9a29b7a`
(`mit-pdos/etcd-grove` branch `pr-etcd-22475-goose-lean`): the PR applied to the fork's `goose-lean` `09669450f`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `kvstore_live_payload_random_test.go` | `TestLiveKVPayloadRandomized` runs 40 random histories with `restoreChunkKeys = 7`, so restore evicts entries from its cache. The histories mix puts (including empty values), deletes, range deletes, multi-op txns, compactions at random revisions, restarts and `Restore`. After every step the test checks `liveKVPayloadGauge` against the sum of `len(key)+len(value)` from a full `Range`. It covers the restore path, which the proof leaves untranslated. | PR head and fork branch: passes. A mutation of `restoreIntoIndex` (`liveSize += newSize` without subtracting the old size) fails it at the first restart. It does not build on the base, which has no gauge. | `cp kvstore_live_payload_random_test.go <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test ./storage/mvcc/ -run TestLiveKVPayloadRandomized` |
| `kvstore_live_payload_random_test.pr.log` | the run above | PR head | as above, with `-v` |
| `kvstore_live_payload_review_test.go` (reviewer) | `TestLiveKVPayloadTwoStoresShareGauge`: two stores in one process share the gauge. Restarting one store resets the other's part, and the gauge goes negative (it logs the values; the test passes by design). `TestLiveKVPayloadPartialCompactionResume`: a crash at every prefix of a scheduled compaction's deletes, then restart and the resumed compaction; the gauge stays exact. | PR head: both pass | `cp kvstore_live_payload_review_test.go <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test ./storage/mvcc/ -run 'TestLiveKVPayloadTwoStoresShareGauge\|TestLiveKVPayloadPartialCompactionResume' -v` |
| `kvstore_live_payload_review_test.pr.log` | the reviewer's tests on the PR head | PR head | as above |

Go: `GOTOOLCHAIN=go1.27.1`.
