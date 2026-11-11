# `schema.MustUnsafeGetAllLeases` (axiom review, 2026-11-05)

**Reviewed** (branch `lease-expiry` at `f5eec16dd1`, the stage under review): the axiom
`schema.MustUnsafeGetAllLeases.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/storage/schema/
MustUnsafeGetAllLeases.lean`, its triple in `Spec/.../storage/schema/MustUnsafeGetAllLeases.lean`),
with the specs around it: `schema.UnsafeCreateLeaseBucket` (proved: a wrapper over `tx`'s
`UnsafeCreateBucket` contract), `schema.MustUnsafePutLease` (the axiom that writes the records the
premise speaks of), `lease.lessor.initAndRecover` and `lease.lessor.Recover` (proved, over this
axiom), and the backend's `batchTxBuffered.Lock`/`LockOutsideApply`/`Close` (who may hold
`batchLocked`). Go at the etcd pin (`upamanyus/etcd` `673da07`: `server/storage/schema/lease.go:31-46`,
`server/storage/backend/batch_tx.go:250-262`, `server/lease/leasepb/lease.pb.go`), bbolt and
protobuf-go as `examples/go.mod` resolves them, `GOTOOLCHAIN=go1.27.3`.

**Verdict: survives** every attack tried. No counterexample; the Go checks are in
`examples/axiomcx/getallleases/getallleases_test.go` (tests only, no Goose project).

## The claims

1. Premise: the batch lock held at `st` (`batchLocked γ P b st`), `t` the backend's `batchTx`, the
   variable `schema.Lease` the bucket `bi`, and `bktEnts (bktOf st.S bi.name) = recs.map
   leaseRecEnc`: the writer's contents of the bucket, in key order (`GoStringLt`), are exactly the
   records `((u64Le id).reverse, leaseEnc id ttl rem)`.
2. No panic.
3. `batchLocked γ P b st` back unchanged.
4. A slice `s ↦* ps`, `|ps| = |recs|`, each `p ↦ v` (whole message, existential) with `v.ID',
   v.TTL', v.RemainingTTL'` the record's, in the records' order. Fresh: no sharing with bbolt or
   with each other.

## Attacks tried

| # | attack | result |
|---|---|---|
| 1 | **Missing bucket** (no `UnsafeCreateLeaseBucket`): Go's `unsafeForEach` checks `tx.Bucket(...) != nil` and returns `nil`; `bktOf` of an absent bucket is `∅`, so `recs = []` | agrees: Go returns an empty non-nil slice (`TestMissingBucket`) |
| 2 | **Empty bucket**, and `UnsafeCreateLeaseBucket` twice | agrees (`TestEmptyBucket`) |
| 3 | **Order**: ids `-1` (key `ff..ff`), `MinInt64` (`80 00..`), `0x100`, `5`, `1`, `0`; a signed-byte, length-first or little-endian order would differ. `GoStringLt` is `List.Lex` on `uint.Z` of the bytes, as `bytes.Compare` / bbolt | agrees, before a commit (the writer's uncommitted puts: `st.S`), after a commit, after a reopen (`TestOrderAndValues`) |
| 4 | **Values at the edges**: negative TTLs (10-byte varints), the all-zero message (the empty encoding, an empty bbolt value) | decoded exactly (`TestOrderAndValues`) |
| 5 | **Aliasing of the results with bbolt's pages**: read, rewrite every record, commit, grow the file to ~128 MB (several mmap remaps), delete the records; and write the second read's messages | the first read is unchanged; the messages have only `int64` fields, which `proto.Unmarshal` copies (`TestNoAliasing`) |
| 6 | **Aliasing between results**: `var lpb` is the closure's local, a new variable per call | the pointers are distinct (`check` in every test) |
| 7 | **Undecodable value** (`0xff`) | Go panics (`failed to Unmarshal lease proto item; lease ID=0000000000000003`, `TestUndecodable`): the premise is needed, and excludes it: `leaseEnc` is `opaque`, so no proof can equate other bytes with an encoding, and `MustUnsafePutLease` is the only writer whose spec yields `leaseEnc` |
| 8 | **Non-injective `leaseEnc`** (two `recs` for one bucket, the proof picking the wrong one): the keys fix the ids; `leaseEnc` is opaque, so no two triples can be proved to encode alike (and `proto.Marshal` of three `int64` fields is injective in Go) | not exploitable |
| 9 | **Unknown fields** (a value the premise cannot describe but Go decodes): Go keeps them, copied (`TestUnknownFields`); `MustUnsafePutLease` requires `unknownFields' = slice.nil`, so `leaseEnc` is only ever the plain encoding; the post's existential `v` says nothing of `unknownFields'`, weaker than Go (nil), not stronger | not exploitable |
| 10 | **Keys not the ids' bytes** (a 3-byte key, id 7 under the key of 9) | Go does not panic (`bytesToLeaseID` runs only on a decode error, `TestOddKeysDecodable`); the premise excludes the state anyway |
| 11 | **After `Close`**: in Go, `Lock` then `MustUnsafeGetAllLeases` after `be.Close()` dereferences the stopped transaction: `runtime error: invalid memory address or nil pointer dereference` (`TestAfterClose`) | excluded: `batchLocked` comes only from `Lock`/`LockInsideApply`/`LockOutsideApply`, which take `bOpen γ qo`; `Close` takes `bOpen γ 1`; `batchFree`'s stopped disjunct (`bStopped`) is never the held state. Holding `batchLocked` across `Close` makes Go deadlock (the stop's `CommitAndStop` waits for the lock), not panic |
| 12 | **Unlocked access / concurrent writers**: `batchLocked` holds `sync.ownMutex (muOf t)`; `UnsafeForEach` reads `t.tx` (`batchPhys`), bbolt's writer, whose contents `ownWTx … st.S` are | no gap at this axiom (bbolt's own triples are `notes/axiom-review/bbolt.md`'s) |
| 13 | **The pre-commit hook**: it runs with `Pk`, not `batchLocked`, and writes only `meta`; `mvcc.leaseParams` makes the `lease` bucket none of the hook's | not reachable |
| 14 | **Callers**: `initAndRecover` passes `rbPart`'s `r`, equal to `st.S` on `lease` (`rbData`); `recMap` needs distinct ids, which `leaseRecs_nodup` proves from the bucket's keys; the only exported use (the snapshot walk, `SnapApplyWalk.lean:431`) is at `recs = []` | consistent |

**Not tried**: a nested bucket inside `lease` (bbolt's `ForEach` gives `v = nil`, which decodes as
the zero message): the backend's API creates only top-level buckets, and `BktData` has no nested
buckets; `LockOutsideApply`'s verification panic inside apply (`Recover` runs in the apply thread;
`ENV_VERIFY` off by default; `LockOutsideApply`'s spec, not this one); bbolt's and protobuf-go's own
correctness beyond what the tests exercise.

## Notes

- The post is weaker than Go in two harmless ways: `unknownFields'` of each message is not said to
  be nil, and the slice's capacity tail is not returned. A caller that wanted to re-put a recovered
  message (`MustUnsafePutLease` needs `unknownFields' = slice.nil`) could not; none does (`Recover`
  copies the fields into a new `Lease`).
- Test output (`go test -v -count=1 ./axiomcx/getallleases/`):

```
--- PASS: TestMissingBucket (0.08s)
--- PASS: TestEmptyBucket (0.05s)
--- PASS: TestOrderAndValues (0.07s)
--- PASS: TestNoAliasing (3.37s)
    getallleases_test.go:184: panics as expected: failed to Unmarshal lease proto item; lease ID=0000000000000003
--- PASS: TestUndecodable (0.10s)
--- PASS: TestOddKeysDecodable (0.14s)
--- PASS: TestUnknownFields (0.18s)
    getallleases_test.go:233: after Close: recover() = runtime error: invalid memory address or nil pointer dereference
--- PASS: TestAfterClose (0.15s)
ok  	github.com/mit-pdos/etcd-grove/examples/axiomcx/getallleases	4.154s
```
