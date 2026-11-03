---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/bbolt#447 issue closed: "Remove panics in the library code", lists the inode-overflow panic, not this trigger
blocks-proof: no
---

# bbolt: a NaN `Bucket.FillPercent` makes `Commit` panic (amd64)

A NaN `FillPercent` passes `splitTwo`'s clamp (`<` and `>` are both false), and on amd64
`int(pageSize * NaN)` is `MinInt64`, read by `splitIndex` as the `uintptr` `2^63`: a leaf is never
split by size, and `Commit` panics (`inode overflow`) once a node holds 65538 entries or more. On
arm64 `int(NaN)` is 0 and the split degenerates to 2-entry pages instead.

**Why not an issue:** a precondition etcd meets: `FillPercent` is a ratio, and etcd sets only `0.9`
(`server/storage/backend/batch_tx.go`, `backend.go`); a NaN fill percent is a caller bug.

## Proof

no: etcd's backend writes only `0.9` (`batchTx__unsafePut.lean`). The axiom
`backend.ownWTxG_fill` (`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean`) gave the
field back with any value, which made the axioms prove that the reproduction returns
(`notes/axiom-review/bbolt.md`): an axiom too strong, not a premise etcd misses.

## Notes

Test: [`bbolt-fillpercent-nan/fillpercent_nan_test.go`](bbolt-fillpercent-nan/fillpercent_nan_test.go)
(package `bbolt_test`, the program `examples/axiomcx/bboltnan`), fails at etcd-io/bbolt@a4ef197
(go1.27.3 linux/amd64, 2026-11-01): `Commit panicked: inode overflow: 69997 (pgid=4)`. A one-line
guard in `splitTwo` (`if !(fillPercent >= minFillPercent)`) would clamp NaN too. Found 2026-10-29
by the axiom review of `ownWTxG_fill`.
