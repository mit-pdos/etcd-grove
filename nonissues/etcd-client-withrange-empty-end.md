---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# clientv3: `WithRange("")` reads one key from a remote member and every key from the key on in-process

A `Get`, `Delete` or transaction operation built with `clientv3.WithRange("")` (or
`Op.WithRangeBytes([]byte{})`, or a comparison's `Cmp.WithRange("")`) carries a non-`nil` empty
range end. Sent to a member over gRPC it reads (or deletes, or compares) the key alone: proto3 does
not encode an empty `bytes` field, so the member decodes the end as `nil`. Sent through an
in-process client (`v3client`, the gRPC proxy's adapters), which hands the request message to the
server's handlers without marshalling it, the same call covers every key from the key on: mvcc reads
a non-`nil` empty end that way (`server/storage/mvcc/index.go`, `unsafeVisit`). No caller in etcd
passes one: the leasing KV's `WithRange(end)` calls are reached only with a non-empty `end`
(`client/v3/leasing/kv.go:394`, `txn.go:122`), the gRPC proxy guards `len(r.RangeEnd) != 0`
(`server/proxy/grpcproxy/kv.go:178`).

**Why not an issue:** no test, found by code reading (verify round, 2026-11-09). `WithRange`'s
documentation requires an end key greater than the start key ("endKey must be lexicographically
greater than start key"), which `""` is not; the caller is outside the documented use. The
in-process side is the same root cause as `etcd-auth-empty-range-end-point-check.md`.

## Proof

no: the client's KV specs take the scope premise that no range end of the request is a non-`nil`
empty slice (`OpM.emptyEnd = false` in `KV.GetTriple`, `DeleteTriple`, `DoTriple`,
`GetStreamTriple`, `Txn.ThenTriple`, `Txn.ElseTriple`; `e ≠ []` in `Cmp.WithRange.spec`:
`SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean`), since one model of the request cannot be right for
both transports; every caller in scope meets it.

## Notes

A fix in the client: `WithRange` (and `Cmp.WithRange`) could store `nil` for an empty end, which is
what every remote member already reads.
