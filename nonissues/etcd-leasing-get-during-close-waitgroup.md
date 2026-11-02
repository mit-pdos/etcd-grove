---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# clientv3/leasing: a `Get` concurrent with the leasing KV's close function can panic in `sync.WaitGroup`

The close function `NewKV` returns
([`leasingKV.Close`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go#L80-L83))
cancels the KV's context and waits on its wait group, whose counter can reach zero as the session
monitor, `clearOldRevokes` and the lease monitors return. A
[`get`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/client/v3/leasing/kv.go#L301-L338)
that acquired a lease then runs `lkv.wg.Add(1)` (L331): as for the cache, "Add called concurrently
with Wait" or "WaitGroup is reused before previous Wait has returned", or, after `Wait` returned, a
lease monitor that outlives the close. Neither documents that they must not overlap.

**Why not an issue:** no test; found by code reading (bounds plan B3's wait-group inventory,
`notes/bounds-waitgroups.md`), and an undocumented precondition etcd meets: its one caller, the gRPC
proxy with `--experimental-leasing-prefix`
([`grpc_proxy.go#L488`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdmain/grpc_proxy.go#L488)),
never calls the close function.

## Proof

no: the proof takes the precondition as the "open" token `leasingOpen`
(`Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean`): `Get` holds a fraction, the close
function needs the whole.

## Notes

The same shape as `nonissues/etcd-cache-watch-during-close-waitgroup.md`; the same fix (a closed
flag guarding `Add(1)`, or documentation). No upstream report drafted (leasing findings are on hold
for reports).
