---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# v3client: Defragment through the in-process client panics

The in-process client `v3client.New(s)` panics with a nil-pointer error on `Defragment`, when auth
is off or the caller is root. etcd's own users of `v3client` (embed's v3election and v3lock
services) never call `Defragment`.

**Expected:** `Defragment` through the in-process client should defragment, as it does through
gRPC.

**Impact:** only a program that embeds etcd and calls `Maintenance.Defragment` on the client
`v3client.New` returns. etcd itself does not.

**Cause:** `v3client.New` builds the maintenance service with a nil health notifier,
`v3rpc.NewMaintenanceServer(s, nil)` (`server/etcdserver/api/v3client/v3client.go:42`).
`maintenanceServer.Defragment` then calls `ms.healthNotifier.defragStarted()`
(`server/etcdserver/api/v3rpc/maintenance.go:121`) on that nil interface. `authMaintenanceServer`'s
admin check runs first, so a non-root caller with auth on gets `ErrPermissionDenied` instead.

**Why not an issue:** found by reading. There is no Go test, and etcd does not reach it.

## Proof

no: `NewMaintenanceServer.spec` takes `notifierAt hn` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`),
which no law gives for `nil`. So the in-process client's maintenance service is outside the
handlers' specs. It is out of scope, and no premise is needed elsewhere.

## Notes

Found by the 2a completeness review, round 1 (`notes/specs-only/reviews/2a-completeness-1.md`,
second tier item 3). The fix is a no-op notifier in `v3client.New`, or a nil check in
`Defragment`.
