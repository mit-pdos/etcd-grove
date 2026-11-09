---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# clientv3: `Maintenance.Status` panics after `SetEndpoints()` with no endpoint, and races `SetEndpoints`

After `cli.SetEndpoints()` with no argument (accepted without error), any call that dials one
member through the client (`Maintenance.Status`, `HashKV`, `Defragment`, `Snapshot`) panics with
"index out of range [0] with length 0" instead of returning an error. The same dial reads the
client's endpoint list without the lock `SetEndpoints` writes it under, so with auto-sync enabled
(`AutoSyncInterval > 0`, whose `Sync` calls `SetEndpoints`) a concurrent `Status` is a data race.

**Expected:** `Status` should return an error (e.g. `ErrNoAvailableEndpoints`) when the client has
no endpoint, and read the endpoint list under `epMu` as `Endpoints()` does.

**Impact:** a client whose endpoints are emptied (a user's `SetEndpoints()`, or an auto-sync that
finds no published voter: `Sync` sets the list it built, possibly empty, when `ETCD_VERIFY` is off)
crashes on its next maintenance call; with auto-sync, `Status`/`Defragment` race the sync (seen
under `-race`). Kubernetes' prober and feature checker call `Status` (they do not auto-sync).

**Reproduction:** `TestStatusAfterEmptySetEndpointsPanics` in
[`issues/etcd-client-dial-empty-endpoints/dial_empty_endpoints_test.go`](etcd-client-dial-empty-endpoints/dial_empty_endpoints_test.go),
run as an external test of `go.etcd.io/etcd/client/v3` at upamanyus/etcd@a4d2bb1720b9 (the pinned
fork of etcd-io/etcd main, 2026-11-07), go1.27.3 linux/amd64 (from `examples/`, renamed into a test
package there):

```
--- FAIL: TestStatusAfterEmptySetEndpointsPanics (0.00s)
    zz_dial_test.go:24: Status panicked after SetEndpoints(): runtime error: index out of range [0] with length 0
```

**Cause:** `Client.dial` builds the target from `authority(c.endpoints[0])` (`client/v3/client.go`,
`dial`), reading `c.endpoints` without `c.epMu` and without checking it is non-empty;
`SetEndpoints` stores any list under `epMu`; `Client.Dial` (the maintenance client's dial closure,
`maintenance.go`'s `NewMaintenance`) reaches `dial` at any time after `New`.

## Proof

no: the client's specs (batch 1c, `Spec/go_etcd_io/etcd/client/v3/`) take the endpoints token
`epsTok` at a non-empty list for `Client.Dial`, `Client.dial` and `maintenance.Status` (a fraction:
no concurrent `SetEndpoints`; `New` gives the token only with auto-sync off), a precondition every
user in scope meets (Kubernetes and the examples never change endpoints).
