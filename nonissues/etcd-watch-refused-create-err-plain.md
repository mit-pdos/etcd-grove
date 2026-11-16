---
upstream: none
checked: 2026-11-16
links:
  - etcd-io/etcd#10131 issue closed: related, different (2019): watchers after permission-denied refusals
  - etcd-io/etcd#14296 pr merged: related: the member answers a refused create with WatchId -1, the response this follows
blocks-proof: no
---

# clientv3: a refused watch's `Err()` is a plain error, not `rpctypes.ErrPermissionDenied`

When the member refuses a watch's create (auth enabled and the user may not read the key, or an
empty watch range), the canceled response's `Err()` is an `errors.New` of the member's cancel
reason, not one of `rpctypes`' errors: for a permission denial its text is
`rpc error: code = PermissionDenied desc = etcdserver: permission denied`, and
`errors.Is(err, rpctypes.ErrPermissionDenied)` and `errors.As(err, &rpctypes.EtcdError{})` are false.
The member puts `rpctypes.ErrGRPCPermissionDenied.Error()` (the gRPC status's full text) in
`CancelReason` (`server/etcdserver/api/v3rpc/watch.go`, `isWatchPermitted`'s refusal); the client's
`addSubstream` wraps it as `v3rpc.Error(errors.New(resp.CancelReason))`, and `rpctypes.Error` maps
only a status's description (`etcdserver: permission denied`), not the full text, so the plain error
stays.

**Why not an issue:** documentation-level: `WatchResponse.Err` documents no error type, and the
message is right; a caller telling a denied watch apart by type gets a wrong answer, but no etcd
caller does. Found while proving k8s's `watchChan.startWatching` (7f-5, 2026-11-16): the client
watch's close error cannot be promised to be one of the client's fixed messages (`errCellOk`), only
a client error that is a pointer (`errPtrOk`).

**Test:** `TestRefusedCreateErrPlain` in
[`etcd-watch-refused-create-err-plain/refused_create_err_test.go`](etcd-watch-refused-create-err-plain/refused_create_err_test.go),
copied into `client/v3` at the verified fork (`upamanyus/etcd` `goose-lean`, 249d76bea), go1.27.3:
a fake `pb.WatchClient` answers the create as the member does (`WatchId: -1, Created, Canceled,
CancelReason`); it passes and logs

```
reason "rpc error: code = PermissionDenied desc = etcdserver: permission denied": closeErr *errors.errorString "rpc error: code = PermissionDenied desc = etcdserver: permission denied"; Err() *errors.errorString "rpc error: code = PermissionDenied desc = etcdserver: permission denied"; EtcdError? false
reason "mvcc: watcher range is empty": closeErr *errors.errorString "mvcc: watcher range is empty"; Err() *errors.errorString "mvcc: watcher range is empty"; EtcdError? false
```

## Proof

no: the client watch's element gives a close error that is a client error and, if an
`*errors.errorString`, a pointer (`closeErrOk`, `Proof/go_etcd_io/etcd/client/v3/ClientErr.lean`),
which holds of these; k8s's watcher needs no more (`kErrOk_clientP`).

## Notes

Upstream not searched yet (no GitHub access from this session); `checked` records the date of the
finding.
