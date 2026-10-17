---
upstream: none
checked: 2026-10-17
links: []
---

# grpc-proxy KV: the backend's error code is lost (sent as `Unknown`)

**Status**: a bug (a wrong result): the gRPC proxy's KV service returns to its clients the error
`clientv3`'s `kv.Do` returned, an `rpctypes.EtcdError`, which has no `GRPCStatus` method, so grpc
sends it with code `Unknown` instead of the code the server sent. Outside the verified code (the
proxy is not translated); found while reviewing etcd#21330 (`notes/pr-verify/etcd-21330.md`).

**Where**: `server/proxy/grpcproxy/kv.go` (pinned etcd `09669450f`, unchanged on upstream main
`f061acd09`): `kvProxy.Range` (`return nil, err` after `p.kv.Do`, line 64), `Put` (line 87),
`DeleteRange` (line 95), `Txn` (line 118). `kv.Do` returns `ContextError(ctx, err)`, which turns a
gRPC status error into `rpctypes.Error(err)`, an `EtcdError{code, desc}`
(`api/v3rpc/rpctypes/error.go`: `EtcdError` has `Code()` and `Error()` only).

**What happens**: through the proxy, `etcdserver: no leader` (server: `Unavailable`) and
`etcdserver: key is not provided` (`InvalidArgument`) reach the client with code `Unknown`. The
client's `rpctypes.Error` still recovers the `EtcdError` from the message, so `errors.Is` against
`rpctypes.Err*` works, but anything that decides on the code does not: clientv3's retry interceptor
(`client/v3/retry_interceptor.go`, `isSafeRetry`: retries only `Unavailable`) does not retry a
no-leader error through the proxy, and non-Go clients see `Unknown`. Reproduction:
`notes/pr-verify/etcd-21330/kv_proxy_errcode_test.go` (package `grpcproxy`; a `kvProxy` over a fake
`clientv3.KV` whose `Do` returns `rpctypes.ErrNoLeader`/`ErrEmptyKey`, served over `bufconn`):

```
$ cp kv_proxy_errcode_test.go <etcd>/server/proxy/grpcproxy/ && go test -run TestProxyKVErrorCode .
proxy Range with backend error etcdserver: no leader: code Unknown, want Unavailable (as from the server directly)
proxy Range with backend error etcdserver: key is not provided: code Unknown, want InvalidArgument (as from the server directly)
```

(at etcd-io/etcd#21330's head `f864d993ab`; the proxy code is the same at the pin).

**Expected**: the proxy forwards the server's error with its code, as a direct connection would.

**How the proof handles it**: not reached: the proxy is not translated.

**Possible fixes**: convert back to a status error in the proxy (e.g. a helper that maps an
`rpctypes.EtcdError` to `status.Error(e.Code(), e.Error())`, applied to every `kvProxy` method's
error; or give `EtcdError` a `GRPCStatus()` method, which makes every server that returns one keep
its code; the latter changes `status.FromError` for all client callers too, to be checked).

**Found**: 2026-10-17, by the reviewer of the etcd#21330 verification (`pr-verify/etcd-21330`),
confirmed end to end with the test above.
