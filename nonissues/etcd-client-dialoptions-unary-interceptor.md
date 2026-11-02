---
upstream: none
checked: 2026-10-16
links: []
blocks-proof: no
---

# clientv3: a grpc.WithUnaryInterceptor in Config.DialOptions silently replaces the client's retry interceptor

`Config.DialOptions` is documented as "a list of dial options for the grpc client (e.g., for
interceptors)"
([config.go](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/config.go#L82)),
but a `grpc.WithUnaryInterceptor` there replaces the client's own (gRPC keeps the last one given):
unary calls lose their retries, the auth token refresh and the API-version metadata, with no error.
`grpc.WithChainUnaryInterceptor` keeps it. The same holds for `grpc.WithStreamInterceptor` and the
client's stream interceptor (by reading).

**Why not an issue:** documentation: the behavior is gRPC's documented `WithUnaryInterceptor`
semantics, and the client works as configured; the user's 2026-10-23 review parked it (skip for now).
A one-line switch to `WithChainUnaryInterceptor` in `dialSetupOpts`, or a sentence on `DialOptions`,
would likely be accepted.

**Test:** `TestDialOptionsUnaryInterceptorReplacesRetry` in
[`nonissues/etcd-client-dialoptions-unary-interceptor/dialoptions_interceptor_test.go`](etcd-client-dialoptions-unary-interceptor/dialoptions_interceptor_test.go),
copied into `client/v3` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef, go1.27.3
linux/amd64 (a gRPC KV server answering the first `Range` with `Unavailable`):

```
$ go test . -run '^TestDialOptionsUnaryInterceptorReplacesRetry$' -count=1
--- FAIL: TestDialOptionsUnaryInterceptorReplacesRetry (0.08s)
    dialoptions_interceptor_test.go:70: with a WithUnaryInterceptor dial option: 1 ranges, err rpc error: code = Unavailable desc = transient; want 2, nil
FAIL
```

## Proof

no: `clientv3.New` is proved under the configuration premise that `Config.DialOptions` is empty
(`Proof/go_etcd_io/etcd/client/v3/InvClientNew.lean`), a scope restriction: another chain would be
another premise, and a client without the retry interceptor retries less, which breaks no safety
statement.
