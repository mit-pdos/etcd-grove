---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#18424 issue closed: same root cause (a maintainer, ahrtr, named the context-error retry branch unsafe for writes); closed not planned, judged unreachable because the server's ErrCanceled had no gRPC mapping
  - etcd-io/etcd#21122 pr merged: related, not this bug; added the errors.ErrCanceled -> codes.Canceled mapping (2026-02), against #18424's reasoning
blocks-proof: no
---

# clientv3: the retry interceptor resends a Put, Txn or Delete after a Canceled or DeadlineExceeded status while the caller's context is live

When an attempt of a unary call fails with gRPC status `Canceled` or `DeadlineExceeded` and the
caller's context is not done, the client's retry interceptor sends the call again whatever its retry
policy
([L76-L83](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/retry_interceptor.go#L76-L83)),
skipping the write-at-most-once check (`isSafeRetryMutableRPC`): a write the first attempt applied is
applied twice.

**Why not an issue:** not reachable with etcd's server: it returns `Canceled`/`DeadlineExceeded` only
when the request's context, derived from the caller's, is done, and then the caller's context is
done too and the interceptor returns. The status must come from something in between (an L7 proxy or
load balancer with its own timeout); the maintainers closed #18424 as unreachable. The test below
uses a fake KV server that answers `Canceled` after applying. The user's 2026-10 review: skip.

**Test:** `TestPutRetriedAfterCanceledStatus` in
[`nonissues/etcd-client-retry-put-ctx-error/retry_put_ctx_error_test.go`](etcd-client-retry-put-ctx-error/retry_put_ctx_error_test.go),
copied into `client/v3` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef, go1.27.3
linux/amd64:

```
$ go test . -run '^TestPutRetriedAfterCanceledStatus$' -count=1
--- FAIL: TestPutRetriedAfterCanceledStatus (0.03s)
    retry_put_ctx_error_test.go:56: the server received the Put 2 times: the client retried a non-repeatable request
FAIL
```

## Proof

no: the verified fork carries a fix (`8a24be2a3`: a non-repeatable call returns its
attempt's error in that branch), but the proof does not depend on it: the transport contract already
lets a successful reply follow earlier applications of the same request
(`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`), and the interceptor's spec is unchanged
over the fix (`Proof/go_etcd_io/etcd/client/v3/Client__unaryClientInterceptor.lean`).

## Notes

The comment above the branch ("its the callCtx deadline or cancellation, in which case try again")
refers to go-grpc-middleware's per-attempt context, which etcd's copy of the interceptor dropped; with
no per-attempt context the branch only serves statuses from elsewhere. Behind an Envoy-style proxy
whose route timeout is shorter than the caller's deadline the double write is plausible; whether that
counts as a supported deployment is the open question.
