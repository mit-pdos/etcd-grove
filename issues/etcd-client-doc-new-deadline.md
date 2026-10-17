---
upstream: unchecked
---

# `clientv3` package doc: `New` on an unreachable endpoint does not return `context.DeadlineExceeded`

**Status**: documentation the code contradicts.

**Where**: `client/v3/doc.go` at the pinned revision (fork `goose-lean` 09669450f), lines 19-29:

```go
// expect dial time-out on ipv4 blackhole
_, err := clientv3.New(clientv3.Config{
	Endpoints:   []string{"http://254.0.0.1:12345"},
	DialTimeout: 2 * time.Second,
})

// etcd clientv3 >= v3.2.10, grpc/grpc-go >= v1.7.3
if err == context.DeadlineExceeded {
```

**What happens**: since client creation became non-blocking (etcd-io/etcd#21832, `grpc.NewClient`),
`New` does not connect: for an unreachable endpoint and no user name/password it returns a client
and no error; the first request fails instead. With a user name and password the token request
times out, and `New` returns `context.DeadlineExceeded` itself at the pinned revision, but, with
etcd-io/etcd#21714, an error wrapping it (`err == context.DeadlineExceeded` false,
`errors.Is` true). Probes: `notes/pr-verify/etcd-21714/client_error_wrap_test.go`
(`TestPR21714UnreachableNoAuth`, `TestPR21714UnreachableWithAuth`), logs `probe-base.log`,
`probe-head.log` of that directory.

**Expected**: the example shows what `New` does now (no error; or, with credentials, an error to
test with `errors.Is(err, context.DeadlineExceeded)`).

**How the proof handles it**: `newClient.spec` (branch `pr-verify/etcd-21714`) does not depend on
the connection succeeding: a dial error is whatever grpc's `NewClient` returns (an axiom), the
token error `getToken`'s.

**Possible fixes**: update the example (drop the blackhole time-out, or add credentials and use
`errors.Is`).

**Found**: 2026-10-17, verifying etcd-io/etcd#21714 (its reviewer pointed at the example).
