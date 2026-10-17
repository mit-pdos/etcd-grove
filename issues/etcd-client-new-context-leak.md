---
upstream: none
checked: 2026-10-17
links:
  - etcd-io/etcd#21714 pr open: changes the same function's other error returns (wraps them); does not touch these two
---

# `clientv3.New` leaks its context on two configuration errors

**Status**: a bug (a resource leak), small: on two of `newClient`'s error returns the client's
context, already made with `context.WithCancel(cfg.Context)`, is never canceled.

**Where**: `client/v3/client.go` at the pinned revision (fork `goose-lean` 09669450f; the same
lines on upstream `main` b25719d10): `newClient` makes `ctx, cancel := context.WithCancel(baseCtx)`
(line 381) and stores `cancel` in the client; then

- `lg, err = cfg.LogConfig.Build()` (397) or `logutil.CreateDefaultZapLogger(...)` fails:
  `if err != nil { return nil, err }` (404-406);
- the message-size check fails: `return nil, fmt.Errorf("gRPC message recv limit ...")` (422);

both return without `client.cancel()`, unlike the endpoints check (441), the dial failure (450),
the token failure (`client.Close()`, 471) and the version check (`client.Close()`).

**What happens**: when the caller's `Config.Context` is cancellable, `WithCancel` registers the
child with its nearest `*cancelCtx` ancestor (`propagateCancel`; `Config.Context` itself, or the
one under a `WithValue`), and the child stays registered, with its `Done` channel, until that
ancestor is canceled: each failed `New` call leaks one child. For a custom context type that is
neither a `*cancelCtx` nor an `afterFuncer` but has a non-nil `Done()`, `propagateCancel` starts a
goroutine waiting on the parent instead: each failed `New` leaks a goroutine. With no `Config.Context` (`context.TODO()`)
nothing is registered and nothing leaks; `go vet`'s `lostcancel` does not see it because
`cancel` is stored in a struct field.

Reproduction: `notes/pr-verify/etcd-21714/client_new_cancel_leak_test.go` (package `clientv3`):
100 failed `New` calls with `MaxCallSendMsgSize: 10, MaxCallRecvMsgSize: 5`, or with a
`LogConfig` whose output path cannot be opened, leave 100 children registered with the parent
context (read by reflection). Fails at the PR's base 5ef5d3c26 and head 73e843991:

```
cp notes/pr-verify/etcd-21714/client_new_cancel_leak_test.go <etcd>/client/v3/
cd <etcd>/client/v3 && go test -run CancelsContext -v .
--- FAIL: TestNewSizeErrorCancelsContext: expected: 0, actual: 100
--- FAIL: TestNewLoggerErrorCancelsContext: expected: 0, actual: 100
```

**Expected**: a failed `New` releases what it made (as its other error paths do).

**How the proof handles it**: `newClient.spec` (`Spec/go_etcd_io/etcd/client/v3/newClient.lean`,
on branch `pr-verify/etcd-21714`) does not mention the context's registration with its parent:
Perennial's context model (`isContext`) does not track a parent's children, so the leak is
invisible to the spec, which only says the call returns an error of one of `newClientErr`'s
origins. Found by reading the code while proving those two error paths.

**Possible fixes**: call `client.cancel()` before both returns (or `defer` a cancel that the
success path disarms); or move `context.WithCancel` after the checks that need no context (the
logger and the size check use none).

**Found**: 2026-10-17, verifying etcd-io/etcd#21714 (`newClient`'s error paths).
