# Axiom review: `KV_Get_dist`'s error arm claims `statusErrOk`

Reviewed in worktree `eg-es-kvge` at `433424fb35` plus its uncommitted diff (the change under review), read-only.
Evidence: a Go program only (no counterexample, so no Goose project and no Lean proof), in
`kvge-scratch/review/` (`main.go`, outputs `run1.txt`, `run2.txt`), at the pins of `examples/go.mod`: clientv3/api
`github.com/upamanyus/etcd/{client,api}/v3 v3.0.0-20261124070122-df6af0c36a6b`, grpc-go v1.84.0, Go 1.27.3.

## The axiom and the change

`etcd_dist.KV_Get_dist.wp_proof : KV_Get_dist.spec` (`{Spec,Proof}/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVGetDist.lean`).
The error arm was `⌜err ≠ nil ∧ resp = null⌝`; it is now `⌜err ≠ nil ∧ resp = null⌝ ∗ statusErrOk err`. The rest
of the statement is unchanged and was reviewed in `n2-kv-dist.md` (sound). The in-process `kv.Get.spec` proves
`kvErr err = ⌜clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err`, so the new claim is one part of a claim already
proved in one process. What has to be checked is that real grpc-go across a network meets it: the in-process proof
gets it from the grpc model's premises.

In Go, `statusErrOk err` for a non-nil `err` says:
* it is a leaf: no `Unwrap() error`, `Unwrap() []error` or `As(any) bool`;
* every `Error()` call returns the same string;
* it has no `Format` method, and `Error` has the signature `Error() string`;
* a `GRPCStatus()` method means it is a `*status.Error` with a status nobody writes;
* an `Is` method returns true only for a target with the same description;
* `stTypedErr`: its value is of its dynamic type.

## Verdicts

| Point | Verdict |
|---|---|
| (a) every error is built at the caller from the received code and message (or a local failure) | **holds, docstring caveat** (F1: the status details proto also comes from the wire) |
| (b) every error `Get` can return meets `statusErrOk` in Go | **holds**: 44 cases, 0 violations |
| (c) no path returns a non-leaf error | **holds** in this configuration. Every wrapping site found is unreachable from `Get` |

**Overall: sound.** Two docstring corrections, F1 and F2. No attack produced a counterexample.

## (a) What the caller builds, and from what

The chain at the pin:
* `kv.Get` returns `ContextError(ctx, ·)` of `kv.Do`'s error (`client/v3/kv.go:164-166`).
* `kv.Do` *also* returns `ContextError(ctx, err)` (`kv.go:249`, F2). Its `err` is one of two things:
  - `rpctypes.ErrInvalidSortOption` (`kv.go:224`);
  - the error of `retryKVClient.Range` → `pb.KVClient.Range` → `cc.Invoke` through `unaryClientInterceptor`
    (`client.go:262-271`, `retry_interceptor.go:41-107`).
* `ContextError` (`client.go:610-630`) works in three steps:
  - `rpctypes.Error` (`api/v3/v3rpc/rpctypes/error.go:256-272`) builds an `EtcdError{code, desc}` (a value)
    when the status message is one of etcd's strings;
  - otherwise it keeps the error;
  - for code `DeadlineExceeded`/`Canceled`, it then substitutes `ctx.Err()` when that is non-nil.

The wire reaches the error only through the HTTP/2 response:
* the `:status` and `content-type` headers;
* the `grpc-status`, `grpc-message` and `grpc-status-details-bin` trailers;
* RST_STREAM/GOAWAY codes;
* the message bytes. A message that does not parse gives a `codes.Internal` status, with the text of the decode error.

`http2_client.go:1685` builds the status with `istatus.NewWithProto(grpcStatusCode, grpcMessage, details)`
(`internal/status/status.go:49-73`). There is no other source.

No Go error value crosses the network. The handler's error is flattened into code and message on the server.
`fake/wrapped` checks this: a handler that returns `fmt.Errorf("wrapped: %w", status.Error(Aborted, …))` reaches the
client as a leaf `*status.Error` whose text contains the server's text. The wire influences only these things:
* the code, which decides whether `ContextError` substitutes `ctx.Err()` (the caller's context: the premise
  `ctxErrClient`);
* the message, which decides whether `rpctypes.Error` makes an `EtcdError` (`fake/etcdmsg`, `h2/detailsmatch`);
* the details.

**F1 (docstring).** "`*status.Error`, built at the caller from a status code and message only" is not exact.
When the trailers' `grpc-status-details-bin` parses as a `google.rpc.Status` whose code equals `grpc-status`, that
whole proto becomes the status (`status.go:59-62`): its message *replaces* `grpc-message`, and its `details` (`Any`
values chosen by the peer) are kept. If the codes differ, the status is `Internal` "grpc-status-details-bin
mismatch: …".
* `h2/detailsmatch`: the client got `EtcdError` "etcdserver: request timed out", taken from the details proto, while
  the header said "header says otherwise".
* `fake/details`: the client got `*status.Error` with `details=1`.

`statusErrOk` is unaffected:
* `Error()` reads only code and message;
* `GRPCStatus()` returns the fixed `*Status`;
* `Is` is `proto.Equal` of the whole proto (`status.go:222-228`), so `true` implies equal messages, as
  `grpcErrMethodsOk` asks;
* nothing on `Get`'s path calls `Details()`.

Suggested text: "built at the caller from a status code, message and details (the reply's trailers, whose
`grpc-status-details-bin` proto, if its code agrees, supplies the message and details; or the transport's or the
context's failure, …)". Likewise, "the remote member's handler only chooses the code and message bytes" should say
"the code, message and status details".

**F2 (docstring, minor).** "`kv.Get` returns `ContextError(ctx, err)` of `kv.Do`'s error … `kv.Do`'s error is
`rpctypes.ErrInvalidSortOption` … or the stub's `Invoke` error" leaves out that `kv.Do` already applies
`ContextError` (`kv.go:249`), so `Get` applies it twice. The set of results is the same. A second application maps
each output of the first into the set:
* an `EtcdError` returns at the `AsType` check;
* a context error carries no etcd message and no status;
* a status of code `DeadlineExceeded`/`Canceled` may now meet a non-nil `ctx.Err()` and become it.

Suggested: "`kv.Do` returns `ContextError(ctx, e)`, and `kv.Get` `ContextError` of that, where `e` is …".

## (b) Every path, checked in Go

`main.go` uses the deployment's `clientv3.Config` (`etcdstart.NewClients`: `DialTimeout` 2s, keepalive 2s/6s,
`grpc.WithNoProxy()`, the default retries and `WaitForReady(true)`; and `newUserClient`'s Username/Password). For
each error it prints:
* the `%T`;
* `Unwrap() error`, `Unwrap() []error`, `As(any) bool` and `fmt.Formatter`;
* whether two `Error()` calls agree;
* membership in `clientErrTys`;
* the `Is`/`GRPCStatus`/`Error` signatures.

Its peers are a fake etcd KV/Auth server, a raw-codec gRPC server, an h2c server that crafts the trailers, raw TCP
peers, a closed port and an unresolvable host. Result: `violations of statusErrOk's Go meaning: 0` (`run2.txt`).
Every error has one of four types, each of them a leaf, with no `Format` and a stable `Error() string`:
`*status.Error`, `rpctypes.EtcdError`, `*errors.errorString` (`context.Canceled`) or
`context.deadlineExceededError`. No response was non-nil alongside an error.

| Path | Cases (program name) | Returned |
|---|---|---|
| Server status, any code/message | `fake/details`, `deadline(alive ctx)`, `canceled(alive ctx)`, `plainerr`, `wrapped`, `h2/badcode` (code 99, odd percent-encoding), `h2/nonnum`, `h2/dlx` | `*status.Error` |
| etcd message under any code | `fake/etcdmsg`, `learner`, `token(no auth)`, `h2/detailsmatch` | `EtcdError` |
| `ErrInvalidSortOption` | `invalidSort` (`SortOrder(7)`) | `EtcdError` (package variable) |
| Retry interceptor, `Unavailable` until the deadline (`waitRetryBackoff`'s `contextErrToGRPCErr`, then `ContextError`) | `fake/unavail`, `unavail/deadline0-4`, `ctx/unavailRetries` | `context.DeadlineExceeded` |
| Token refresh: the second `Authenticate` fails (etcd error / status with details / `Internal` / hangs) | `auth/refresh-*` | `EtcdError` / `*status.Error` / `*status.Error` / `DeadlineExceeded` |
| Closed client (`ErrClientConnClosing`) | `closedClient` | `*status.Error` Canceled |
| Protocol violations (no message, two messages, garbage bytes, truncated frame, RST_STREAM, HTTP 404 HTML, HTTP 500, details mismatch) | `rawgrpc/*`, `h2/*` | `*status.Error` (Internal/Unimplemented/Unknown) |
| Non-etcd gRPC server | `emptyGrpcServer` | `*status.Error` Unimplemented |
| Connection failures: refused, peer closes, peer sends HTTP/1 garbage, peer silent, DNS failure, server stops mid-call or is stopped | `closedPort`, `tcp/*`, `badHost`, `serverStop*` | `context.DeadlineExceeded` (`WaitForReady` waits until the deadline; the pick's `DeadlineExceeded` status is replaced by `ctx.Err()`) |
| Caller's contexts: `WithTimeout`, `WithCancel`, `WithCancelCause(custom)`, `WithTimeoutCause(custom)`, already canceled | `ctx/*` | `DeadlineExceeded` / `Canceled`; `Err()` ignores the cause (`context.Cause` is `main.myCause`) |

Notes:
* **Context errors.** grpc-go v1.84 never reads `context.Cause` (no use in the module). Its internal contexts
  inherit the parent's `Err()`, and it converts them to statuses (`toRPCErr`, `rpc_util.go:1133-1157`;
  `transport.ContextErr`, `transport.go:870-878`). A custom context whose `Err()` returns another error would flow
  through `ContextError` as-is: such a context is excluded by the premise `ctxErrClient` (InvKVConn.lean:2082), which
  demands `clientErr`, `statusErrOk` and `ctxErrShape`/`ctxErrMsg` of every `Err()` result. `withVersion`
  (`ctx.go:41`) is a value context and delegates `Err()`.
* **`ContextError`'s non-status passthrough.** It returns the error as-is when the error is neither a status nor an
  etcd message. It is reached only by `ctx.Err()` values: the outer call of the double `ContextError`, or `gtErr`
  when `Authenticate` returned `ctx.Err()`. Those are premise-covered. The unary `Invoke` returns no `io.EOF`:
  `toRPCErr` keeps `io.EOF`, but the unary paths turn end-of-stream without a message into the cardinality status
  (`stream.go:1290-1298`, `call.go:83-95`; `rawgrpc/nomsg`).
* **Not exercised (code read only).**
  - A message over the receive limit: `MaxCallRecvMsgSize` is `MaxInt32`; the result is a `status.Errorf`
    `ResourceExhausted`.
  - Response compressors: `status.Errorf` (`stream.go:1280`).
  - TLS: the deployment is plaintext. A handshake error would sit inside a `ConnectionError` that never reaches the
    caller (see (c)).

## (c) Non-leaf errors

Under today's `statusErrOk` (`errors.isLeafError`), any non-leaf that `Get` returned would make the new claim false.
It would make the proved `kvErr`'s `clientErr` false too. I found every non-leaf or wrapping site on the client path
and none reaches `Get` in this configuration:

| Site | Why it does not reach `Get` |
|---|---|
| `transport.ConnectionError` (has `Unwrap`, `transport.go:793-822`) | `toRPCErr` turns it into `status.Error(Unavailable, Desc)` (`rpc_util.go:1146`). A picker error that is one becomes `status.Error(Unavailable, …)` (`picker_wrapper.go:176`); with `WaitForReady` it only sets `lastPickErr`'s text |
| `toRPCErr`'s and the picker's passthrough of anything `status.FromError` accepts. `FromError` uses `errors.As`, so a `fmt.Errorf("%w", st)` would pass through as a non-leaf (`rpc_util.go:1152`, `picker_wrapper.go:162-168`; `dropError` is unwrapped at `stream.go:618`) | Its producers in this configuration create no such error. etcd's `perRPCCredential.GetRequestMetadata` returns no error (`credentials.go:69-77`). The default config selector returns none. round_robin → endpointsharding → pickfirst pickers return `ErrNoSubConnAvailable`, a `ConnectionError`, or `fmt.Errorf("…%v")` / `errors.New` texts (`pickfirst.go:206,713,742,777`; `endpointsharding.go:292`) |
| `"max retries exhausted: …: %w"` (`stream.go:867`) | Needs a service-config retry policy. etcd's resolver sets only `{"loadBalancingPolicy":"round_robin"}` (`internal/resolver/resolver.go:44`), and no resolver takes a config from the peer |
| `"failed to exit idle mode: %w"`, `"failed to start resolver: %w"` (`clientconn.go:303,416`) | Returned by `grpc.NewClient`, not by a call. `idlenessMgr.OnCallBegin` returns nothing in v1.84 (`internal/idle/idle.go:193`) |
| Server-side wrapping (`fake/wrapped`) | Flattened to code and message on the wire |

This matches the configuration caveat already recorded in `clientErrTys`' docstring (`ClientErr.lean`):
* per-RPC credentials that return a wrapped status;
* a retry policy's error.

The dist deployment has neither. It sets no credentials but etcd's token bundle, and no retry policy.

## Not in scope

The fake servers answer `Get` successfully (`fake/ok`), as any program serving etcd's KV service at the address
could. Who may listen at a member's address is `kvClientAt`'s address facts (`n2-kv-dist.md`, F5), unchanged here.
As instructed, I updated neither `notes/audit.md` nor the README index of this directory.

## Re-review (docstring after F1, F2)

This re-review checks `git diff HEAD` of the axiom file `Proof/.../dist/KVGetDist.lean`. Only the docstring bullet
"*Why a remote call's error is `statusErrOk`.*" changed. The statement did not change.

**Verdict: accurate. It fixes F1 and F2 and adds no false claim.**

* **F1, fixed.** The new text, "built … from a status code, message and details", agrees with
  `internal/status/status.go:49-73`. So does "whose `grpc-status-details-bin` proto, if its code agrees, supplies
  the message and details" (on a code mismatch, the result is an `Internal` status whose message embeds the peer's
  text, which is still a code and a message). "`Error()` reads only the code and message" is true
  (`status.go:211-213`, `Status.String`). "The handler only chooses the code, message and status details" is also
  true.
* **F2, fixed, with one nit.** "`kv.Do`'s error (itself already a `ContextError` of the stub's: the same set of
  results)" leaves out the sort-option case. `kv.Do` also passes `ErrInvalidSortOption` through `ContextError`
  (`kv.go:224,249`), which returns it unchanged. So the result set is right, but the words could be "a
  `ContextError` of the stub's error or of `ErrInvalidSortOption`". The nit is optional and does not block.
