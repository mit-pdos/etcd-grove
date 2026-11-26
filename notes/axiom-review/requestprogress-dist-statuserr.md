# Review: `RequestProgress_dist`'s post `statusErrOk err` across a real network

Reviewed at `origin/etcd-safe-full-r3/2026-11-26` = `78f45712b1`, in a read-only worktree that has since been removed.
The statement is in `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/WatchDist.lean:84-97` and the axiom in
`Proof/.../etcd/dist/WatchDist.lean:153`. Pins:
* clientv3/api/server `github.com/upamanyus/etcd/* v3.0.0-20261124070122-df6af0c36a6b`;
* grpc-go v1.84.0;
* Go 1.27.3.

The method is the `axiom` skill's. No counterexample was found, so there is no Goose project and no Lean proof. The
evidence is a Go program, in `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/rv-rp/`: `main.go`, `members.go`, and the
outputs `run1.txt` and `run2.txt`.

## Verdict: **SOUND**

`statusErrOk err` holds of every error `(*watcher).RequestProgress` can return against remote members. The in-process
proof gets the property from client-side facts: grpc-go's client code and etcd's client code. None of those facts
depends on who the peer is, so copying the post verbatim is justified. The real-cluster run tried 13 kinds of failure
(about 1.7M calls in run 2) and found 0 violations.

One docstring note, optional and non-blocking (D1 below).

## What `RequestProgress` can return (`client/v3/watch.go:413-444`)

| Return | Source | Type |
|---|---|---|
| `nil` | the `*progressRequest` was handed to `run` on the local channel `reqc`. The real `wc.Send` happens later in `run` (`:588-591`), and its error is only logged | — |
| `errors.New("no stream found for context")` | the watcher is closed (`w.streams == nil`) | `*errors.errorString`, leaf |
| `ctx.Err()` | the caller's context. Covered by the premise `context.isContext ctx cs`, as in process. grpc and clientv3 never read `context.Cause` | `context.Canceled` / `deadlineExceededError` |
| `wgs.closeErr` | read only after `donec` is closed. `donec` is closed in `closeStream`, called from `run`'s defer *after* `w.closeErr = closeErr` (`:525-545`) | see below |

`run`'s `closeErr` (the local variable) has exactly three sources:
1. **The raw `wc.Recv()` error** (`:677-680`), when `isHaltErr` holds or the error is `ErrNoLeader`. It is grpc-go's
   `clientStream.RecvMsg` error: a `*status.Error` (via `toRPCErr` or the trailers) or `io.EOF`.
2. **`v3rpc.Error` of `openWatchClient`'s error** (`:549`, `:683`, `:942-985`, `:1058-1076`), which is one of:
   * `NewStream`'s status;
   * `getToken`'s `Authenticate` error, through etcd's stream interceptor (`retry_interceptor.go:117-133`, `withMax(0)`:
     no retrying stream);
   * `w.ctx.Err()`. `w.ctx` is a `WithCancel` of a `valCtx`, so this is `Canceled`.

   `v3rpc.Error` (`rpctypes/error.go:256-272`) returns the error itself or a fresh `EtcdError` value.
3. **`nil`**, which makes `RequestProgress` retry.

`addSubstream` also writes `w.closeErr = v3rpc.Error(errors.New(resp.CancelReason))` (`:469`). That write is
overwritten by the defer before `donec` closes, so `RequestProgress` never returns it. The `Watch` channel does
expose it (`WatchResponse.Err`), and it is a leaf too. The run shows it: `*errors.errorString "rpc error: code =
PermissionDenied …"`.

Every error a remote peer can cause is therefore built in the caller's process by grpc-go or clientv3. The peer
chooses only the bytes: code, message and status details (KV_Get review F1). The Go types that can come back are
`*status.Error`, `rpctypes.EtcdError`, `*errors.errorString` (`io.EOF`, `context.Canceled`, the "no stream" value) and
`deadlineExceededError`. All of them are leaves with no `Format` method and a stable `Error() string`. Only
`*status.Error` has `GRPCStatus`/`Is`, and its `Is` is `proto.Equal`.

## Q1: the cases

| Case asked | Code path | Real-cluster result |
|---|---|---|
| context cancel / deadline (also `WithCancelCause`, `WithTimeoutCause`, already done) | `ctx.Err()` | `context canceled` (`*errors.errorString`), `deadlineExceededError`. The cause is ignored |
| stream closed / broken / reconnecting | `Unavailable`/`Internal` Recv errors are not halts: `run` reopens and the call is unaffected. A halt closes with the raw Recv status | bridge `DropConnections` every 150 ms under bursts: 240 calls, all `nil`. Blackholed: `nil` (the stream opens without the peer) |
| member down / restarting | `WaitForReady(true)` (`options.go:29`): `NewStream` waits, so the call waits for `ctx`. If the watcher is closed meanwhile, `closeErr` = `v3rpc.Error(NewStream's status)` | connection refused: `DeadlineExceeded`/`Canceled`. Watcher closed mid-call: `*status.Error` `Canceled` "latest balancer error: connection error: desc = … connection refused" (the transport's `ConnectionError` text, as a status). Restart via a new listener: `nil` again. Raft stopped with gRPC still up: `nil` |
| the request's send failing | `wc.Send` is in `run`. Its error is dropped (`:589-591`) and never reaches the caller | not observable (`nil`) |
| auth failure (auth on) | `getToken` at stream open → `Authenticate`'s `EtcdError` → `isHaltErr` (code `Unknown`) → `closeErr` → returned | password changed / user deleted: `rpctypes.EtcdError` "authentication failed, invalid user ID or password" (50 calls). Forbidden watch on the stream: `nil`. Auth disabled under credentials: `nil` (`ErrAuthNotEnabled` is swallowed) |
| `ErrNoLeader` / `WithRequireLeader` | raw Recv `*status.Error`, kept un-mapped (`:678`) | member 0 cut from both peers: `*status.Error` Unavailable "etcdserver: no leader" (13442 calls in run 2) |
| clientv3 wrapping (`toErr`, `ContextError`) | `RequestProgress` applies neither to its result. `v3rpc.Error` maps to an `EtcdError` *value*. `ContextError` is used only inside `isHaltErr`'s `ErrNoLeader` test and `close()` (not this path); `Authenticate`'s `toErr` gives an `EtcdError`, a status or a ctx error | covered by the rows above |
| closed watcher / closed client | `"no stream found for context"` | `*errors.errorString`, the fixed text |

Run 2 checks, for every non-nil error:
* the type is in `clientErrTys`;
* it has no `Unwrap() error`, `Unwrap() []error`, `As` or `Format` method;
* two `Error()` calls agree, and `Error` has the signature `Error() string`;
* only a `*status.Error` has `GRPCStatus` or `Is`.

Result: `calls: 1700739; violations of statusErrOk's Go meaning: 0`. Run 1 (without case 7's refused connections)
gave 2009222 calls and 0 violations.

The setup:
* auth-off cluster: 3 members over TCP, clients through bridges (`cluster3.StartBridge`), the dist client
  configuration (`etcdstart` timeouts, `WithNoProxy`);
* auth-on cluster: 3 members (`AuthToken` "simple"), with root and user `u`.

The members are configured like `etcdstart.StartMembers`, but the data lives in the scratch directory because `/tmp`
is over quota.

## Q2: does the verbatim copy hold?

Yes. The in-process proof of `watcher.RequestProgress.spec` gets `statusErrOk` from four places:
* the context premise;
* the `errors.New` model;
* `closeErrPub`, an invariant that `run` maintains from `cliStreamErr` (`Proof/google_golang_org/grpc/InvGrpcStream.lean:340-369`);
* `closeErrOk` of the `v3rpc.Error`/`getToken` results.

`cliStreamErr` is asserted *unconditionally* in the error arms of the client end's trusted specs
(`ClientConn.NewStream`, `SendMsg`/`RecvMsg`/`CloseSend`: `InvGrpcStream.lean:683-745`,
`Spec/google_golang_org/grpc/ClientConn__NewStream.lean:82`). Its justification is grpc-go's client code (`stream.go`,
`toRPCErr`, `rpc_util.go:1133-1157`). It was checked by `examples/k8s/etcd3`'s `TestStreamErrorCells` over a 3-member
TCP cluster with partitions. Nothing in it depends on the server being the in-process model: real grpc-go over TCP is
the code those claims are about.

The claim does have configuration bounds:
* no dial option outside `GrpcDialOpt`;
* no per-RPC credentials that return errors;
* no retry policy;
* only etcd's stream interceptor.

The dist watcher meets them. `watchClientAt` carries `isNewClient cl eps V` (the same `clientv3.New` configuration)
plus `clientNoProxy`, and `WithNoProxy` is in `GrpcDialOpt` (`InvDial.lean:29`).

Compared with KV_Get_dist: the argument has the same shape (the errors are built client-side, and the wire supplies
only code, message and details) and an even smaller surface. RequestProgress makes no unary call of its own, applies
no `ContextError` substitution, and drops send errors. The two new paths are:
* the un-mapped `ErrNoLeader` status;
* `getToken`'s `EtcdError` at stream open.

Both are exercised above. The status-details caveat (KV review F1) applies unchanged: `Is` compares the whole proto,
and `Error()` reads only the code and message.

## D1 (docstring, optional)

The axiom's "Why it is true" asserts that "grpc's `status` accepts each error it returns", but does not say why the
close error does across machines. Suggested addition:

> the stream's close error is set by `run` only: the raw `Recv` error on a halt or `ErrNoLeader`, or `v3rpc.Error`
> of `openWatchClient`'s (`NewStream`'s, etcd's interceptor's `getToken`, or `w.ctx`'s `Canceled`). All of them are
> built in the caller's process by grpc-go (`cliStreamErr`, unconditional of the peer) or clientv3, and a remote
> member chooses only their code, message and status details. `addSubstream`'s `CancelReason` error is overwritten by
> `run`'s defer before `donec` closes.

## Proposed `etc/errdesc-check.py` entry

`WatchDist.lean` mentions `statusErrOk` only in `RequestProgress_dist`; `Watch_dist` names none of the gate's
predicates. The key is the Spec file:

```python
    'Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/WatchDist.lean':
        'RequestProgress_dist only (Watch_dist names none): nil, errors.New\'s "no stream found", ctx.Err() (isContext) or run\'s closeErr, a raw Recv status/io.EOF or v3rpc.Error of NewStream\'s/getToken\'s error, all built in the caller by grpc-go (cliStreamErr, peer-independent) or clientv3, the member choosing only code, message, details; real 3-member cluster, 13 failure kinds, 0 violations (review-requestprogress-statuserr)',
```

Side note, outside this review: on this branch the gate also fails on
`Spec/.../dist/KVGetDist.lean`, because it has no REVIEWED entry. Its review (`kv-get-dist-statuserr.md`) exists, but
the entry is missing.
