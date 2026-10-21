# Plan: read retries, with the client's default configuration

Status: planned (2026-10-21, branch `read-retry`). Follows `notes/keepalive-plan.md` (D28) and
`notes/client-cut-plan.md` (K4, failover, D27).

## Goal

A production etcd client is configured with the defaults: `MaxUnaryRetries` unset, which means
100 attempts (`defaultUnaryMaxRetries`, `client.go:247-270`). A read (`Range`, the repeatable
policy) that fails with `Unavailable` is retried after a short backoff (`roundRobinQuorumBackoff`,
25ms), and the next attempt goes to another member (the round-robin balancer). So a read whose member
is cut off does not fail: the caller sees the answer of another member. linkv3p's clients are
configured with `MaxUnaryRetries: 1` (D21i (A), 2026-10-19), so today every call through a cut
member fails, reads included (`TestFailover`: one to three failures per cut).

This plan has linkv3p's clients use the default configuration, so `linkv3p_safe` covers a client
that retries reads as production clients do.

## The catch: one client, one bound

The retry bound is per client: `withMax(MaxUnaryRetries)` is an option of the interceptor installed
at dial, and `withMax` is unexported, so no call can lower it. A client that retries reads also
retries writes, whenever the interceptor finds a write safe to retry. For a write (the
`nonRepeatable` policy, every unary call but `Range`), retrying a request that was applied applies
it twice. linkvtxn's write update is ordinary (fired once, D21 M6), so the proof needs:

**A write is sent again only after an attempt that did not apply it.** At the fork's pin
(`8a24be2a3`, the context-error fix of `issues/etcd-client-retry-put-ctx-error.md`), the
interceptor retries a `nonRepeatable` call in three cases (`retry_interceptor.go:62-96`):

1. `shouldRefreshToken`: the error is `ErrUserEmpty` with a token bundle (none without
   authentication: false already), or `retryAuth` (on by default) and the error is
   `ErrInvalidAuthToken` or `ErrAuthOldRevision`. `refreshToken` with no bundle returns nil, and
   the loop continues.
2. `isSafeRetry`: `ErrGRPCNotSupportedForLearner` with more than one endpoint (linkv3p's three).
3. `isSafeRetry`, `isSafeRetryMutableRPC`: an `Unavailable` status, or an error that is not a
   status, whose description is `"there is no address available"` or `"there is no connection
   available"`. These are messages of grpc's old balancer, and grpc v1.84 (linkv3p's) never makes
   them: a grep of its sources finds neither. In practice a write is never retried after a
   connection error.

The context-error branch returns the error for a `nonRepeatable` call (the fork's fix). Every other
error stops the loop.

So the write retries come from **refusals**, errors the server returns when it did not apply the
request: a learner refusing (in the server's unary interceptor, before the handler), and
authentication errors (before the proposal, or at apply). linkv3p's members are voters with
authentication off, so they never refuse.

## Design

**D-RR1. Refusal-free servers (recommended).** The proof shows that a write is never retried,
because the error that would cause it never arrives:

- `etcdRefusal err : Prop`: the errors of cases 1 to 3 (by status code and description, as the
  client's code tests them).
- **The trust boundary (to be approved by the user, D29).** An attempt's error is grpc's own or the
  server's status, forwarded unchanged. grpc's own errors are never refusals: its descriptions are
  its own, and grpc v1.84 has neither of case 3's. So the attempt contract (`grpcInvokerOk`,
  through `grpc.ClientConn.Invoke`'s axiom) gains, on its error side, `⌜¬ etcdRefusal err⌝` for a
  connection whose servers never answer with a refusal (`noRefusalAt addr` for each of its
  addresses, a persistent fact the server side provides).
- **The server's side (proved).** linkv3p's members give `noRefusalAt`. The unary interceptor
  (`newUnaryInterceptor`, verified) reaches the learner branch only if `IsLearner()` (an axiom,
  `EtcdServer__IsLearner.lean`, whose spec may not say enough: R1 checks). The KV handlers' auth
  errors need authentication off (`AuthInfoFromCtx`, `isOpPermitted`, verified; whether the
  server's invariant knows auth is off is for R1 to check). The handler contract
  (`grpcHandlerOk`) gains the same pure fact on its error side, `⌜¬ etcdRefusal err⌝`, as an
  option of the method's registration.
- **The client (proved).** `isSafeRetry`, `isSafeRetryMutableRPC` and `shouldRefreshToken` get
  stronger specs: for a `nonRepeatable` call, `true` only of an `etcdRefusal`. The interceptor's
  contract becomes policy-aware: a call with the repeatable policy (`withRepeatablePolicy`, which
  `retryKVClient.Range` passes) takes `□ ▷ Spec m Φ`, as today; any other call takes an ordinary
  `▷ Spec m Φ` on a refusal-free connection, since none of its failed attempts is retried. That
  makes `isEtcdConn1` and `reqPre`'s second disjunct (D21i (A)) unnecessary, but they stay for the
  examples that keep `MaxUnaryRetries: 1`.

The closed theorem's statement does not change. Its premises stay the same, and what the clients
are configured with moves to the default.

**Alternatives.**

- *(Refunds)* Instead of excluding refusals, a refusal gives the precondition back: the handler
  contract returns `Spec m Φ` with a refusal, and the attempt contract carries it to the client.
  This is more general (a cluster with learners or authentication), but each refusal must be shown
  to leave the update unfired. `ErrAuthOldRevision` comes at apply, after raft's commit, where the
  update fires (D21 M6b), so the server's apply would also need to change. Not now. D-RR1 can grow
  into this later.
- *(Two clients)* Each worker gets two clients: one with the default configuration for reads, one
  with `MaxUnaryRetries: 1` for writes. There is no trust-base change and little proof (a second
  `newClient`, reads through one client and writes through the other). But production programs
  do not do this, and the goal is the production configuration. A fallback if R1 finds the
  server's facts out of reach.

## Stages

### R0. The Go program, measured

- `newClient`: drop `MaxUnaryRetries: 1`.
- `TestFailover`, `TestClientCuts`, `TestMainRun` re-measured: failures should now be writes and
  transactions only, and fewer. Their checks assume some failure during a cut; adjust them to
  count reads and writes apart, and check that a read fails only if every member it could reach
  was cut.
- A probe confirming that a write is not retried after a connection error. The bridge counts the
  `Put`s it forwards, and one cut in flight must give at most one forwarded copy.
- `go test -race`.

**Done (2026-10-21).** `newClient` has the default retries (`MaxUnaryRetries` unset). The tests
record whether each operation is a read (a `Get` or a `List`: a `Range`). Findings:

- **No read failed**, in 3 runs of the package (one under `-race`). A read held by a cut is retried
  once the cut's connection closes, on the next member. `cutRun` now checks that no read fails.
  Only writes fail: 1 to 5 per run of `TestFailover`, 0 to 3 of `TestClientCuts`, where each
  client has one bridge and a held read waits for the unblackhole.
- `TestFailover` with retries saw one failure in a run where, before, the other clients' stalls
  failed too: those stalls were reads, now retried. Its phases are driven by **stalls** (a failed
  operation, or one that took more than 5s, which is a keepalive close's) instead of failures; a
  failure alone could be missing from a run. `TestClientCuts` checks for a cut operation through
  client 1 (a failure, or a read held over the unblackhole).
- **`TestWriteOnce`** (the probe): 3 workers put distinct keys through Main's clients for 20s,
  while member 1's bridge is blackholed for 15s and member 2's connections are dropped every
  second. Each key's version must be 1, so no put was applied twice. In 4 runs, 16,000 to 60,000
  puts each: 6 to 8 failed, and every key had version 1. Of the failed puts, a few were applied
  anyway (in flight when the connection closed); none was resent.
- `TestMainRun`'s comment: a read at an isolated member is retried at the next member.

The translation is regenerated. linkv3p's `newClient` proof no longer builds: the configuration's
literal has no `MaxUnaryRetries`, and `clientKVOnce` needs one attempt. It builds again at R5.

### R1. Audit (notes only)

- Each refusal's source in the server, with the facts its exclusion needs: `IsLearner`'s spec, auth
  being off in the server's invariant, and where `ErrInvalidAuthToken` and `ErrAuthOldRevision`
  are returned.
- How `noRefusalAt` gets from linkv3p's members (`startMember`, `v3rpc.Server`'s registration) to
  the client's connection (`clientOk`, D27's `anySpec`).
- If the server's facts are out of reach, stop and ask: the two-client fallback, or a premise.

**Done (2026-10-21): the server's side is out of reach at D-RR1's cost; stopped and asked.**
Each refusal at its source:

- **The learner refusal** (`newUnaryInterceptor`, verified: `IsMemberExist(MemberID()) &&
  IsLearner()`). `EtcdServer.IsLearner` is an axiom returning any boolean
  (`EtcdServer__IsLearner.lean`). The membership model owns each member's `IsLearner` field with
  any value (`membership.memberIs`), and records only that the local member stays in the map
  (`rcLocalIn`). Excluding the refusal needs the local member's flag `false` in the model (from
  bootstrap's members, kept by the conf changes the server takes, `ccApplyOk`: an `AddNode` of a
  voter) and a stronger `IsLearner` axiom (it returns that flag): a model change and a change to a
  trust-boundary spec. Medium.
- **The auth errors at apply** (`ErrAuthOldRevision`, `ErrUserEmpty`, `ErrPermissionDenied`):
  **in reach.** The apply side's auth store has a mode (`apply.isAuthStore … on`, unit T1).
  `NewAuthStore` gives `on = false` on a fresh backend, where the permission checks return `nil`
  and `AuthEnable` is never called.
- **`ErrInvalidAuthToken` at the request side** (`AuthInfoFromCtx`, before the proposal or the
  read). Its contract (`isReqAuth`, `InvRequest.lean:2463`) returns any `applyErrIs` error, and the
  real store's spec any of five auth errors (`authErrIs`). It has no off mode: the store's
  `enabled` field is any boolean (`enabledP`). Adding one, with `enabled` tied to the apply side's
  `on`, is small to medium.
- **Error identity, the large part.** Even with both sources excluded, the handler contract would
  have to say *which* error it returns. The client tells a refusal by its description
  (`rpctypes.Error` looks the status message up), so the server would have to say that the
  message of every error it answers is not a refusal's. Today the server's errors are described
  by structure, not identity: `applyErrIs` (an error tree, a safe map key whose `Error()`
  returns, 77 files, 176 uses), `srvErrIs`, `kvOut`'s error side (`∃ e, A.err q e`, with the
  returned error unrelated to `e`), and `togRPCError`'s result (non-nil). `togRPCError`'s default
  case sends `err.Error()` as the message (`codes.Unknown`), so the property is about the
  messages of every error the request path can return: the raft node's, the backend's, the wait
  registry's, the context's, many of them from axioms whose specs would each have to name their
  messages. Large, and it touches many trust-boundary specs.

So D-RR1 as planned (proved refusal-freedom) costs far more than the rest of the plan. The
choices:

- **(P) A premise on the server, as an axiom (recommended).** `noRefusalAt addr` for a member
  booted as a voter of a new cluster, with authentication off, is a trust-boundary axiom about
  the server (D29). Code inspection backs it. The refusal descriptions come only from
  `togRPCError`'s map entries for `auth.ErrInvalidAuthToken`, `ErrAuthOldRevision` and
  `ErrUserEmpty`, and from the interceptor's learner branch. The auth errors are returned only
  with authentication enabled (`AuthInfoFromCtx`, `isOpPermitted`: `if !as.IsAuthEnabled() {
  return nil, nil }`), and the learner branch only at a learner. A wrapped error has a longer
  message, and grpc's own errors have grpc's messages. The client's side (R4) and the attempt
  contract's error side are as planned. The server's KV results stay proved. The learner and
  auth parts can be proved at their sources later, which would shrink the axiom to error identity
  alone.
- **(T) Two clients**: no trust-base change, but not the production pattern.
- **(F) The full proof**: error messages through the server's request path, as above.

### R2. The trust boundary (asked of the user)

- `etcdRefusal`; `noRefusalAt`; the attempt contract's error side; the handler contract's
  option; `notes/decisions.md` D29; ask.

With (P) (chosen by the user, 2026-10-21) the handler contract does not change. D29, as drafted:
`errDesc` (an error's description, a function of the error, through `status.FromError`), `errors.Is`
on a leaf error keeps the description, rpctypes' initializers give the refusals' descriptions,
the attempt's error is `noRefusal` on a connection to `noRefusalAt` addresses, and a new axiom
says the members are `noRefusalAt`. R3 shrinks to stating the members' axiom from `startMember`'s
facts.

**Done (2026-10-21; D29 approved).** The boundary is in place:

- `errDesc`, `refusalDescs` and `noRefusal` are in `cache/v3/Base.lean`.
- `status.FromError`'s `Message()` returns `errDesc err`, and for a non-status error its
  `Error()` does too.
- `errors.Is` returns `true` only for equal descriptions.
- rpctypes' facts give the refusals' descriptions and each `errStringToError` entry's description
  (`etc/gen-init.py`).
- `rpctypes.errDesc_etcdError` (a new axiom) says an `EtcdError`'s description is its `desc`.
- `noRefusalAt` and the attempt contract's new error clause are in `InvGrpc.lean`.
- The bridge carries refusal-freedom (`bridge.New`'s spec, `forwards`).
- `etcd_noRefusal` (a new axiom) is in `v3rpc/NoRefusal.lean`.

The proofs that read the restated specs are adapted by pattern only (`ErrorDesc`, `Error`,
`shouldRefreshToken`, `isSafeRetry`, the interceptor, `startBridge`). `lake build` fails only in
linkv3p's `newClient` (since R0). `etc/tcb-report.py --check`, which needs a full build, waits
until R5.

### R3. The server

- The unary interceptor, the KV handlers' error paths, `v3rpc.Server`'s registration giving
  `noRefusalAt` for the KV methods.

**Done (2026-10-21).** `startMember` applies `etcd_noRefusal` before `etcd_kv_started`, with the
server's request view, the quota wrapper, the gRPC server with its KV registrations, the client
listener, and authentication off (`memberUp`'s `E.authOn = false`). `memberServed` gains
`⌜noRefusalAt client⌝`, and `Main` takes it apart (unused until R5, where each bridge's address
gets it through `forwards`). `startMember` and `Main` build.

### R4. The client

- The stronger specs of `isSafeRetry`, `isSafeRetryMutableRPC` and `shouldRefreshToken`. The
  interceptor's policy-aware contract (`Client__unaryClientInterceptor.lean`, the loop's invariant
  holding the ordinary precondition until the first attempt). `etcdConn_Invoke`, the `retryKVClient`
  methods, `kv.*` and `Failover.lean`: `Range` with the persistent read update (already so, D27),
  `Put`/`DeleteRange`/`Txn` ordinary on a refusal-free connection.
- `dialSetupOpts`/`New`: any `MaxUnaryRetries` gives the policy-aware contract.

**Done (2026-10-21).**

- **Specs that name descriptions and policies.**
  - `ErrorDesc` returns `errDesc err`.
  - `rpctypes.Error` keeps the description.
  - `isSafeRetryMutableRPC` and `shouldRefreshToken` return `true` only on a refusal.
  - `isSafeRetry`, given the call's policy (`retryOptsPol`), returns `true` only on a refusal or
    for the repeatable policy.
- **The options' policy.**
  - `defaultOptions` is `nonRepeatable` (`W8 1`; its initializer's fact, `etc/gen-init.py`).
  - The dial's `withMax` and `withBackoff` keep the policy (`optApplyMax … true`).
  - `reuseOrNewWithCallOptions` keeps it through such options, and returns the options themselves
    when there are none.
  - `filterCallOptions` finds no retry option among scalar options.
- **The interceptor's contract has three modes** (`AttemptMode`, `modePre`, `etcdInterceptorOkM`).
  The third, `.write` (`etcdInterceptorOkW`), takes an ordinary precondition whatever the bound,
  on a refusal-free connection with scalar call options.
  - The loop's invariant gains `md = .write → a = 0`. Each `continue` is a contradiction in that
    mode: the context-error branch returns for `nonRepeatable`, a token refresh follows an auth
    refusal, and `isSafeRetry` is `true` only on a refusal or the repeatable policy.
  - `isEtcdConn` carries the third mode. `dialSetupOpts`, `dial` and `newClient` pass it on.
- **The request precondition takes the call options** (`reqPre conn addr vs P`).
  - Its third case is a refusal-free connection with scalar options. `etcdConn_Invoke` uses the
    third mode for it.
  - The stubs prepend grpc's `StaticMethod` option. Its axiom's spec now also says it is a scalar
    option (it returns a `StaticMethodCallOption`): a restatement, recorded in D29.
    `reqPre_scalar_app` carries the precondition across it.
  - `callOptsAt` (a client's call options) is scalar. `kvReqPre` and `txnReqPre` gain the
    refusal-free case, and `kvReqPre_conn` passes the scalar fact on.
- **The failover results take `writeOnce`** (a one-attempt client, or refusal-free members), and
  `txnWriteOnce` for transactions. linkvtxn's `Calls` passes its one-attempt client's fact
  (`ileft`).

`lake build` fails only in linkv3p's `newClient` (R0).

### R5. linkv3p (and linkvtxn)

- `newClient`'s proof without `MaxUnaryRetries`, `clientOk` with `noRefusalAt`, `Apply`/`Calls`
  through the policy-aware contract. linkvtxn's `Main` moves to the default as well, unless that
  costs more than it shows.
- The gates: `lake build`, `etc/goose.py --check`, `etc/gen-init.py --check`, `etc/gen-link.py`,
  `etc/tcb-report.py --check` (D29's change to the axioms' statements), the collections, and
  `go test -race`.

## Trust base (estimate)

No axiom added. Restated: `grpc.ClientConn.Invoke`'s promise (the attempt's error is not a
refusal on a refusal-free connection) and the handler contract's error side. `EtcdServer.IsLearner`'s
axiom may need a stronger spec (R1); that is a further change, asked with D29.
