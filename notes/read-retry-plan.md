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

### R1. Audit (notes only)

- Each refusal's source in the server, with the facts its exclusion needs: `IsLearner`'s spec, auth
  being off in the server's invariant, and where `ErrInvalidAuthToken` and `ErrAuthOldRevision`
  are returned.
- How `noRefusalAt` gets from linkv3p's members (`startMember`, `v3rpc.Server`'s registration) to
  the client's connection (`clientOk`, D27's `anySpec`).
- If the server's facts are out of reach, stop and ask: the two-client fallback, or a premise.

### R2. The trust boundary (asked of the user)

- `etcdRefusal`; `noRefusalAt`; the attempt contract's error side; the handler contract's
  option; `notes/decisions.md` D29; ask.

### R3. The server

- The unary interceptor, the KV handlers' error paths, `v3rpc.Server`'s registration giving
  `noRefusalAt` for the KV methods.

### R4. The client

- The stronger specs of `isSafeRetry`, `isSafeRetryMutableRPC` and `shouldRefreshToken`. The
  interceptor's policy-aware contract (`Client__unaryClientInterceptor.lean`, the loop's invariant
  holding the ordinary precondition until the first attempt). `etcdConn_Invoke`, the `retryKVClient`
  methods, `kv.*` and `Failover.lean`: `Range` with the persistent read update (already so, D27),
  `Put`/`DeleteRange`/`Txn` ordinary on a refusal-free connection.
- `dialSetupOpts`/`New`: any `MaxUnaryRetries` gives the policy-aware contract.

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
