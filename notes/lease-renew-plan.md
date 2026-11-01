# The lease renewal entry point: `EtcdServer.LeaseRenew` (item 5 of the lessor/auth list, 2026-11-01)

Spec-first, as `notes/lease-read-plan.md`. Branch `lease-renew`. **The user's scope (2026-11-01):
"LeaseRenew, contracts"**: translate `LeaseRenew`'s body and prove its spec over trust-boundary
contracts of the callees that stay names-only; the gRPC keep-alive stream
(`LeaseServer.leaseKeepAlive`) and `lessor.Renew`'s body are not in this stage.

## Scope (2026-11-01)

`EtcdServer.LeaseRenew(ctx, id)` (`server/etcdserver/v3_server.go:488-571` at the pin):
- a tracing span (`traceutil.Tracer.Start`, `span.End`; specs exist, the KV entry points use them);
- **on the leader** (`isLeader`): `ensureLeadership` (`ErrNotPrimary` if not); then, with
  `FastLeaseKeepAlive`, `lessor.Lookup(id)` and `waitAppliedIndex` only if it is absent, else
  `waitAppliedIndex`; `checkLeaseRenew` (proved); `lessor.Renew(id)`: its `ttl` on `nil`, its
  error unless `ErrNotPrimary`, which falls through to the forwarding;
- **the forwarding** (a follower, or a demoted leader): under `context.WithTimeout(ctx,
  Cfg.ReqTimeout())`, while the context has no error: `waitLeader`, `checkLeaseRenew`, then
  `leasehttp.RenewHTTP` to each of the leader's peer URLs (`url + leasehttp.LeasePrefix`), returning
  on `nil` or `ErrLeaseNotFound`, other errors retried after `time.Sleep(50ms)`; at the timeout
  `ErrTimeout`, `ErrCanceled` or the context's error.

Translated now (`Code/.../etcdserver.toml`, `LeaseRenew`; a new names-only package
`server/lease/leasehttp`, `Code/.../lease/leasehttp.toml`, for `RenewHTTP` and `LeasePrefix`).

**What the spec can say**: on `nil`, the renewal passed the key check (the last `checkLeaseRenew`
before the success: `leaseCheckFrom` with `leaseKeysVerdictFrom … .write`, as
`checkLeaseRenew.spec`'s post); on an error, an error the gRPC layer can take (`applyErrIs`).
Nothing of the TTL.

**A finding** (recorded: `issues/etcd-lease-renew-keys-follower-lag.md`, not yet reproduced): on a
follower the check reads the follower's lessor (no wait for any index) and the renewal is the
leader's, so a lagging follower's check misses keys the leader's lease holds. The spec states the
check over the local lessor at a lower bound, nothing of the renewed lease; its margin names it.

## Draft (2026-11-01)

The contracts (trust-boundary axioms, each in `Spec/<pkg>/<fn>.lean` with an `axiom … wp_proof` in
`Proof/<pkg>/<fn>.lean`; the user approves them at Freeze):
- **C1 `lease.lessor.Renew`** (names-only in the lease package: heap updates, `refresh`'s time
  arithmetic, the checkpointer call): with the lessor (`lessorInv`), any goroutine: returns a TTL
  and `nil`, or `ErrNotPrimary`/`ErrLeaseNotFound` (the lease package's values). Its argument: it
  touches only what `le.mu` guards (`lessorMu`: the lease's `expiry` half and `remainingTTL`
  (`leaseMeta`), the expiry notifier, the checkpoint heap; with both of `l.expiryMu`'s halves under
  `refresh`), locking `le.mu` itself through the guard; it reads `le.cp` without the lock, which is
  written once, by `SetCheckpointer` in `NewServer`, before any request goroutine runs; the only
  checkpointer is `NewServer`'s, which returns `nil` or `ErrNotPrimary`.
- **C2 `EtcdServer.ensureLeadership`** (names-only: `isActive`, a linearizable read with a
  timeout, `raftStatus`): with the request and read sides' server facts (`isServerReqM`,
  `isServerReadM`, as `leaseTimeToLive.spec`): returns a boolean.
- **C3 `EtcdServer.waitAppliedIndex`** (names-only: `ApplyWaitCommit`, `stopping`, `time.After`):
  the same facts: `nil`, or `ErrStopped`/`ErrTimeoutWaitAppliedIndex` (`applyErrIs`).
- **C4 `EtcdServer.waitLeader(ctx)`** (names-only: the cluster's `Member(Leader())`, a loop on
  `time.After`): the same facts and the context: a member (read-only, `↦□`) with its peer URLs
  (`↦*□`), or `nil` and `ErrStopped`/`ErrNoLeader` (`applyErrIs`). `Member` returns a clone.
- **C5 `leasehttp.RenewHTTP(ctx, id, url, rt)`** (names-only: protobuf marshal, an HTTP POST, the
  reply's decoding): at a context: a TTL and `nil`, or an error the gRPC layer can take
  (`applyErrIs`: `ErrLeaseHTTPTimeout`, `ErrLeaseNotFound`, the HTTP client's and `fmt.Errorf`'s
  errors). **Its assumption on the cluster**, as `leaseTimeToLive.spec`'s: the peer URLs are served
  by etcd's lease handler.
  Its premise on `rt`: `http.roundTripperOk H rt` (an arbitrary `RoundTripper` could panic).
  Also: `RenewHTTP` returns an `fmt.Errorf` error when the reply's ID differs from `id`.
- `leasehttp`'s initializer (`Proof/.../lease/leasehttp/{Base,Init}.lean`, `etc/gen-init.py`'s
  `SPECIAL`): `LeasePrefix` holds *some* string (the trust-boundary axiom `LeasePrefix_init`); its
  value (`"/leases"`) is not stated, since `RenewHTTP` takes any URL.
- `ErrNotPrimary` is now translated (`lease.toml`) and in `leaseInit` (`leaseErrVar`, appended at
  the end so the `icases` patterns of the other readers stay; one, `apply/Init.lean`'s, shifts):
  `LeaseRenew` returns it to the client, so it needs `applyErrIs`, which comes from `leaseErrVar`.
  Before, its initializer was an opaque axiom and no fact named it.

**The entry point**, `EtcdServer.LeaseRenew.spec`: with `LeaseTimeToLive.spec`'s resources and
facts (the auth store and lessor at lower bounds `n`, `m`, their readers, a thread token, the
context) and the server's `peerRt` field (some `http.roundTripperOk` value; a premise, since no
boot proof yet states the field: `NewServer` stores `rafthttp.NewRoundTripper`'s, whose spec gives
`roundTripperOk`): on `nil`, `leaseCheckFrom s E ctx n (fun info =>
leaseKeysVerdictFrom E.authMode n info γl m id .write)`; on an error, `applyErrIs`. **The margin**:
the key check is of the local lessor; the renewed lease is the leader's, possibly holding keys the
check did not see (`issues/etcd-lease-renew-keys-follower-lag.md`), and on the leader a key
attached between the check and `Renew` (`issues/etcd-lease-timetolive-keys-toctou.md`'s window).
The revision re-check is `checkLeaseRenew.spec`'s margin.

## Review (2026-11-01, an independent spec-reviewer)

Findings and what changed:
- **C2 took no reader slots** while `ensureLeadership` read-locks `lgMu` (`Logger()`), the read
  loop's `mux` (`LinearizableReadNotify`) and `r.tickMu` (twice, `isActive`). Now it takes and
  returns `srvLgReader s ∗ srvReadReader s γr ∗ threadTok` (with the thread bound). `tickMu`'s
  reader slots are dropped at node start (`NodeStart.lean`), so no request goroutine holds one: C2
  states that as **an assumption** (its readers are at most the goroutines, below the lock's
  reader limit by the thread bound). A `tickMu` pool, as `lgMu`'s, would remove it.
- **C1 missed a reader slot**: `l.expired()` read-locks the lease's `expiryMu`, whose slots
  `isLeaseObj`'s pool lends for a thread token. C1 now takes and returns `lessorRd lp γl` (its
  `le.mu.RLock`) and `threadTok` (with the bound). Its docstring names `leaseRenewed.Inc()`.
- **C1's checkpointer argument was wrong**: `apply.rqOk` constrains the verified proposers, and
  the checkpointer's `raftRequest` bypasses them. The covering premise is `ckptEffectsOk`
  (`InvBoot.lean`, taken by `NewLessor`, carried by every closed result), whose docstring names
  only the lessor loop's calls. Not exercised today: `srvGrantGuard` is `False`, so no lessor of
  a closed result has a lease, and `Renew` returns before it reads `cp`. **Open, for the user**:
  widen `ckptEffectsOk`'s docstring to `Renew`'s call (an opaque premise every closed result
  carries); the lease-grant work must revisit C1.
- **C5's `roundTripperOk H rt` was ceremonial**: it constrains `RoundTrip` only on requests with
  the raft network's registrations, which `RenewHTTP`'s POST lacks. Replaced by the type of `rt`:
  a `*http.Transport` (what `rafthttp.NewRoundTripper` builds, `transport.NewTimeoutTransport`).
  The cluster assumption is restated: a peer's reply small enough to buffer
  (`maxLeaseHTTPResponseSize`, 100 MiB per call).
- **The entry point's `peerRt` premise has no source**: no construction spec states the field
  (the bootstrap's `prt`, `server.go:330`). **Open**: `NewServer`'s contract must export
  `peerRt ↦□ rt` with its type before a `LeaseKeepAlive` handler can call `LeaseRenew`. The
  entry point also takes `srvReadReader` now (for C2).
- **The margin** names the `FastLeaseKeepAlive` leader path, which skips `waitAppliedIndex`
  (also added to the issue).
- C3, C4 and the package-init change: sound.

## Probe (2026-11-01)

`EtcdServer.LeaseRenew.wp_proof` is proved over the contracts (`lake build` of the module):
every path, the leader's (with and without `FastLeaseKeepAlive`, `Renew`'s three outcomes) and the
forwarding loop's (the timeout context, `waitLeader`, the check, the range over the peer URLs,
`RenewHTTP`'s outcomes, the sleep, the exit). Findings:
- `features.FastLeaseKeepAlive` was untranslated (an axiomatized `val`): now translated
  (`features.toml`).
- The switch after the loop: Perennial's context `Err()` may return any typed error, but once the
  context is done this repository's `context.ErrDone` says `Canceled` or `DeadlineExceeded`, and
  `errors.IsCtxErr` answers `true` on equal values, so the default case (`Logger().Warn`) is
  unreachable; the proof does not call `Logger`. `srvLgReader` stays for C2.
- On `nil`, the check's `leaseCheckFrom` is over the span's context; `Tracer.Start` keeps the
  incoming metadata, so it moves to the caller's (`leaseCheckFrom_ctx`, by `infoBoundM_ctx`).

## Freeze (2026-11-01, the user)

"Approve all": C1-C5 and `LeasePrefix_init` linked as axioms, the TCB baseline updated, an entry in
`notes/decisions.md` ("The lease keep-alive entry point"); C2's `tickMu` assumption stays in its
docstring. "Widen ckptEffectsOk's doc": `InvBoot.lean`'s docstring names `Renew`'s checkpointer
call (no statement changes). "Keep premise, record open": `peerRt` stays a premise of
`LeaseRenew.spec`, open in `notes/STATUS.md`.

## Prove (2026-11-01)

`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseRenew.lean`, no `sorry`, linked in the
server's `Link.lean`. Open: `peerRt` from `NewServer`'s contract; a `tickMu` pool (C2); C1 at the
lease-grant work; a Go reproduction of `issues/etcd-lease-renew-keys-follower-lag.md`.
