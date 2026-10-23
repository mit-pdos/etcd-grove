# Plan: the examples' clients configured as etcd's clients are in practice (timeouts)

**Status.** Finished. T0 and T1 carried out (2026-10-23, branch `client-timeouts`;
`notes/decisions.md`, "D-T1..D-T5"); T2's gates run with them; T3 carried out (2026-10-23, branch
`with-timeout-bg`: Perennial `c25bef57e`'s `wp_WithTimeout_Background`, the pin moved to it, the
axiom `context.WithTimeoutBackground.wp_proof` a theorem; `notes/perennial-changes.md`, "Landed"). What differed
from the plan below: (1) `NewClient(addr, lg)` stays, as `NewClients({addr}, lg)`, so the five
one-endpoint callers and their proofs are untouched; (2) D-T4's "no statement changes" holds for
the conclusions only: `putget_safe`, `putget3_safe`, `linkvtxn_safe` and `linkv3p_safe` gain the
premise `ContextErrsClient` (Go's context error types), which the watch theorems already took,
and every spec on the call chains takes it and `ContextReadErrs` as class premises; (3) D-T5 done
(the policy on every member; D28's axiom in five more collections, nothing new in the baseline);
(4) linkv3p's `TestFailover` rewritten as D-T1's risk foresaw: the blackholed member's calls fail
at 5s, 10s and 15s (request timeouts, reads too), the keepalive close at 16s fails the calls in
flight, then failover; `cutRun` accepts reads that failed at their request timeout;
`TestWatchFailover`'s blackholes 18s (over the 16s close). The ten call-site proofs each use one
lemma, `client.wp_WithTimeout_bg` (`Proof/go_etcd_io/etcd/client/v3/TimeoutCtx.lean`).

## Problem

The etcd examples (`examples/putget`, `putget3`, `linkvtxn`, `linkv3p`, `watchkv`, `cachekv`,
through `examples/common`) make every client call with `context.Background()`: no request
timeout. Their `clientv3.Config` sets no `DialTimeout`; only linkv3p's clients have gRPC
keepalive (D28) and only linkv3p's members the server-side keepalive policy. Nobody uses etcd
that way:

| who | dial timeout | per-request timeout | client keepalive (time / timeout) |
|---|---|---|---|
| `etcdctl` defaults (`etcdctl/ctlv3/ctl.go`) | 2s | 5s (`--command-timeout`) | 2s / 6s (grpc clamps the time to its 10s floor) |
| `client/v3`'s README and `doc.go` | 5s | `ctx, cancel := context.WithTimeout(context.Background(), timeout)` around each call | — |
| Kubernetes' API server | 20s | per request | 30s / 10s |
| the examples today | none | none | linkv3p only: 10s / 2s |

`notes/client-cut-plan.md` D-C5 records the consequence: a call in flight on a connection a
blackhole silences hangs until the connection closes; a call made while there is no connection
waits forever (the client's `WaitForReady(true)`). A real client fails such a call at its deadline
(`context.DeadlineExceeded`) and goes on. That failure mode is exactly the one the models were
built to cover and the examples never exercise: a timed-out write may still be applied later (a
pending write of linkvtxn's model, "a failed write stays pending in the model to the end of the
history"), and a timed-out read is not retried (the retry interceptor's `isContextError` branch
returns when `ctx.Err() != nil`, `client/v3/retry_interceptor.go:76-80`).

The servers' timeouts are already etcd's: `TickMs: 100`, `ElectionTicks: 10` are `embed`'s
defaults (heartbeat 100ms, election 1s), so `ReqTimeout()` is etcd's `5s + 2·1s = 7s`; `MaxTxnOps`
and `MaxRequestBytes` are the defaults; the raft-only examples (`kv`, `kvwitness`) propose with
`context.Background()` as raft's own `raftexample` does (`context.TODO()`). What `embed` sets and
the examples do not: the gRPC server's keepalive policy (`KeepaliveEnforcementPolicy{MinTime: 5s}`,
linkv3p only) and parameters (`KeepaliveParams{Time: 2h, Timeout: 20s}`, nowhere), and the
warning thresholds (`WarningApplyDuration` 100ms, `WarningUnaryRequestDuration` 300ms: logging
only).

## What the proofs already have (so the change is mostly in the examples)

- **The client's specs take any context.** `ctxOk ctx cd` is `isContext ctx cd ∨ ctxQuiet ctx`
  (`InvGrpc.lean`), and the client's lemmas (`client_put_end_to_end`, `client_Put_rep`,
  `client_Put_st`, the Get/Delete/Txn forms) take `ctxOk` and `ctxErrClient`; `ctxErrClientAll`
  (D37, `ErrorsNewOk.lean`) gives `ctxErrClient` of every `isContext`. The examples' call proofs
  (`common/Writer.lean`, `putget/Main.lean`, `putget3/Main.lean`, `linkv3p/writer.lean`,
  `linkvtxn/call{Get,Put,Del,List,Txn}.lean`) get both today from `client.background_ctx`.
- **`context.WithTimeout(context.Background(), d)`** has a spec: the trust-boundary axiom
  `context.WithTimeoutBackground.wp_proof` (`Spec/context/WithTimeoutBackground.lean`, the read
  loop's `sendReadIndex`), giving `isContext ctx' cd` and a cancel function callable from
  anywhere. It is already in every etcd example's collection (`etc/tcb-collections/{putget,
  putget3,linkvtxn,linkv3p,watchkv,cachekv}.txt`, through the server), so using it in the
  examples adds no axiom. Its premise `context.isClosedchanInit` comes from the package's
  initialization (`isClosedchanInit_of_init`, as `cachekv/Main.lean:134`).
- **`DialTimeout > 0`** is covered: `clientCfgOk` does not constrain it, and `newClient`'s proof
  takes the `DialTimeout > 0` branch with Perennial's `wp_WithTimeout` on the client's cancel
  context (`newClient.lean:210`). At the pin the client dials with `grpc.NewClient` (no blocking
  dial), so `DialTimeout` bounds only `getToken` and `checkVersion`, both no-ops in the examples'
  configuration; it is realistic, not behavior-changing.
- **Keepalive** is D28: any `DialKeepAliveTime`/`DialKeepAliveTimeout` in `clientCfgOk`
  (`kaOpts`); the server's `grpc.KeepaliveEnforcementPolicy` an axiom in linkv3p's collection.
- **A timed-out write is at most once**: the fork's fix of the interceptor
  (`issues/etcd-client-retry-put-ctx-error.md`) and D29's refusal-free members, both proved.

## Decisions (recommendations; to confirm)

**D-T1. One configuration, etcdctl's defaults, in `examples/common`.** Constants
`DialTimeout = 2s`, `RequestTimeout = 5s`, `KeepAliveTime = 2s`, `KeepAliveTimeout = 6s`
(etcdctl's: what a person who types `etcdctl put` gets); `common.NewClient(eps []string, lg)`
builds the `clientv3.Config` from them (endpoints, `DialTimeout`, `DialKeepAliveTime`,
`DialKeepAliveTimeout`, logger); linkv3p's `newClient` (10s / 2s, chosen for its tests' failover
speed) goes, replaced by `common.NewClient`. *Risk:* linkv3p's `TestFailover` is written for
today's configuration: it expects the first failures of the blackholed client's calls to be the
keepalive close, at least 10s in (`linkv3p_test.go:388-414`, `stalled` and `now < 13*time.Second`).
With a 5s request timeout the calls fail at 5s, before any keepalive close (reads too: the
interceptor returns a context error when the caller's context is done, so a read fails over only
once the connection is closed), and with 10s (the clamped 2s) + 6s that close comes at 16s, not
12s. T0 rewrites the test's phases around that (timeouts from 5s, failover after the keepalive
close) and re-times the others; if a test becomes slow, keep the keepalive pair as parameters of
`NewClient` and give linkv3p its 10s / 2s (D28's values, documented in `linkv3p.go:209-211`)
rather than two configurations of everything.
*Rejected:* the README's 5s dial timeout and no keepalive (keepalive is what every production
client sets, D28); Kubernetes' values (30s / 10s make every failover test minutes long).

**D-T2. Every unary call under a request timeout, the README's pattern.** At each call site:

```go
ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
resp, err := cli.Put(ctx, key, val)
cancel()
```

No `defer`: Goose translates it (`with_defer`), but none of the examples' translated code uses it
and the proofs would gain a defer frame for nothing; `cancel()` right after the call is the
README's own form. Sites: `putget.go` (Put, Get), `putget3.go` (Put, Get), `common/watch.go`'s
`Writer` (Put; used by watchkv and cachekv), `linkv3p.go`'s `writer` (Put), `linkvtxn.go`'s
`callGet`, `callList`, `callPut`, `callDel`, `callTxn` (which linkv3p's `Apply` also runs).
Watches keep `context.WithCancel(context.Background())`: a watch is long-lived, and its context
is cancelled, not timed out, in practice too. (Kubernetes also wraps a watch's context in
`clientv3.WithRequireLeader`; its spec is stated for `Background()` only, `notes/audit.md`,
`WithRequireLeader.wp_proof`. Out of scope here; a plan of its own if wanted.)

**D-T3. The spec of `WithTimeout(Background(), d)`: the existing axiom now, a Perennial lemma
later.** T1 uses `context.WithTimeoutBackground.wp_proof` (no trust change). It is a general fact
Perennial can prove as it proved `wp_WithCancel_Background` (`WithCancelGen.lean`): `Background()`'s
`Deadline()` (`wp_background_Deadline`), `propagateCancel` from `Background()`
(`wp_propagateCancel_background`) and the timer context (`isContext_timerCtx_of`) are all there;
only `WithDeadlineCause`'s proof takes an `isContext` parent. T3 proposes `wp_WithTimeout_Background`
(and `wp_WithDeadline_Background`) to Perennial and, at the pin that has it, turns the axiom into
a proved lemma: one axiom fewer in every etcd collection and the baseline. Entry in
`notes/perennial-changes.md` at T0.

**D-T4. The theorems' statements do not change.** A timed-out call is an error, and every example
handles errors already: `putget`/`putget3`'s `Main` return, `Writer` logs only successful puts,
linkvtxn's `Apply` reports the failure and the model keeps the write pending. So the closed
theorems (`putget_safe`, `putget3_safe`, `linkvtxn_safe`, `linkv3p_safe`, `linkv3p_watch_safe`,
`watch_safe`, `cache_safe`) are restated only through the examples' new code. Nontriviality by the
Go tests, as D-C5: linkv3p's cut tests count `context.DeadlineExceeded` among the failed
operations (a timeout actually fires under the cuts), and `TestClientCuts`' blackhole (3s, under
the 5s timeout) is lengthened or a second one added so that calls time out while the connection
is silent, not only when it is closed.

**D-T5 (optional). The members' gRPC keepalive as `embed`'s.** `common.Serve` passes
`grpc.KeepaliveEnforcementPolicy{MinTime: 5s}` (as linkv3p's `startMember`) -- needed once the
clients ping, else grpc answers a fast pinger with `GOAWAY too_many_pings` (D28, KA0; at the 10s
clamped client time it is not hit, but a configuration a client may lower). Cost: the existing
axiom `grpc.KeepaliveEnforcementPolicy.wp_proof` enters the other five examples' collections (no
new axiom). `grpc.KeepaliveParams{Time: 2h, Timeout: 20s}` (embed's server-side pings) would be
one more neutral-option axiom (+1): not recommended now; it changes nothing a test can observe.

## Stages

### T0. The Go change, tested

- `examples/common/common.go`: the constants, `NewClient(eps []string, lg)` as D-T1 (and
  `Serve`'s policy option if D-T5); `common/watch.go`'s `Writer` as D-T2.
- The call sites of D-T2; linkv3p's `newClient` removed; the examples' doc comments (each lists
  the functions it calls: add `context.WithTimeout` and the cancel).
- `go test` of every example (`examples/`: `putget`, `putget3`, `common`, `linkvtxn`, `linkv3p`
  with `-race`, `watchkv`, `cachekv`), re-timed; linkv3p's budgets adjusted (D-T1's risk) and
  D-T4's timeout counts added.
- `etc/goose.py --project common putget putget3 linkvtxn linkv3p watchkv cachekv`, then
  `etc/goose.py --check`; `etc/gen-init.py --check` (no initializer changes expected).
- `notes/perennial-changes.md`: the `wp_WithTimeout_Background` entry (D-T3).

### T1. The proofs

- `common.NewClient`'s proof: `clientCfgOk` over the new configuration (nothing to add to the
  predicate: `DialTimeout` free, keepalive by `kaOpts`); its spec takes the endpoint list
  (linkv3p's `newClient` spec is the model); the endpoints' `plainEndpoints` premise unchanged.
- The ten call-site proofs: `wp_apply context.WithTimeoutBackground.wp_proof` (with
  `isClosedchanInit_of_init`), then `ctxOk_of_isContext` and `ctxErrClientAll` where
  `background_ctx` gave `ctxOk` and `ctxErrClient`; the `cancel()` call by the axiom's
  postcondition. A small lemma `timeoutCtx` in the client (`InvServerKV.lean`, beside
  `background_ctx`: from `isContext` and `ctxErrClientAll`, the pair the call lemmas take) keeps
  the ten proofs one line each.
- `common.Serve`'s proof with the policy option (D-T5), as linkv3p's `startMember`.
- The links: `etc/gen-link.py` for every example mode (`--common`, `--linkvtxn`, `--linkv3p`,
  `--watchkv`, `--cachekv`) and their `etc/link-lean-first-*.txt` callee lists
  (`context_WithTimeoutBackground` as `link-lean-first-read.txt:12,31`); putget's and putget3's
  `Main` are linked by hand in their `Results.lean` (no gen-link mode).

### T2. Gates and notes

- `etc/gates.sh`; `etc/tcb-report.py --check --update` only for the collections whose axiom set
  moves (D-T5: `grpc.KeepaliveEnforcementPolicy.wp_proof` into five collections; nothing new in
  the baseline); `etc/verified-code.py` unchanged in substance (the same functions, a few more
  lines).
- `notes/STATUS.md` (this plan's line, the examples' summary), `notes/decisions.md` (D-T1..D-T5
  as one entry), the examples' doc comments.

### T3. The Perennial lemma, and the axiom retired

- Perennial, a branch off `lean`: `wp_WithTimeout_Background` and `wp_WithDeadline_Background`
  (the `Background()` parent of `WithDeadlineCause`, as `wp_WithCancel_Background`'s), landed by
  Perennial's workflow; the pin bumped.
- Here: `Proof/context/WithTimeoutBackground.lean`'s axiom becomes a theorem over the new lemma;
  `etc/tcb-report.py --check --update` (−1 axiom in the baseline and in the `read`, `server` and
  every etcd example's collection); the perennial-changes entry marked landed.

## Out of scope (recorded)

- `clientv3.WithRequireLeader` on watch contexts (D-T2's note).
- The raft-only examples' `context.Background()` in `node.Propose`/`ReadIndex` (`kv`,
  `kvwitness`): raft's own example does the same; the server's calls, which pass a timeout, are
  proved over `nodeCtx` already (R7a).
- A `DialTimeout` that bounds a blocking dial: the pinned client has none (`grpc.NewClient`).
