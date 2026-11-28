# Review: `GracefulStop_dist.wp_proof` (draft interim axiom, etcd_safe S0)

Reviewed on `origin/etcd-safe-crash-s0/2026-11-26` @9e66b4dbac, 2026-11-26, read-only. Method: the `axiom` skill.
- Spec: `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/GracefulStopDist.lean` (`grpcServing` :42, the spec :46).
- Axiom: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/GracefulStopDist.lean:51`.
- Go code checked: grpc-go v1.84.0 (the version `examples/go.mod` pins) from the module cache, plus the model at
  `models/grpc/server.go`; etcd from the pinned fork `github.com/upamanyus/etcd/server/v3@...251a430ce042`.

## Verdict: SOUND WITH FIXES

I found no program that panics while the axiom proves it doesn't, and nothing produces `grpcServing` yet, so
today the axiom cannot be used at all. The grpc-go fact it rests on is true: `GracefulStop` returns only after
every method handler goroutine has returned. I read the code and a test confirms it (below).

The **docstring's argument for the post is wrong**, though. Two of etcd's handlers start a goroutine that
`GracefulStop` does not wait for, and the in-process proofs give each of those goroutines its own loan from the
same run pool. So the pool need not be full when `GracefulStop` returns, and `srvStopReaders E` does not follow
from the proofs the docstring cites. The post is still true of the Go program, but only with **auth off**:

- **Auth off.** After their handler has returned, those goroutines touch no backend state.
- **Auth on.** The watch `recvLoop` reads the auth store's backend after `HardStop` closes it. That is a nil
  bolt `Tx`, so a real panic.

The draft `serve_dist` (`notes/etcd-dist-restart-axioms.md` §2) gives `⌜E.authOn = false⌝ ∗ grpcServing gs E ∗ srvStopRight …` in its auth-on
arm as well, from `memberUpOnL`. But `memberUpOnL` holds no `srvStopRight` and has `E.authMode = .on γa`. Once
that arm exists, it is the open door to the auth-on panic. Fixes F1 to F3 close it. F4 and F5 only correct the
docstring.

## Answers

**Q1: does `GracefulStop` wait for every handler?** Yes, in both grpc-go v1.84.0 and the model.
`stop(true)` runs in this order (`server.go:1687-1733`; model `:1412-1445`):
1. `quit.Fire`;
2. close the listeners;
3. `serveWG.Wait`, which covers every `Serve` loop and every `handleRawConn`. Handshakes are therefore included:
   the `serveWG.Add` comes before `go handleRawConn` (`:990-994`);
4. drain every transport;
5. `for len(s.conns) != 0 { cv.Wait() }`, then `conns = nil`;
6. `if graceful || waitForHandlers { handlersWG.Wait() }`.

Point by point:
- **Handler accounting.** Every handler is counted. `handlersWG.Add(1)` runs on the transport's `serveStreams`
  goroutine, inside the `HandleStreams` callback, before `go f()`. It is also counted on the server-workers path
  (`:1090-1106`). `Done` is deferred around `handleStream`, which includes marshalling the reply and writing the
  status. Every `Add` happens before that transport's `removeConn`, and `stop` sees `conns` empty under `s.mu`.
  So all `Add`s happen before the `Wait`, and there is no WaitGroup-misuse panic.
- **Streams that never end** (watch, keep-alive). `GracefulStop` blocks until the client ends them. This is
  liveness only: the triple is vacuous on those executions. The "no long-lived streams" deployment class is
  **not** needed as a soundness precondition. Keep it as the liveness note it already is.
- **Handlers started after `GracefulStop` begins.** Streams that arrive on an existing connection between the
  GOAWAYs are dispatched and counted. Later ones are refused. Once `conns = nil`, `addConn` closes any new
  transport (`:1155-1174`), `Serve` returns `ErrServerStopped` (`:908-914`), and `ServeHTTP` is refused by
  `addConn` (the model panics `NotModelled` there).
- **Connections still in their handshake.** They delay `GracefulStop` by up to `ConnectionTimeout` (120 s by
  default), then they are either added and drained, or closed.
- **`ServerTransport` drain.** `Drain` sends GOAWAY. grpc-go's loopy writer closes the connection once the last
  stream ends (`controlbuf.go:839-841`). The model's drained connection instead reads until the client closes it
  (`model_transport.go:839-851`, `drainReads`). That only affects liveness for this axiom, because
  `GracefulStop`'s body is not translated. It is worth one line in the model's claim, though: in this case the
  model has fewer terminating runs than grpc-go.
- **`WaitForHandlers`.** It defaults to false (`server.go:645-658`) and only affects `Stop`. The graceful branch
  waits regardless. etcd's `v3rpc.Server` and `etcdstart.Serve` do not set it.

**Q2: is `srvStopReaders E` justified?** Not by the docstring's argument.
- **The watch receive loop.** `watchServer.Watch` waits for `sendLoop` (`sws.wg`) but not for `recvLoop`. etcd's
  own comment explains why (`watch.go:197-210`). The proof gives `recvLoop` a level-3 run-pool loan
  (`mvccReaders W.γm 1 ∗ F₃`) taken with its own fork token, and it gives the loan back "when the loop returns"
  (`watchServer__Watch.lean:229-241`), not when the handler returns.
- **The lease keep-alive loop.** `LeaseServer.LeaseKeepAlive` returns on the stream context's `Done` and leaves
  `leaseKeepAlive` running (`lease.go:95-108`). Its spec says so: "the goroutine then keeps running, with
  `S' ∗ A.revR`", and `S'` includes `srvReadReader s γr`, which is part of a run-pool element.
- **Only those two.** They are the only forks among the v3rpc handler proofs: grep for `wp_fork*` finds only
  `watchServer__Watch.lean` and `LeaseServer__LeaseKeepAlive.lean`.

Test T4 confirms in grpc-go that `GracefulStop` returns while a goroutine a handler started is still running.

What makes the post true of Go anyway, at auth off: after its handler has returned,
- `recvLoop` calls only
  - `watchStream.Rev()` (the in-memory revision),
  - `watchStream.Watch` (it returns early at `ws.closed`, because `sws.close()` closed the stream before the
    handler returned),
  - `isWatchPermitted` (`AuthInfoFromCtx` and `isOpPermitted` both return at `IsAuthEnabled()`);
- `leaseKeepAlive` calls only
  - `LeaseRenew`: `ensureLeadership` over `readMu`, channels and `s.done`; the lessor's in-memory
    `Lookup`/`Renew`; a checkpoint proposal that fails once raft stops;
  - `Send`/`Recv` on the finished stream, which return errors.

Neither reads the backend that the stop closes with these readers. With auth on, `isWatchPermitted` goes through
`isOpPermitted` to `as.lockedReadTx()` and `tx.UnsafeGetUser` (`auth/store.go:864-885`). That is a backend read,
and after `Close` it hits a reset `readTx` (nil bolt `Tx`).

Other things the handlers held are handed back correctly:
- reply messages are marshalled before `handlersWG.Done`;
- grpc's own buffers and its loopy writer touch no program resources;
- the stats handler's `ConnEnd` runs before `removeConn`.

**Q3: a panicking program with a no-panic proof?** None found.
- **Double `GracefulStop`.** It needs two `grpcServing gs E`, and nothing duplicates it. In Go, a second call is
  harmless anyway (T6).
- **`GracefulStop` concurrent with `Stop`, or with `Serve`.** No panic in grpc-go (T6). `Serve`'s spec has post
  `True`, so no false fact is available to exploit.
- **`Serve` on a stopped server.** Returns `ErrServerStopped`, no panic. `etcdstart.Serve` ignores the error
  (`go gs.Serve(l)`).
- **A handler that outlives `GracefulStop`.** Impossible (Q1).
- **A goroutine a handler started that outlives it.** Possible (T4). That is Q2's gap, safe at auth off and a
  panic at auth on.
- **`GracefulStop` blocking forever.** This happens with an open stream, an idle client in the model, or a slow
  handshake until the timeout. The triple is then vacuous on those runs, which is fine.

**Q4: is `grpcServing` exclusive, and where does it come from?** It is a Lean `opaque` with no instances and no
laws. Nothing persistent, splittable or duplicable is stated about it, so it cannot be copied. No
`grpcServing gs E ∗ grpcServing gs E ⊢ False` is stated either, but soundness does not need one as long as one
producer makes it once per `gs`. Its only producer is the draft `serve_dist`, which exists only as text in
`notes/etcd-dist-restart-axioms.md` §2. Nothing in the tree produces it, so today the axiom is unusable.
- **Arm without auth.** `serve_dist` consumes `memberUpL` whole, including `srvServeStock`'s `srvRevokePoolN`
  readers. That matches what `GracefulStop` returns (`srvStopReaders_intro` and `memberUp_stop` read the same
  stock). `serve` makes a fresh `gs` each call, and `memberUpL` is consumed, so there is one `grpcServing` per
  `gs`.
- **Auth arm.** This is F3: it gives a `srvStopRight` that `memberUpOnL` does not contain, together with
  `⌜E.authOn = false⌝`, while `memberUpOnL` has `E.authMode = .on γa`.

**Q5: route over the grpc model.** Proving it there needs the model's `stop`, `serveStreams` and `handleRawConn`
bodies translated (`GracefulStop` is a name only today). It also needs `Serve`'s axiom (today it consumes
`grpcServeTok` and has post `True`) restated to leave a drain token with:
- an invariant over `s.mu`'s `conns`/`drain`, `serveWG` and `handlersWG` (Perennial's WaitGroup specs), whose
  per-handler slot holds that handler's run-pool loan;
- a cancelable run pool.

Even then the proof fails until the Watch and LeaseKeepAlive proofs leave no run-pool loan alive past their
handler (Q2). That takes either an in-process accounting change or an etcd change. The HardStop header is right
that there is no `Stop`/`GracefulStop` spec today. `SpecPlan/.../Server__GracefulStop.lean`'s `drainTok` plan
has the same gap.

## Scenarios tried (a Go test outside the repository, not committed)

The test runs against grpc-go v1.84.0, Go 1.27.3, with `-race -count=3`. It uses the health service as a generic
service, with a blocking unary `Check` and a never-ending streaming `Watch`. All passes are stable across the
three runs.

| # | Scenario | Result |
|---|---|---|
| T1 | `GracefulStop` while a unary handler is blocked | still blocked after 500 ms; returns only after the handler returned |
| T2 | never-ending server stream | `GracefulStop` still blocked after 1.5 s; returns after the client cancels; the handler returned first |
| T3 | 8 unary calls issued on the open connection right after `GracefulStop` starts, 200 rounds | about 1500 dispatched after the start; every handler returned before `GracefulStop` did; the rest refused |
| T4 | the handler starts a 500 ms goroutine and returns | **`GracefulStop` returns while the goroutine is still running** (Q2's gap, in grpc-go) |
| T5 | raw TCP connection that sends no preface, `ConnectionTimeout(1s)` | `GracefulStop` takes about 0.9 s (handshake under `serveWG`) |
| T6 | 4× (`GracefulStop` ∥ `Stop`), then `GracefulStop` again, then `Serve` after stop; 200× `Serve` racing `GracefulStop` | no panic; `Serve` returns `ErrServerStopped` or `nil` |

Logic-level attacks, all blocked:
- duplicating `grpcServing`: no law;
- a cross-world entailment: nothing persistent;
- `Serve`'s post being exploitable: it is `True`;
- a missing `isPkgInit` premise: Go runs grpc's package init before `main`.

## Fixes (exact wording)

**F1, the axiom's docstring.** In "Why it is true", replace from "Each handler's run contract" to "holds
`srvStopReaders E`." with:

> `GracefulStop` waits for the handler goroutines, not for goroutines a handler started. Two of etcd's handlers
> start one that can outlive them: `watchServer.Watch`'s `recvLoop` (not in `sws.wg`, etcd `watch.go:197-210`) and
> `LeaseServer.LeaseKeepAlive`'s `leaseKeepAlive` (left running when the stream's context is done, `lease.go:95-108`).
> The in-process proofs give each its own loan of the run pool, taken with its own thread token
> (`watchServer__Watch.lean:229-241`; `LeaseServer.LeaseKeepAlive.spec`: "the goroutine then keeps running, with
> `S' ∗ A.revR`"), so the run pool need not be full when `GracefulStop` returns: the post is not derived from those
> proofs. It is true of the Go program at auth off (the premise `E.authOn = false`): after its handler returned,
> `recvLoop` calls only `watchStream.Rev` (the store's in-memory revision), `watchStream.Watch` on the closed watch
> stream (it returns at `ws.closed`) and `isWatchPermitted` (it returns at `IsAuthEnabled()`), and `leaseKeepAlive`
> only `LeaseRenew` (the leadership check over `readMu` and channels, the lessor's in-memory `Lookup`/`Renew`, a
> checkpoint proposal that fails once raft stops) and `Send`/`Recv` on the finished stream; none reads the backend
> `HardStop` closes with these readers. With auth on the post would be false: `isWatchPermitted` reads the auth
> store's backend (`isOpPermitted`'s `lockedReadTx`, `auth/store.go:882-885`) after `Close`.

**F2, the spec: add the auth-off premise.** It weakens the axiom and costs the stopper nothing, since
`serve_dist`'s post already gives it.

```lean
abbrev GracefulStop_dist.spec : Prop :=
  ∀ (gs : Loc) (E : apply.AEnv GF),
  {{ grpcServing gs E ∗ ⌜E.authOn = false⌝ }}
    (App (Val (gs @!! go.GoType.PointerType google_golang_org.grpc.Server.ty @!! go!"GracefulStop")) (Val #()))
  {{ RET #(); srvStopReaders E }}
```

Header bullet: "`GracefulStop_dist.spec`: from `grpcServing gs E` at auth off (`E.authOn = false`, on which the
post's truth rests: the axiom's docstring), `GracefulStop` returns with …".

**F3, the `serve_dist` draft (`notes/etcd-dist-restart-axioms.md` §2): no stop rights in the auth arm.** Replace the success disjunct with:

```lean
      ⌜err = GoInterface.nil⌝ ∗ (if Γ.auth then True else ∃ (E : apply.AEnv GF) (dd : GoString),
        ⌜E.authOn = false ∧ E.cmp = E₀.cmp⌝ ∗ grpcServing gs E ∗ srvStopRight s E ρ.rd.raft.raft ρ mid dd) }}
```

Add to its contract: "`grpcServing gs E` is made only here, once per `gs` (`serve` makes a fresh one), from the
serving stocks `memberUpL` holds (`srvServeStock`'s `srvRevokePoolN` store readers): the readers
`GracefulStop_dist` gives back. `memberUpOnL` holds no `srvStopRight` and has auth on, so the auth arm gives no
stop right."

**F4, the axiom's docstring: the grpc-go argument, made precise.** Replace "No `Add` can follow the wait: once
the connections are gone no transport delivers a stream." with:

> Every `Add` runs on a transport's `serveStreams` goroutine before that transport's `removeConn`, and `stop` sets
> `conns = nil` under `s.mu` after the last `removeConn`, so a later transport is refused (`addConn`) and the
> `Add`s happen before the `Wait`. The same holds in grpc-go v1.84.0 itself (`server.go:1071-1106`, `:1155-1174`,
> `:1687-1733`; its server-workers path counts the handler too); connections still in their handshake are under
> `serveWG` (`:990-994`), waited for before the drain. `WaitForHandlers` (default false) only matters to `Stop`.

**F5, the axiom's docstring: retirement.** Replace "**Retired by** phase 7's grpc proof: …" with:

> **Retired by** phase 7's grpc proof (`GracefulStop` over the grpc model, `drainTok`), once the Watch and
> LeaseKeepAlive proofs leave no run-pool loan alive after their handler returns (or etcd waits for those
> goroutines): as the proofs stand, the run pool is not provably full at `GracefulStop`'s return.

Keep the liveness note as it is. The no-long-lived-stream class is not a soundness precondition. It does happen
to keep the F1 goroutines from arising, but remote clients are not bound by the axiom, so F1 must not rely on it.

## Not tried
- A Lean counterexample. None was warranted: no producer of `grpcServing` exists, and no Go panic was found in
  scope.
- An exhaustive audit of every unary handler for goroutines that outlive it. The proof-side grep finds only the
  two forks above. etcd's `monitorLeader` is a `GoAttach` goroutine, which `HardStop` waits for.
- A Go-level reproduction of the auth-on panic through the real etcd member.

## Applied (2026-11-26, branch `etcd-safe-crash-b4/2026-11-26`)

F1 to F5 are applied as worded above:
- F1, F4 and F5 in the axiom's docstring (`Proof/.../etcd/dist/GracefulStopDist.lean`);
- F2 in the spec and its header bullet (`Spec/.../etcd/dist/GracefulStopDist.lean`);
- F3 in `serve_dist`'s draft text (`notes/etcd-dist-restart-axioms.md` §2).
