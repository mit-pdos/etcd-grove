/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached; reviewed 2026-11-26, SOUND WITH FIXES, applied: `notes/axiom-review/gracefulstop-dist.md`).** grpc-go's `(*Server).GracefulStop` on a member
machine: a trust-boundary axiom until phase 7's grpc proof (S2/S3).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.GracefulStopDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`gs.GracefulStop()` gives the serving stocks back** (DRAFT, trust boundary).

**Contract.** From the right to stop `gs` (`grpcServing gs E`, `serve_dist`'s post) at auth off, `GracefulStop` returns, and
then holds the store readers the member's serving stocks lent to `gs` (`srvStopReaders E`).

**Why it is true of grpc-go v1.84 (the model, `models/grpc/server.go:1405-1445`).** `GracefulStop` is
`s.stop(true)`: it fires `quit`, closes the listeners, waits for the `Serve` goroutines (`serveWG`), drains every
server transport (GOAWAY), waits until no connection is left (`for len(s.conns) != 0 { s.cv.Wait() }`), and then,
because `graceful` is true, waits for `s.handlersWG` (`if graceful || s.opts.waitForHandlers`), which counts every
method handler goroutine (`serveStreams`' `handlersWG.Add(1)` before `go handleStream`, `Done` when it returns,
`:1007-1011`). Every `Add` runs on a transport's `serveStreams` goroutine before that transport's `removeConn`, and `stop` sets
`conns = nil` under `s.mu` after the last `removeConn`, so a later transport is refused (`addConn`) and the
`Add`s happen before the `Wait`. The same holds in grpc-go v1.84.0 itself (`server.go:1071-1106`, `:1155-1174`,
`:1687-1733`; its server-workers path counts the handler too); connections still in their handshake are under
`serveWG` (`:990-994`), waited for before the drain. `WaitForHandlers` (default false) only matters to `Stop`. So when
`GracefulStop` returns, every handler `gs` started has returned. `GracefulStop` waits for the handler goroutines, not for goroutines a handler started. Two of etcd's handlers
start one that can outlive them: `watchServer.Watch`'s `recvLoop` (not in `sws.wg`, etcd `watch.go:197-210`) and
`LeaseServer.LeaseKeepAlive`'s `leaseKeepAlive` (left running when the stream's context is done, `lease.go:95-108`).
The in-process proofs give each its own loan of the run pool, taken with its own thread token
(`watchServer__Watch.lean:229-241`; `LeaseServer.LeaseKeepAlive.spec`: "the goroutine then keeps running, with
`S' ∗ A.revR`"), so the run pool need not be full when `GracefulStop` returns: the post is not derived from those
proofs. It is true of the Go program at auth off (the premise `E.authOn = false`): after its handler returned,
`recvLoop` calls only `watchStream.Rev` (the store's in-memory revision), `watchStream.Watch` on the closed watch
stream (it returns at `ws.closed`) and `isWatchPermitted` (it returns at `IsAuthEnabled()`), and `leaseKeepAlive`
only `LeaseRenew` (the leadership check over `readMu` and channels, the lessor's in-memory `Lookup`/`Renew`, a
checkpoint proposal that fails once raft stops) and `Send`/`Recv` on the finished stream; none reads the backend
`HardStop` closes with these readers. With auth on the post would be false: `isWatchPermitted` reads the auth
store's backend (`isOpPermitted`'s `lockedReadTx`, `auth/store.go:882-885`) after `Close`. `Stop` (`graceful = false`) without
`WaitForHandlers` would not wait for the handlers, and this axiom would be false of it.
**Liveness only:** `GracefulStop` blocks while a client keeps a stream open (a watch); partial correctness allows
it, and the restart workload's class has no long-lived stream (design §5 Q7).

**Retired by** phase 7's grpc proof (`GracefulStop` over the grpc model, `drainTok`), once the Watch and
LeaseKeepAlive proofs leave no run-pool loan alive after their handler returns (or etcd waits for those
goroutines): as the proofs stand, the run pool is not provably full at `GracefulStop`'s return.

**Route.** Translate: grpc-go is a trusted Go model (`models/grpc`, translated into `Code/google_golang_org/grpc`;
`GracefulStop` is in the method set, its body not translated). Go model: exists, in-process (S1), no
`GracefulStop` proof. Trusted code: none. Axiom: interim. -/
axiom GracefulStop_dist.wp_proof : GracefulStop_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
