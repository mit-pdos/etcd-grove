/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached, not reviewed).** grpc-go's `(*Server).GracefulStop` on a member
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

**Contract.** From the right to stop `gs` (`grpcServing gs E`, `serve_dist`'s post), `GracefulStop` returns, and
then holds the store readers the member's serving stocks lent to `gs` (`srvStopReaders E`).

**Why it is true of grpc-go v1.84 (the model, `models/grpc/server.go:1405-1445`).** `GracefulStop` is
`s.stop(true)`: it fires `quit`, closes the listeners, waits for the `Serve` goroutines (`serveWG`), drains every
server transport (GOAWAY), waits until no connection is left (`for len(s.conns) != 0 { s.cv.Wait() }`), and then,
because `graceful` is true, waits for `s.handlersWG` (`if graceful || s.opts.waitForHandlers`), which counts every
method handler goroutine (`serveStreams`' `handlersWG.Add(1)` before `go handleStream`, `Done` when it returns,
`:1007-1011`). No `Add` can follow the wait: once the connections are gone no transport delivers a stream. So when
`GracefulStop` returns, every handler `gs` started has returned. Each handler's run contract (`grpcRunOkMd`, proved
in-process for etcd's handlers) gives back the run's store reader when the handler returns (a goroutine a handler
starts, the watch server's `recvLoop`, holds none of the run's tokens after it: the handler's proof returns them),
so the run pool is full again and holds `srvStopReaders E`. `Stop` (`graceful = false`) without
`WaitForHandlers` would not wait for the handlers, and this axiom would be false of it.
**Liveness only:** `GracefulStop` blocks while a client keeps a stream open (a watch); partial correctness allows
it, and the restart workload's class has no long-lived stream (design §5 Q7).

**Retired by** phase 7's grpc proof: `GracefulStop` over the grpc model with the planned in-process spec
(`SpecPlan/Spec/google_golang_org/grpc/Server__GracefulStop.lean`, `drainTok`), across machines.

**Route.** Translate: grpc-go is a trusted Go model (`models/grpc`, translated into `Code/google_golang_org/grpc`;
`GracefulStop` is in the method set, its body not translated). Go model: exists, in-process (S1), no
`GracefulStop` proof. Trusted code: none. Axiom: interim. -/
axiom GracefulStop_dist.wp_proof : GracefulStop_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
