/-
## `(*EtcdServer).HardStop()` (`server.go:1339-1346`)

**Users.** `examples/etcd/restart`'s `stop` (then the member's peer listener closed, and the
member started again on its directory); `Stop`; etcd's tests. Snippets: `etcdserverboot/boot.go`
(`ReqRestart`, `ReqStopAfterError`: `run` already returned on a transport error; `ReqStopDrained`:
a request racing the stop, the gate).

**Proof sketch.** `srvRunning` holds the right to send on `s.stop` (unbuffered: `run`'s loop
receives it) and the escrow of `s.done`. The `select`: either the send succeeds (`run` returns, its
deferred stop runs: `stopping` closed, the context cancelled, the scheduler stopped, the attached
goroutines waited for, the raft node stopped with its WAL closed (`ServerStorage.storage.Close`),
`Cleanup`, `close(s.done)` with `memberDisk γ id ds` deposited: 2d's `run`), or `s.done` is already
closed (`run` returned on a server error, `errorc`). Then `<-s.done` takes the deposit with the
escrow's token.

**Changes** (from `specs-ref`'s `EtcdServer__HardStop.lean`: `srvStopRight`, `srvStopReq` to
`srvDiskImage γ ρ id dd`): the image is `memberDisk`, which every start takes (`memberStart_restart`),
in place of the R2d'a restart contract's premises.

**Round 1 (completeness F2).** The whole gate is a premise: no request in flight. `Cleanup` closes
the backend while a serializable `Range` may still read it
(`issues/etcd-read-after-backend-close-panic.md`); the gate's shares are the request path's (2c's
specs hold one per call), so a program stops a member only after draining its gRPC server (or
serving none). The alternative, a gate in the Go code, is open (`batch-2e.md` Q7).

**Margin.** A second `HardStop` returns at once in Go; the spec takes the one stop right.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Stops the running server `s`** and waits for its stop: the member's directories hold its
durable state. -/
def EtcdServer.HardStop.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (ds : Config.Dirs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvRunning s γ id ds ∗ srvGate s 1 }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"HardStop")) (Val #()))
  {{ RET #(); memberDisk γ id ds }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
