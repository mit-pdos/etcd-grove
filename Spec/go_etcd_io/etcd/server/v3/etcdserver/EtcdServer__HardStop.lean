/-
`s.HardStop()` (`server/etcdserver/server.go`; the restart plan's R2a, 2026-11-02): stop the
server without a leadership transfer. It signals `run` to stop and waits for `run`'s deferred
shutdown: the scheduler stopped, the server's goroutines waited for (`s.wg`), the raft node and the
transport stopped (`raftNode.stop`), `Cleanup` (the lessor, the KV store, the auth store, the
backend and the compactor closed), `done` closed. Lean-first (no Rocq counterpart).

**The triple (DRAFT):** from the right to stop the server (`srvStopRight`, which `NewServer` gives,
R2b) once it was started (its request view `isServerReq`, which `Start` returns: a `HardStop` of a
server never started blocks forever, sending on `s.stop`, which only `run` receives; R2b checks that
only `Start` gives it), `HardStop` returns with member `id`'s data directory as it left it (`srvDiskImage`,
R2c), from which the member can be started again. The server's other resources are not given back:
the next incarnation has its own, and goroutines of this one may still hold some (an `http.Serve`
handler in flight).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev EtcdServer.HardStop.spec : Prop :=
  ∀ (s : Loc) (γ : SrvRaft) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvStopRight s γ id ∗ (∃ (E : apply.AEnv GF) (ρ : ReqNames), isServerReq s E ρ) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"HardStop")) (Val #()))
  {{ RET #(); srvDiskImage γ id }}

end spec

end EtcdGrove
end Perennial
