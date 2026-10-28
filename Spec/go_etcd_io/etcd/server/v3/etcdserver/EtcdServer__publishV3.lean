/-
`(*EtcdServer).publishV3(timeout)` (`server.go`): names-only, one of the goroutines `Start` attaches. Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MonitorsOn

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

/-- `s.publishV3(timeout)` returns (names-only: it publishes the member's attributes through raft
until it succeeds or `stopping` is closed). It proposes, through `s.raftRequest`, only
`ClusterMemberAttrSet` requests (`server.go`: `req := pb.InternalRaftRequest{ClusterMemberAttrSet:
…}`), with the permission `srvMonitorPermitM` gives (in either auth mode, `MonitorsOn.lean`, E3zb) (D19c, 2026-10-18, `InvMonitors.lean`; until
then the contract took only the package's initialization, and its proposals were outside the
model). On success it closes `s.readych` (`close(s.readych)`), with the right to (`srvReadyCloser`,
2026-10-23: until then the contract closed a channel it did not own). -/
abbrev EtcdServer.publishV3.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (d : _root_.Perennial.time.Duration) (E : apply.AEnv GF) (ρ : ReqNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMonitorPermitM on s E ρ ∗ srvReadyCloser s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"publishV3")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
