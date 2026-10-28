/-
`(*EtcdServer).monitorClusterVersions()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
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

/-- `s.monitorClusterVersions()` returns (names-only: the leader's cluster version monitor, until
`stopping`). It proposes, through `s.updateClusterVersionV3` and `s.raftRequest`, only
`ClusterVersionSet` requests of a version it decided (`semver.Version.String()`, which parses
back: `semverValid`), with the permission `srvMonitorPermitM` gives (in either auth mode, `MonitorsOn.lean`, E3zb) (D19c, 2026-10-18,
`InvMonitors.lean`; until then the contract took only the package's initialization, and its
proposals were outside the model). -/
abbrev EtcdServer.monitorClusterVersions.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMonitorPermitM on s E ρ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"monitorClusterVersions")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
