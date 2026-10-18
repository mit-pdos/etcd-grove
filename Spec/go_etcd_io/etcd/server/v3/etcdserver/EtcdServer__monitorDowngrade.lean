/-
`(*EtcdServer).monitorDowngrade()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvMonitors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.monitorDowngrade()` returns (names-only: the downgrade monitor, until `stopping`), **with
the check off** (`s.Cfg.DowngradeCheckTime` zero, read-only): it builds its monitor
(`serverversion.NewMonitor(s.Logger(), NewServerVersionAdapter(s))`: a reader slot of `s.lgMu`
and the logger field), reads the interval and returns at once. Once configured the leader may
propose `DowngradeInfoSet` (`CancelDowngradeIfNeeded`), which no permit covers (audit B4a,
2026-10-18, D19m; until then the contract took only the package's initialization). -/
abbrev EtcdServer.monitorDowngrade.spec : Prop :=
  ∀ (s l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ l ∗ srvLgReader s ∗
      srvCfgFieldAddr s go!"DowngradeCheckTime" ↦□ (W64 0) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"monitorDowngrade")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
