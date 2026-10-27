/-
`(*EtcdServer).monitorKVHash()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.monitorKVHash()` returns (names-only: the corruption check's periodic hash monitor, until
`stopping`), **with the check off** (`s.Cfg.CorruptCheckTime` zero, read-only): it reads the
interval and returns at once (`server.go`, `if t == 0 { return }`). Once configured it reads the
whole backend and may propose `Alarm{CORRUPT}`, which the KV model does not admit (audit B4a,
2026-10-18, D19m; until then the contract took only the package's initialization, false of a
configured check: `InvMonitors.lean`). -/
abbrev EtcdServer.monitorKVHash.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCfgFieldAddr s go!"CorruptCheckTime" ↦□ (W64 0) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"monitorKVHash")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
