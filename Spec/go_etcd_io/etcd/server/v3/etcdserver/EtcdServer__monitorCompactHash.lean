/-
`(*EtcdServer).monitorCompactHash()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
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

/-- `s.monitorCompactHash()` returns (names-only: the compaction hash check's monitor, until
`stopping`), **with the check off** (the feature gate `s.Cfg.ServerFeatureGate` answering `false`
for `CompactHashCheck`, its default): `s.FeatureEnabled(features.CompactHashCheck)` is false and
it returns at once. Once enabled the leader reads the store's hashes and may propose
`Alarm{CORRUPT}`, which the KV model does not admit (audit B4a, 2026-10-18, D19m; until then the
contract took only the package's initialization). -/
abbrev EtcdServer.monitorCompactHash.spec : Prop :=
  ∀ (s : Loc) (fg : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ featureIs fg go!"CompactHashCheck" false }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"monitorCompactHash")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
