/-
`s.FeatureEnabled(f)` (`server.go`): the configuration's feature gate. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.FeatureEnabled(f)`: some boolean (the feature gate's contract, `isFeatureGate`). -/
abbrev EtcdServer.FeatureEnabled.spec : Prop :=
  ∀ (s : Loc) (fg : GoInterface) (f : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"FeatureEnabled")) (Val #f))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
