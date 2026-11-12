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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.FeatureEnabled(f)` of a registered feature `f`: some boolean (the feature gate's
contract, `isFeatureGate`; a feature not registered panics); `b'` when the caller knows the gate
answers `b'` for `f` (`ob = some b'` with `featureIs fg f b'`; stage B3, 2026-11-12, for
`NewServer`'s `LeaseCheckpoint`). -/
abbrev EtcdServer.FeatureEnabled.spec : Prop :=
  ∀ (s : Loc) (fg : GoInterface) (f : GoString) (ob : Option Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗ ⌜f ∈ serverFeatures⌝ ∗
      (match ob with | some b' => featureIs fg f b' | none => emp) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"FeatureEnabled")) (Val #f))
  {{ (b : Bool), RET #b; ⌜∀ b', ob = some b' → b = b'⌝ }}

end spec

end EtcdGrove
end Perennial
