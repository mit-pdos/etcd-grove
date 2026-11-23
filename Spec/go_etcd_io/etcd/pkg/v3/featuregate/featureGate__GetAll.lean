/-
`(*featureGate).GetAll()` (`pkg/featuregate/feature_gate.go`), on a read-only gate (`isGate`, from
any thread): a fresh map, owned by the caller, holding the registered features `K` (`known`'s map,
copied with `maps.Copy`). Lean-first (featuregate-4, 2026-11-23: the server's
`addFeatureGateMetrics` ranges over it).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev featuregate.featureGate.GetAll.spec : Prop :=
  ∀ (p : Loc) (K : GMap GoString _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (E : GMap GoString Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate ∗
      featuregate.isGate p K E }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty
      @!! go!"GetAll")) (Val #()))
  {{ (m : Loc), RET #m; m ↦$ K }}

end spec

end EtcdGrove
end Perennial
