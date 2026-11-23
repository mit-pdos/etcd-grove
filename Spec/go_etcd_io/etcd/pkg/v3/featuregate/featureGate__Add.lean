/-
`(*featureGate).Add(features)` (`pkg/featuregate/feature_gate.go`), on a gate its caller owns
(`ownGate`: `closed` false, the `Value`s whole), of features compatible with the registered ones
(`addCompat`: a feature already known has the same spec): the gate's known features become
`features` over them (`F ∪ K`; the two agree where both have a feature), and `Add` returns
`nil`. `features` is only read. (`Add` of a closed gate or of a conflicting spec returns an error;
not specified, as no verified caller does either.) Lean-first (featuregate-3, 2026-11-23).
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
abbrev featuregate.featureGate.Add.spec : Prop :=
  ∀ (p fm : Loc) (K F : GMap GoString _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (E : GMap GoString Bool) (dq : DFrac),
  featuregate.addCompat F K →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate ∗
      featuregate.ownGate p K E ∗ fm ↦${dq} F }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty
      @!! go!"Add")) (Val #fm))
  {{ RET #interface.nil; featuregate.ownGate p (F ∪ K) E ∗ fm ↦${dq} F }}

end spec

end EtcdGrove
end Perennial
