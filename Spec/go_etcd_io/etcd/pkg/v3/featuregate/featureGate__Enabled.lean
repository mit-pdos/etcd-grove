/-
`(*featureGate).Enabled(key)` (`pkg/featuregate/feature_gate.go`), on a read-only gate (`isGate`,
from any thread), of a feature set or registered (`Enabled` panics on a feature neither): the
feature's value, `enabled[key]` if set, else `known[key].Default` (`gateValue`). Lean-first
(featuregate-3, 2026-11-23).
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
abbrev featuregate.featureGate.Enabled.spec : Prop :=
  ∀ (p : Loc) (K : GMap GoString _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (E : GMap GoString Bool) (f : GoString),
  (E !! f).isSome ∨ (K !! f).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate ∗
      featuregate.isGate p K E }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty
      @!! go!"Enabled")) (Val #f))
  {{ RET #(featuregate.gateValue K E f); True }}

end spec

end EtcdGrove
end Perennial
