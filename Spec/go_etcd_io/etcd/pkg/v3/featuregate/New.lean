/-
`featuregate.New(name, lg)` (`pkg/featuregate/feature_gate.go`): a fresh gate, owned by its caller,
its known features featuregate's own (`AllAlpha`, `AllBeta`: `maps.Clone(defaultFeatures)`), none set
(an empty `enabled` map), returned as a `MutableFeatureGate`. A nil `lg` is replaced by
`zap.NewNop()`; the gate's logger, name and `special` map are not in the spec (only `SetFromMap`,
`OverrideDefault` and `Enabled`'s panic read them, and none of them is specified). Lean-first
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
abbrev featuregate.New.spec : Prop :=
  ∀ (name : GoString) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate }}
    (App (App (Val (@! _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.New)) (Val #name))
      (Val #lg))
  {{ (p : Loc), RET #(interface.mkOk
        (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #p);
      ⌜p ≠ null⌝ ∗ featuregate.ownGate p featuregate.defaultKnown ∅ }}

end spec

end EtcdGrove
end Perennial
