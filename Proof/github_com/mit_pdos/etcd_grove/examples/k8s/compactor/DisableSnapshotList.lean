/-
`DisableSnapshotList`'s proof: an axiom, the trust boundary of the feature gate (U3 of K2 in
`notes/k8s-compactor-plan.md`, the user's approval 2026-11-04).

**Why it is sound.** `DefaultMutableFeatureGate` and `DefaultFeatureGate` are one
`featuregate.featureGate` (`k8s.io/apiserver/pkg/util/feature/feature_gate.go`). `ListFromCacheSnapshot`
is registered in it by `k8s.io/apiserver/pkg/features`' `init` (beta, not locked to its default), so
`Set("ListFromCacheSnapshot=false")` records `false` for it and returns `nil`
(`component-base/featuregate/feature_gate.go`, `Set` and `SetFromMap`; the post also admits an
error). From then on `Enabled(ListFromCacheSnapshot)` returns the recorded value, `false`: no
verified code changes it again, since the gate's other mutators (`Set` with another string,
`SetFromMap`, `SetEmulationVersion`, `Add`, ...) have no spec, and this one only sets the same value.
`featureInit` (the init's axiom) says `Enabled` answers some `bool`, which `false` is.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.DisableSnapshotList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary: see the file header. -/
axiom DisableSnapshotList.wp_proof : DisableSnapshotList.spec (GF := GF) (hG := hG)

end proof

end k8s_compactor
end EtcdGrove
end Perennial
