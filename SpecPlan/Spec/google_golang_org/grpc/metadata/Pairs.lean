/-
`metadata.Pairs(kv...)` (grpc-go, assumed: `metadata/metadata.go`).

Users: the client's `withVersion` (1c), Kubernetes.

Why true: panics on an odd count (excluded); else a fresh map of the pairs, keys lowercased.

Changes: new.
verify-round (A6 F3): the result is non-`nil` (a `make`), what `MD.Set` now takes.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

/-- `metadata.Pairs(kv...)` with an even number of strings: a fresh map of them. -/
def Pairs.spec : Prop :=
  ∀ (sl : GoSlice) (kvs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ sl ↦*□ kvs ∗ ⌜kvs.length % 2 = 0⌝ }}
    (App (Val (@! google_golang_org.grpc.metadata.Pairs)) (Val #sl))
  {{ (m : Loc), RET #m; mdAt m (DFrac.own 1) (MD.ofPairs kvs) ∗ ⌜m ≠ null⌝ }}

end spec

end Grpc
end EtcdGrove
end Perennial
