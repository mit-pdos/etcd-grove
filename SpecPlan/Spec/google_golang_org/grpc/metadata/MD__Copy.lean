/-
`metadata.MD.Copy()` (grpc-go, assumed: `metadata/metadata.go`).

Users: the client's `WithRequireLeader` (1c).

Why true: a fresh map with copies of the value slices.

Changes: new.
Re-review (R-A6 N1): also of a `nil` map (`mdAtN true`: `make(MD, 0)` then a loop over nothing), a fresh empty map.
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

/-- `md.Copy()`: a fresh map holding the same metadata. -/
def MD.Copy.spec : Prop :=
  ∀ (b : Bool) (m : Loc) (dq : DFrac) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ mdAtN b m dq md }}
    (App (Val (m @!! google_golang_org.grpc.metadata.MD.ty @!! go!"Copy")) (Val #()))
  {{ (m' : Loc), RET #m'; mdAtN b m dq md ∗ mdAt m' (DFrac.own 1) md ∗ ⌜m' ≠ null⌝ }}

end spec

end Grpc
end EtcdGrove
end Perennial
