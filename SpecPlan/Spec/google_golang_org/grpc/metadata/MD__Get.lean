/-
`metadata.MD.Get(k)` (grpc-go, assumed: `metadata/metadata.go`).

Users: `v3rpc.newUnaryInterceptor`, `newStreamInterceptor` (the client API version key).

Why true: it lowercases the key and returns the map's slice for it (shared, read-only by
convention: the interceptors only read it).

Changes: new.
Re-review (R-A6 N1): also of a `nil` map (`mdAtN true`: a lookup in a `nil` map gives `nil`, `md.get` of `[]` is `[]`).

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

/-- `md.Get(k)`: the key's values (a read-only slice). -/
def MD.Get.spec : Prop :=
  ∀ (b : Bool) (m : Loc) (dq : DFrac) (md : MD) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ mdAtN b m dq md }}
    (App (Val (m @!! google_golang_org.grpc.metadata.MD.ty @!! go!"Get")) (Val #k))
  {{ (sl : GoSlice), RET #sl; mdAtN b m dq md ∗ sl ↦*□ md.get (lowerKey k) }}

end spec

end Grpc
end EtcdGrove
end Perennial
