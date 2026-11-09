/-
`metadata.MD.Set(k, vals...)` (grpc-go, assumed: `metadata/metadata.go`).

Users: the client's `WithRequireLeader` (1c).

Why true: no-op with no values; else it lowercases the key and stores the slice (the caller's,
read-only afterwards).

Changes: new.

Margin: stated for at least one value (etcd sets one).
-/
module

public import Spec.google_golang_org.grpc.Api

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

/-- `md.Set(k, vs...)` on an owned map, with at least one value: the key's values replaced. -/
def MD.Set.spec : Prop :=
  ∀ (m : Loc) (md : MD) (k : GoString) (sl : GoSlice) (vs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ mdAt m (DFrac.own 1) md ∗ sl ↦*□ vs ∗ ⌜vs ≠ []⌝ }}
    (App (App (Val (m @!! google_golang_org.grpc.metadata.MD.ty @!! go!"Set")) (Val #k)) (Val #sl))
  {{ RET #(); mdAt m (DFrac.own 1) (MD.set md k vs) }}

end spec

end Grpc
end EtcdGrove
end Perennial
