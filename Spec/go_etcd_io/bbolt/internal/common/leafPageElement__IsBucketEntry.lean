/-
`(*leafPageElement).IsBucketEntry`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `n.IsBucketEntry()`: the element is a nested bucket (its `BucketLeafFlag` bit, `1`, is set). -/
abbrev leafPageElement.IsBucketEntry.spec : Prop :=
  ∀ (l : Loc) (v : leafPageElement) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType leafPageElement.ty @!! go!"IsBucketEntry")) (Val #()))
  {{ RET #(decide (v.flags' &&& W32 1 ≠ W32 0)); l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
