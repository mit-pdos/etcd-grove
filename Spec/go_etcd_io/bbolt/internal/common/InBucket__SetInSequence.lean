/-
`(*InBucket).SetInSequence`'s spec (`internal/common/bucket.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `InBucket.SetInSequence(x)` writes the field `sequence`. -/
abbrev InBucket.SetInSequence.spec : Prop :=
  ∀ (l : Loc) (v : InBucket) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType InBucket.ty @!! go!"SetInSequence")) (Val #x))
  {{ RET #(); l ↦ ({ v with sequence' := x } : InBucket) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
