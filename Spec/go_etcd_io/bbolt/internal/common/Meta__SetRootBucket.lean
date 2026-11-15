/-
`(*Meta).SetRootBucket`'s spec (`internal/common/meta.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `Meta.SetRootBucket(x)` writes the field `root`. -/
abbrev Meta.SetRootBucket.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (x : InBucket),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"SetRootBucket")) (Val #x))
  {{ RET #(); l ↦ ({ v with root' := x } : Meta) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
