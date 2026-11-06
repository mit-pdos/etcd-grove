/-
`(*branchPageElement).SetKsize`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `branchPageElement.SetKsize(x)` writes the field `ksize`. -/
abbrev branchPageElement.SetKsize.spec : Prop :=
  ∀ (l : Loc) (v : branchPageElement) (x : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType branchPageElement.ty @!! go!"SetKsize")) (Val #x))
  {{ RET #(); l ↦ ({ v with ksize' := x } : branchPageElement) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
