/-
`(*Inode).SetPgid`'s spec (`internal/common/inode.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `Inode.SetPgid(x)` writes the field `pgid`. -/
abbrev Inode.SetPgid.spec : Prop :=
  ∀ (l : Loc) (v : Inode) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Inode.ty @!! go!"SetPgid")) (Val #x))
  {{ RET #(); l ↦ ({ v with pgid' := x } : Inode) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
