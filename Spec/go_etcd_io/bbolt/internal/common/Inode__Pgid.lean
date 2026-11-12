/-
`(*Inode).Pgid`'s spec (`internal/common/inode.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `Inode.Pgid()` reads the field `pgid`. -/
abbrev Inode.Pgid.spec : Prop :=
  ∀ (l : Loc) (v : Inode) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Inode.ty @!! go!"Pgid")) (Val #()))
  {{ RET #(v.pgid'); l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
