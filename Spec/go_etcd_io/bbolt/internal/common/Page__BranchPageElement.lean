/-
`(*Page).BranchPageElement`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `p.BranchPageElement(i)`: the address of element `i` of a branch page, `16 + 16 i` bytes past `p` (16-byte
elements after the 16-byte header; `UnsafeIndex`). Pure in the address: it reads nothing. The
address must lie in the address space (`unsafe.Add`). -/
abbrev Page.BranchPageElement.spec : Prop :=
  ∀ (l : Loc) (i : w16),
  0 < l.addr → l.addr + 16 + 16 * uint.Z i ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"BranchPageElement")) (Val #i))
  {{ RET #(l +ₗ (16 + 16 * uint.Z i)); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
