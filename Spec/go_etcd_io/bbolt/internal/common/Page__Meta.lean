/-
`(*Page).Meta`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `p.Meta()`: the address 16 bytes past `p`, after the page header, where a meta page keeps its
`Meta` (`UnsafeAdd`). Pure in the address. -/
abbrev Page.Meta.spec : Prop :=
  ∀ (l : Loc),
  0 < l.addr → l.addr + 16 ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"Meta")) (Val #()))
  {{ RET #(l +ₗ 16); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
