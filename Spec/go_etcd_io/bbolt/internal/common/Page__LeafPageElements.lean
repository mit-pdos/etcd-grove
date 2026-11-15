/-
`(*Page).LeafPageElements`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `p.LeafPageElements()`: the page's `count` elements, as a `[]leafPageElement` over the page after its
header (16 bytes each; `unsafe.Slice`); `nil` if there are none. It reads only the header's
`count`. -/
abbrev Page.LeafPageElements.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  0 < l.addr → l.addr + 16 + 16 * uint.Z v.count' ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"LeafPageElements")) (Val #()))
  {{ RET #(if v.count' = W16 0 then slice.nil
           else slice.mk (l +ₗ 16) (W64 (uint.Z v.count')) (W64 (uint.Z v.count')));
      l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
