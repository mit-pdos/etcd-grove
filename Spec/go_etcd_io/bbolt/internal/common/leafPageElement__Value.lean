/-
`(*leafPageElement).Value`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `n.Value()`: the element's value as a byte slice into its page, the `vsize` bytes after its key
(`pos + ksize` bytes past the element; length and capacity `vsize`). For element `i` of the leaf
page `pg` at `p` this is `valSliceAt p pg i`. The slice must lie in the address space. -/
abbrev leafPageElement.Value.spec : Prop :=
  ∀ (l : Loc) (v : leafPageElement) (dq : DFrac),
  0 < l.addr → l.addr + uint.Z v.pos' + uint.Z v.ksize' + uint.Z v.vsize' ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType leafPageElement.ty @!! go!"Value")) (Val #()))
  {{ RET #(slice.mk (l +ₗ (uint.Z v.pos' + uint.Z v.ksize')) (W64 (uint.Z v.vsize'))
             (W64 (uint.Z v.vsize')));
      l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
