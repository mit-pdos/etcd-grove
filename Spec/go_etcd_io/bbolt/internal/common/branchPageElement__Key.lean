/-
`(*branchPageElement).Key`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `n.Key()`: the element's key as a byte slice into its page, the `ksize` bytes `pos` bytes past
the element (`UnsafeByteSlice`; length and capacity `ksize`). For element `i` of the branch page
`pg` at `p` this is `keySliceAt p pg i`. The slice must lie in the address space. -/
abbrev branchPageElement.Key.spec : Prop :=
  ∀ (l : Loc) (v : branchPageElement) (dq : DFrac),
  0 < l.addr → l.addr + uint.Z v.pos' + uint.Z v.ksize' ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType branchPageElement.ty @!! go!"Key")) (Val #()))
  {{ RET #(slice.mk (l +ₗ uint.Z v.pos') (W64 (uint.Z v.ksize')) (W64 (uint.Z v.ksize')));
      l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
