module
public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageCount

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `p.FreelistPageIds()`: the ids of a freelist page, as a slice of `Pgid`s over the page
(`nil` if there are none). -/
abbrev Page.FreelistPageIds.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac) (c : w64),
  l.locCar ≠ 0 → v.flags' = W16 16 → (fpOverflow v → 0 ≤ sint.Z c) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗ fpCountCell l v dq c }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"FreelistPageIds")) (Val #()))
  {{ RET #(if fpCount v c = W64 0 then slice.nil
           else slice.mk (l +ₗ (16 + 8 * uint.Z (fpIdx v))) (fpCount v c) (fpCount v c));
      l ↦{dq} v ∗ fpCountCell l v dq c }}

end spec

end bbolt
end EtcdGrove
end Perennial
