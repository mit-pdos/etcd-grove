module
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage

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

/-- A freelist page's count: its header's, or, if that is `0xFFFF` (the overflow marker), the
`Pgid` after the header (`c`), the ids then starting one element later. -/
def fpOverflow (v : Page) : Prop := v.count' = W16 65535

instance (v : Page) : Decidable (fpOverflow v) := by unfold fpOverflow; infer_instance

/-- The index of a freelist page's first id. -/
def fpIdx (v : Page) : w64 := if fpOverflow v then W64 1 else W64 0

/-- The number of ids on a freelist page. -/
def fpCount (v : Page) (c : w64) : w64 := if fpOverflow v then c else W64 (uint.Z v.count')

/-- The `Pgid` after an overflowing freelist page's header (`True` otherwise). -/
def fpCountCell (l : Loc) (v : Page) (dq : DFrac) (c : w64) : IProp GF :=
  if fpOverflow v then (l +ₗ 16) ↦{dq} c else iprop(True)

/-- `p.FreelistPageCount()`: the index of the first id and the number of ids of a freelist
page (it panics on another page, or on a negative overflow count). -/
abbrev Page.FreelistPageCount.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac) (c : w64),
  v.flags' = W16 16 → (fpOverflow v → 0 ≤ sint.Z c) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗ fpCountCell l v dq c }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"FreelistPageCount")) (Val #()))
  {{ RET (PairV #(fpIdx v) #(fpCount v c)); l ↦{dq} v ∗ fpCountCell l v dq c }}

end spec

end bbolt
end EtcdGrove
end Perennial
