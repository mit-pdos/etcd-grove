module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The key, value and flags `keyValue` returns for leaf element `i` of the page at `p`
with bytes `pg` (nil, nil, 0 past the end). -/
def kvResult (p : Loc) (pg : List w8) (i : Int) : GoSlice × GoSlice × w32 :=
  if pageCount pg = 0 ∨ (pageCount pg : Int) ≤ i then (slice.nil, slice.nil, W32 0)
  else
    let e := elemOff i.toNat
    (slice.mk (p +ₗ ((e + leafPos pg i.toNat : Nat) : Int)) (W64 (leafKsize pg i.toNat))
        (W64 (leafKsize pg i.toNat)),
     slice.mk (p +ₗ ((e + leafPos pg i.toNat + leafKsize pg i.toNat : Nat) : Int))
        (W64 (leafVsize pg i.toNat)) (W64 (leafVsize pg i.toNat)),
     W32 (leafFlags pg i.toNat))

/-- `c.keyValue()` with the top of the stack a reference to a leaf page (the read path): the
key and value (slices into the page) and flags of its current element, or nil past the end.
(An index below 0 only arises on an empty page: `last` on an empty leaf.) -/
abbrev Cursor.keyValue.spec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (dqc : DFrac) (es : List elemRef) (dqs : DFrac) (rv : elemRef)
    (q : DFrac) (pg : List w8),
  es.getLast? = some rv → rv.node' = null → rv.page'.locCar ≠ 0 → 16 ≤ pg.length →
  pageFlags pg = leafPageFlag → leafWF pg pg.length →
  (0 ≤ sint.Z rv.index' ∨ pageCount pg = 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦{dqc} cv ∗ cv.stack' ↦*{dqs} es ∗ bytesPointsto rv.page' q pg }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ RET (PairV (PairV #(kvResult rv.page' pg (sint.Z rv.index')).1
        #(kvResult rv.page' pg (sint.Z rv.index')).2.1) #(kvResult rv.page' pg (sint.Z rv.index')).2.2);
      cl ↦{dqc} cv ∗ cv.stack' ↦*{dqs} es ∗ bytesPointsto rv.page' q pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
