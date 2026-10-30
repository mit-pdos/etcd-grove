module
public import Spec.go_etcd_io.bbolt.Cursor__nsearch_w
public import Proof.go_etcd_io.bbolt.ShapeRoute

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

/-- `c.nsearch(key)` (`Cursor.nsearch.wspec`), with a page's index: where `key` goes among the
leaf page's keys (`keysIdx`). -/
abbrev Cursor.nsearch.sspec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (dqc : DFrac) (es : List elemRef) (rv : elemRef) (q : DFrac)
    (pg : List w8) (nv : node) (dqn : DFrac) (ins : List internal.common.Inode) (dqs : DFrac)
    (ens : List NodeEntry) (key : GoSlice) (kb : List w8) (dk : DFrac),
  es.getLast? = some rv →
  (rv.node' = null → rv.page'.locCar ≠ 0 ∧ 16 ≤ pg.length ∧ pageFlags pg = leafPageFlag ∧
    leafWF pg pg.length) →
  (rv.node' ≠ null → entriesSorted ens) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦{dqc} cv ∗ cv.stack' ↦* es ∗
      leafRes rv q pg nv dqn ins dqs ens ∗ key ↦*{dk} kb }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ (idx : w64), RET #();
      ⌜0 ≤ sint.Z idx ∧ (rv.node' = null → sint.Z idx ≤ pageCount pg) ∧
        (rv.node' ≠ null → isSearchIdx ens kb (sint.nat idx)) ∧
        (rv.node' = null → keysIdx ((List.range (pageCount pg)).map (leafKey pg)) kb
          (sint.Z idx).toNat)⌝ ∗
      cl ↦{dqc} cv ∗ cv.stack' ↦* es.set (es.length - 1) { rv with index' := idx } ∗
      leafRes rv q pg nv dqn ins dqs ens ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
