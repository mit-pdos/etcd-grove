module
public import Proof.go_etcd_io.bbolt.NodeModel
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.Cursor__nsearch

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

/-- The leaf `nsearch` searches: the top element's node (its inodes `ins`, entries `ens`), or
its page `pg`. -/
def leafRes (rv : elemRef) (q : DFrac) (pg : List w8) (nv : node) (dqn : DFrac)
    (ins : List internal.common.Inode) (dqs : DFrac) (ens : List NodeEntry) : IProp GF :=
  if rv.node' = null then bytesPointsto rv.page' q pg
  else iprop(rv.node' ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodesOwn ins ens)

/-- `c.nsearch(key)` of a writer's cursor: the top element (a leaf node or a leaf page) gets the
index where `key` goes (`isSearchIdx` of the node's entries; for a page, as
`Cursor.nsearch.spec`). -/
abbrev Cursor.nsearch.wspec : Prop :=
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
        (rv.node' ≠ null → isSearchIdx ens kb (sint.nat idx))⌝ ∗
      cl ↦{dqc} cv ∗ cv.stack' ↦* es.set (es.length - 1) { rv with index' := idx } ∗
      leafRes rv q pg nv dqn ins dqs ens ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
