module
public import Proof.go_etcd_io.bbolt.NodeModel

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

/-- `n.put(oldKey, newKey, value, pgId, flags)` on a node whose inodes are sorted: at the
search index `idx` of `oldKey`, the inode with that key is replaced (and its key and value
handed back), or, if there is none, a new inode is inserted (the inodes may move: `s'`); the
inode is `flags`, `pgId`, `newKey`, `value`, which it now holds. It panics if `pgId` is not
below the transaction's high-water mark (`n.bucket.tx.meta.pgid`) or a key is empty. -/
abbrev node.put.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (ins : List internal.common.Inode) (es : List NodeEntry)
    (bv : Bucket) (dqb : DFrac) (tv : Tx) (dqt : DFrac) (mv : internal.common.Meta) (dqm : DFrac)
    (oldKey : GoSlice) (okb : List w8) (dok : DFrac) (newKey : GoSlice) (nkb : List w8) (dnk : DFrac)
    (value : GoSlice) (vb : List w8) (dv : DFrac) (pgId : w64) (flags : w32),
  entriesSorted es → uint.Z pgId < uint.Z mv.pgid' → 0 < okb.length → 0 < nkb.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗ inodesOwn ins es ∗
      nv.bucket' ↦{dqb} bv ∗ bv.tx' ↦{dqt} tv ∗ tv.meta' ↦{dqm} mv ∗
      oldKey ↦*{dok} okb ∗ newKey ↦*{dnk} nkb ∗ value ↦*{dv} vb }}
    (App (App (App (App (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"put")) (Val #oldKey))
      (Val #newKey)) (Val #value)) (Val #pgId)) (Val #flags))
  {{ (idx : w64) (s' : GoSlice), RET #();
      ⌜0 ≤ sint.Z idx ∧ isSearchIdx es okb (sint.nat idx)⌝ ∗
      nv.bucket' ↦{dqb} bv ∗ bv.tx' ↦{dqt} tv ∗ tv.meta' ↦{dqm} mv ∗ oldKey ↦*{dok} okb ∗
      nl ↦ ({ nv with inodes' := s' } : node) ∗
      s' ↦* putList ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb))
        (internal.common.Inode.mk flags pgId newKey value) ∗
      ownSliceCap internal.common.Inode s' (DFrac.own 1) ∗
      inodesOwn
        (putList ins (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb))
          (internal.common.Inode.mk flags pgId newKey value))
        (putList es (sint.nat idx) (decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb))
          (NodeEntry.mk flags pgId nkb vb dnk dv)) ∗
      (if decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb) then
        (∃ (it : internal.common.Inode) (e : NodeEntry),
          ⌜ins[sint.nat idx]? = some it ∧ es[sint.nat idx]? = some e⌝ ∗ inodeIs it e)
      else True) }}

end spec

end bbolt
end EtcdGrove
end Perennial
