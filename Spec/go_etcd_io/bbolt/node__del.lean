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

/-- `n.del(key)` on a node whose inodes are sorted: if an inode has the key (at the search
index `idx`), it is removed (in place: the inodes become `inodes[:len-1]`, the removed inode's
key and value are handed back) and the node is marked unbalanced; otherwise nothing changes. -/
abbrev node.del.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (ins : List internal.common.Inode) (es : List NodeEntry)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  entriesSorted es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗ inodesOwn ins es ∗ key ↦*{dk} kb }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"del")) (Val #key))
  {{ (idx : w64), RET #(); ⌜0 ≤ sint.Z idx ∧ isSearchIdx es kb (sint.nat idx)⌝ ∗ key ↦*{dk} kb ∗
      (if decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) then
        (∃ (it : internal.common.Inode) (e : NodeEntry),
          ⌜ins[sint.nat idx]? = some it ∧ es[sint.nat idx]? = some e⌝ ∗ inodeIs it e ∗
          nl ↦ ({ nv with inodes' := slice.slice nv.inodes' internal.common.Inode (W64 0) (nv.inodes'.len - W64 1), unbalanced' := true } : node) ∗
          slice.slice nv.inodes' internal.common.Inode (W64 0) (nv.inodes'.len - W64 1) ↦*
            ins.eraseIdx (sint.nat idx) ∗
          ownSliceCap internal.common.Inode
            (slice.slice nv.inodes' internal.common.Inode (W64 0) (nv.inodes'.len - W64 1)) (DFrac.own 1) ∗
          inodesOwn (ins.eraseIdx (sint.nat idx)) (es.eraseIdx (sint.nat idx)))
      else
        nl ↦ nv ∗ nv.inodes' ↦* ins ∗ ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗
          inodesOwn ins es) }}

end spec

end bbolt
end EtcdGrove
end Perennial
