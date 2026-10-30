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

/-- `n.childIndex(child)` on a node whose inodes are sorted: where the child's key goes among
them (`isSearchIdx`: the index of the inode with that key, if there is one). -/
abbrev node.childIndex.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (dq : DFrac) (ins : List internal.common.Inode) (dqs : DFrac)
    (es : List NodeEntry) (cl : Loc) (cv : node) (dqc : DFrac) (ck : List w8) (dk : DFrac),
  entriesSorted es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins ∗
      inodesOwn ins es ∗ cl ↦{dqc} cv ∗ cv.key' ↦*{dk} ck }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"childIndex")) (Val #cl))
  {{ (idx : w64), RET #idx; ⌜0 ≤ sint.Z idx ∧ isSearchIdx es ck (sint.nat idx)⌝ ∗
      nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodesOwn ins es ∗ cl ↦{dqc} cv ∗ cv.key' ↦*{dk} ck }}

end spec

end bbolt
end EtcdGrove
end Perennial
