module
public import Proof.go_etcd_io.bbolt.WriteSplit

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

/-- `n.splitTwo(pageSize)` (see `WriteSplit`): either nothing (`next` nil), or the node keeps
its first `k` inodes (at least 2; a prefix of its old slice, without capacity of its own) and a
new node `next` under the parent `pl` (the old one, or a new one whose children are the node)
gets the others (at least 3), appended to `pl`'s children. -/
abbrev node.splitTwo.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (ins : List internal.common.Inode) (bv : Bucket) (dqb : DFrac)
    (st : TxStats) (pv : node) (pcs : List Loc) (ps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗ nv.bucket' ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"splitTwo")) (Val #ps))
  {{ (nx : Loc), RET (PairV #nl #nx); nv.bucket' ↦{dqb} bv ∗
      ((⌜nx = null⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs) ∨
        (∃ (k : Nat) (pl : Loc) (pv' : node) (pcs' : List Loc),
          ⌜2 ≤ k ∧ k + 3 ≤ ins.length ∧ nx ≠ null ∧ pl ≠ null ∧
            splitParent nl nx nv pv pcs pl pv' pcs'⌝ ∗
          nl ↦ splitLeft nv pl k ∗ inodesL nv k ↦* ins.take k ∗
          nx ↦ splitRight nv pl k ∗ inodesR nv k ↦* ins.drop k ∗
          ownSliceCap internal.common.Inode (inodesR nv k) (DFrac.own 1) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦ ({ st with Split' := st.Split' + W64 1 } : TxStats))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
