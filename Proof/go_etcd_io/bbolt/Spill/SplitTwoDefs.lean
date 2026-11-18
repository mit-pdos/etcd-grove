/-
The nodes, ownership and spec of `node.splitTwo`, out of `SplitTwo.lean`'s proof so that `Split`'s
definitions import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.bbolt.TxStats__IncSplit
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Proof.go_etcd_io.bbolt.Spill.SplitModel
public import Spec.go_etcd_io.bbolt.Data
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section nodes
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The first piece's inodes: the old slice's first `k`. -/
def inodesL (nv : node) (k : Nat) : GoSlice :=
  slice.slice nv.inodes' Inode (W64 0) (W64 (k : Int))

/-- The second piece's inodes: the rest of the old slice (and its capacity). -/
def inodesR (nv : node) (k : Nat) : GoSlice :=
  slice.slice nv.inodes' Inode (W64 (k : Int)) nv.inodes'.len

/-- The node after the split: its first `k` inodes, under the parent `pl`. -/
def splitLeft (nv : node) (pl : Loc) (k : Nat) : node :=
  { nv with parent' := pl, inodes' := inodesL nv k }

/-- The new node `next`: the other inodes, under the parent `pl`. -/
def splitRight (nv : node) (pl : Loc) (k : Nat) : node :=
  { (zero_val node : node) with bucket' := nv.bucket', isLeaf' := nv.isLeaf', parent' := pl, inodes' := inodesR nv k }

/-- A new parent: the node's bucket, the children `cs`. -/
def newParent (nv : node) (cs : GoSlice) : node :=
  { (zero_val node : node) with bucket' := nv.bucket', children' := cs }

/-- The parent after the split of `nl` (struct `nv`; its parent `pv`, children `pcs`) into it and
`nx`: the old one with `nx` appended to its children, or a new one whose children are the two. -/
def splitParent (nl nx : Loc) (nv pv : node) (pcs : List Loc) (pl : Loc) (pv' : node)
    (pcs' : List Loc) : Prop :=
  (nv.parent' = null ∧ pv' = newParent nv pv'.children' ∧ pcs' = [nl, nx]) ∨
  (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv' = { pv with children' := pv'.children' } ∧
    pcs' = pcs ++ [nx])

end nodes

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A node's parent `p` (if any): its struct and its children with their capacity. -/
def parentOwn (p : Loc) (pv : node) (pcs : List Loc) : IProp GF :=
  if p = null then iprop(emp) else
    iprop(p ↦ pv ∗ pv.children' ↦* pcs ∗ ownSliceCap Loc pv.children' (DFrac.own 1))

end own

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`n.splitTwo(ps)`** (`ps < 2 ^ 53`, every inode's share below `2 ^ 60` (`insBnd`), the bucket's fill percent not a NaN). Unsplit (`nil`),
everything as it was, and the node fits (`pieceFits ps`). Split at `k`: the node keeps its first
`k` inodes (`splitLeft`), a new node `nx` the rest with the capacity (`splitRight`), both under
the parent `pl` (`splitParent`), the first piece fitting; the split counted. -/
abbrev node.splitTwo.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp)
    (nl : Loc) (nv : node) (ins : List Inode) (f : w64) (dqf dqt : DFrac)
    (pv : node) (pcs : List Loc) (ps : w64),
  insBnd ins → ¬ float64IsNaN f → uint.Z ps < 2 ^ 53 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r ∗
      statsTok r m q ∗
      nl ↦ nv ∗ nv.inodes' ↦* ins ∗ ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗
      nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"splitTwo")) (Val #ps))
  {{ (nx : Loc), RET (PairV #nl #nx);
      statsTok r m q ∗
      nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      ((⌜nx = null ∧ pieceFits ps.toNat ins⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗ parentOwn nv.parent' pv pcs) ∨
        (∃ (k : Nat) (pl : Loc) (pv' : node) (pcs' : List Loc),
          ⌜2 ≤ k ∧ k + 3 ≤ ins.length ∧ pieceFits ps.toNat (ins.take k) ∧ nx ≠ null ∧ pl ≠ null ∧
            splitParent nl nx nv pv pcs pl pv' pcs'⌝ ∗
          nl ↦ splitLeft nv pl k ∗ inodesL nv k ↦* ins.take k ∗
          nx ↦ splitRight nv pl k ∗ inodesR nv k ↦* ins.drop k ∗
          ownSliceCap Inode (inodesR nv k) (DFrac.own 1) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1))) }}

end spec
section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

end proof

end bbolt
end EtcdGrove
end Perennial
