/-
`node.splitTwo` and `node.split` (the write path's spill): what they need and give.

`splitTwo` splits a node of more than four inodes that does not fit a page at the index
`splitIndex` picks (`splitIndexOf`, at a threshold of the page size times the bucket's fill
percent: a `float64`, its value uninterpreted), which is at least 2 and leaves at least 2: the
first part stays the node (its inodes a prefix of the old slice, whose capacity is now the
second part's), the second a new node `next` under the same parent (made if there is none),
appended to the parent's children.
-/
module

public import Proof.go_etcd_io.bbolt.NodeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem splitIndexGo_range (thr : w64) :
    ∀ (l : List Inode) (i : Nat) (idx sz : w64), l ≠ [] → i + l.length < 2 ^ 63 →
    ∃ j : Nat, (splitIndexGo thr i idx sz l).1 = W64 (j : Int) ∧ i ≤ j ∧ j + 1 ≤ i + l.length ∧
      (2 ≤ j ∨ j + 1 = i + l.length)
  | [], _, _, _, h, _ => absurd rfl h
  | it :: rest, i, idx, sz, _, hl => by
    simp only [splitIndexGo]
    have hi : uint.Z (W64 (i : Int)) = i := by
      simp only [List.length_cons] at hl; word
    split
    · rename_i hc
      refine ⟨i, rfl, Nat.le_refl _, by simp only [List.length_cons]; omega, Or.inl ?_⟩
      have := hc.1; omega
    · cases rest with
      | nil =>
        refine ⟨i, rfl, Nat.le_refl _, by simp, Or.inr (by simp)⟩
      | cons it2 rest2 =>
        obtain ⟨j, hj, h1, h2, h3⟩ := splitIndexGo_range thr (it2 :: rest2) (i + 1)
          (W64 (i : Int)) _ (by simp) (by simp only [List.length_cons] at hl ⊢; omega)
        refine ⟨j, hj, by omega, by simp only [List.length_cons] at h2 ⊢; omega, ?_⟩
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · right; simp only [List.length_cons] at h3 ⊢; omega

/-- The split index of more than four inodes: at least 2, leaving at least 2 (in fact 3). -/
theorem splitIndexOf_range (thr : w64) (ins : List Inode) (h5 : 5 ≤ ins.length)
    (hl : ins.length < 2 ^ 63) :
    ∃ k : Nat, (splitIndexOf thr ins).1 = W64 (k : Int) ∧ 2 ≤ k ∧ k + 3 ≤ ins.length := by
  unfold splitIndexOf
  have hne : ins.take (ins.length - 2) ≠ [] := by
    intro e; have := congrArg List.length e; simp at this; omega
  have hlen : (ins.take (ins.length - 2)).length = ins.length - 2 := by simp only [List.length_take]; omega
  obtain ⟨j, hj, -, h2, h3⟩ := splitIndexGo_range thr _ 0 (W64 0) (W64 16) hne (by rw [hlen]; omega)
  rw [hlen] at h2 h3
  exact ⟨j, hj, by omega, by omega⟩

end pure

section nodes
variable [ext : FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The first part's inodes: a prefix of the old slice. -/
def inodesL (nv : node) (k : Nat) : GoSlice :=
  slice.slice nv.inodes' Inode (W64 0) (W64 (k : Int))

/-- The second part's inodes: the rest of the old slice (and its capacity). -/
def inodesR (nv : node) (k : Nat) : GoSlice :=
  slice.slice nv.inodes' Inode (W64 (k : Int)) nv.inodes'.len

/-- The node after the split: its first `k` inodes, under the parent `pl`. -/
def splitLeft (nv : node) (pl : Loc) (k : Nat) : node :=
  { nv with parent' := pl, inodes' := inodesL nv k }

/-- The new node `next`: the other inodes, under the parent `pl`. -/
def splitRight (nv : node) (pl : Loc) (k : Nat) : node :=
  { zero_val node with bucket' := nv.bucket', isLeaf' := nv.isLeaf', parent' := pl, inodes' := inodesR nv k }

/-- A new parent: the node's bucket, the children `cs`. -/
def newParent (nv : node) (cs : GoSlice) : node :=
  { zero_val node with bucket' := nv.bucket', children' := cs }

/-- The parent after the split of `nl` (struct `nv`; its parent `pv`, children `pcs`) into it
and `nx`: the old one, `nx` appended to its children, or a new one, its children the two. -/
def splitParent (nl nx : Loc) (nv pv : node) (pcs : List Loc) (pl : Loc) (pv' : node)
    (pcs' : List Loc) : Prop :=
  (nv.parent' = null ∧ pv' = newParent nv pv'.children' ∧ pcs' = [nl, nx]) ∨
  (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv' = { pv with children' := pv'.children' } ∧
    pcs' = pcs ++ [nx])

end nodes

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The parent `p` of a node (its struct `pv`, children `pcs`), owned when there is one. -/
def parentOwn (p : Loc) (pv : node) (pcs : List Loc) : IProp GF :=
  if p = null then iprop(emp) else
    iprop(p ↦ pv ∗ pv.children' ↦* pcs ∗ ownSliceCap Loc pv.children' (DFrac.own 1))

end own

end bbolt
end EtcdGrove
end Perennial
