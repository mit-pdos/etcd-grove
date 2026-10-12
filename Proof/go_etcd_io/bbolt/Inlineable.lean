/-
When a bucket of a write transaction is inlineable (`Bucket.inlineable`), as a pure fact of its
record: its root node is materialized, a leaf, with no nested bucket, and the size of its page
(`PageHeaderSize`, then per inode a `LeafPageElementSize` element and its key and value, in
`uintptr` arithmetic: `sizeFrom`) after each inode at most `pageSize / 4`
(`Bucket.maxInlineBucketSize`). Stated over the node's inodes (`r.ins`); for a clean node they
are its entries `r.ws` (`wOwn`: the same flags, and keys and values of the entries' lengths).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section inl
variable [ext : FfiSyntax]

/-- `b.maxInlineBucketSize()` for the page size `ps`. -/
def maxInline (ps : Nat) : w64 := W64 ((ps / 4 : Nat) : Int)

/-- No inode of `ins` is a nested bucket, and the page's size after each is at most `mx`. -/
def inlineIns (mx : w64) (ins : List Inode) : Prop :=
  ∀ (k : Nat) (it : Inode), ins[k]? = some it →
    it.flags' &&& W32 1 = W32 0 ∧ uint.Z (sizeFrom (W64 16) (W64 16) (ins.take (k + 1))) ≤ uint.Z mx

/-- The node `r` is inlineable for the page size `ps`. -/
def inlineNode (r : NRec) (ps : Nat) : Prop :=
  r.nv.isLeaf' = true ∧ inlineIns (maxInline ps) r.ins

/-- `b.inlineable()` of the bucket `B` for the page size `ps`: its root node is materialized
and inlineable. -/
def inlineableB (B : BRec) (ps : Nat) : Prop :=
  B.bv.rootNode' ≠ null ∧ ∃ r, B.ns !! B.bv.rootNode' = some r ∧ inlineNode r ps

theorem inlineableB_of_root (B : BRec) (r : NRec) (ps : Nat) (hn : B.bv.rootNode' ≠ null)
    (hr : B.ns !! B.bv.rootNode' = some r) : inlineableB B ps ↔ inlineNode r ps := by
  unfold inlineableB
  constructor
  · rintro ⟨-, r', hr', h⟩; rw [hr] at hr'; cases hr'; exact h
  · intro h; exact ⟨hn, r, hr, h⟩

theorem not_inlineableB_nil (B : BRec) (ps : Nat) (hn : B.bv.rootNode' = null) :
    ¬ inlineableB B ps := fun h => h.1 hn

theorem inlineIns_nil (mx : w64) : inlineIns mx [] := by
  intro k it h; simp at h

theorem inlineIns_step (mx : w64) (ins : List Inode) (j : Nat) (it : Inode)
    (hj : ins[j]? = some it) (hpre : ∀ k it', k < j → ins[k]? = some it' →
      it'.flags' &&& W32 1 = W32 0 ∧
      uint.Z (sizeFrom (W64 16) (W64 16) (ins.take (k + 1))) ≤ uint.Z mx)
    (hf : it.flags' &&& W32 1 = W32 0)
    (hs : uint.Z (sizeFrom (W64 16) (W64 16) (ins.take (j + 1))) ≤ uint.Z mx) :
    ∀ k it', k < j + 1 → ins[k]? = some it' →
      it'.flags' &&& W32 1 = W32 0 ∧
      uint.Z (sizeFrom (W64 16) (W64 16) (ins.take (k + 1))) ≤ uint.Z mx := by
  intro k it' hk hk'
  by_cases e : k = j
  · subst e; rw [hj] at hk'; cases hk'; exact ⟨hf, hs⟩
  · exact hpre k it' (by omega) hk'

theorem sizeFrom_take_succ (ins : List Inode) (j : Nat) (it : Inode) (hj : ins[j]? = some it) :
    sizeFrom (W64 16) (W64 16) (ins.take (j + 1)) =
      sizeFrom (W64 16) (W64 16) (ins.take j) + (W64 16 + it.key'.len + it.value'.len) := by
  rw [List.take_add_one, hj]
  simp only [Option.toList_some]
  rw [sizeFrom_append]

/-- `b.maxInlineBucketSize()`'s division. -/
theorem maxInline_eq (ps : Nat) (h : ps < 2 ^ 63) :
    BitVec.sdiv (W64 (ps : Int)) (W64 4) = maxInline ps := by
  unfold maxInline
  word

end inl

end bbolt
end EtcdGrove
end Perennial
