/-
The pure facts `freepages`' check needs of the root bucket of a `treeOK` view and its top-level
buckets (U10e of `notes/bbolt-proof-plan.md`): a top-level bucket has no nested bucket
(`rootShape`), is a tree root (`ownRootOK`) when stored in pages, and the own pages of the root and
of the top-level buckets, in `ForEachBucket`'s order, cover each slot of the view once.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckPure
public import Proof.go_etcd_io.bbolt.Inv.Tx
public import Proof.go_etcd_io.bbolt.Read.BktOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- Slot `x` is covered by an own page of one of the first `i` top-level buckets (in
`bktNames` order) stored in pages. -/
def chSlot (v : View) (i x : Nat) : Prop :=
  ∃ j < i, ∃ kb cv, (bktNames v.pages (rootVal v))[j]? = some kb ∧
    bktEntry v.pages (rootVal v) kb cv ∧ inBucketRoot cv ≠ 0 ∧
    ownSlot v.pages (inBucketRoot cv) x

/-- The root bucket's value names the view's root page. -/
theorem rootVal_root (v : View) (h : v.root < 2 ^ 64) : inBucketRoot (rootVal v) = v.root ∧
    16 ≤ (rootVal v).length := by
  rw [inBucketRoot_rootVal, rootVal_length]
  exact ⟨Nat.mod_eq_of_lt h, Nat.le_refl _⟩

/-- The view's root is a tree root. -/
theorem root_ownRootOK (v : View) (h : viewWF v) : ownRootOK v.pages v.root := by
  obtain ⟨C, hok, hvC⟩ := h
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  rw [hpv, hrv]
  exact ⟨C, hok, rfl, hok.1.1, hok.1.2.2.1⟩

/-- A top-level bucket is an entry of the root's tree. -/
theorem top_entries (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : ∃ n, (n, cv) ∈ treeEntries v.pages v.root := by
  sorry

/-- A name of the root bucket names one top-level bucket. -/
theorem top_entry_unique (v : View) (h : viewWF v) (kb cv cv' : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (he' : bktEntry v.pages (rootVal v) kb cv') :
    cv = cv' := by
  sorry

/-- A top-level bucket's value holds its header. -/
theorem top_len (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : 16 ≤ cv.length := by
  sorry

/-- A top-level bucket has no nested bucket. -/
theorem top_names_nil (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : bktNames v.pages cv = [] := by
  sorry

/-- A top-level bucket stored in pages is a tree root. -/
theorem top_ownRootOK (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (hf : inBucketRoot cv ≠ 0) :
    ownRootOK v.pages (inBucketRoot cv) := by
  sorry

/-- The root's own pages are not in a top-level bucket's tree. -/
theorem top_disj_root (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (hf : inBucketRoot cv ≠ 0) (x : Nat)
    (hx : ownSlot v.pages (inBucketRoot cv) x) : ¬ ownSlot v.pages v.root x := by
  sorry

/-- **The `i`-th top-level bucket's own pages are not an earlier one's.** -/
theorem top_disj_prev (v : View) (h : viewWF v) (i : Nat) (kb cv : List w8)
    (hi : (bktNames v.pages (rootVal v))[i]? = some kb) (he : bktEntry v.pages (rootVal v) kb cv)
    (hf : inBucketRoot cv ≠ 0) (x : Nat) (hx : ownSlot v.pages (inBucketRoot cv) x) :
    ¬ chSlot v i x := by
  sorry

/-- **The root's and the top-level buckets' own pages cover the view's slots.** -/
theorem root_cover (v : View) (h : viewWF v) (x : Nat) :
    (ownSlot v.pages v.root x ∨ chSlot v (bktNames v.pages (rootVal v)).length x) ↔
      coversSlot v.pages x := by
  sorry

end pure

end bbolt
end EtcdGrove
end Perennial
