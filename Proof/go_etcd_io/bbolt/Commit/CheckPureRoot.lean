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
  exact ⟨C, hok, rfl, ⟨C.hwm, hok.1.1⟩, hok.1.2.2.1⟩

/-- A top-level bucket is an entry of the root's tree. -/
theorem top_entries (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : ∃ n, (n, cv) ∈ treeEntries v.pages v.root := by
  obtain ⟨pg, i, hpg, hi, hk, -, hv⟩ := he
  have hr : inBucketRoot (rootVal v) = v.root := by
    obtain ⟨C, hok, hvC⟩ := h
    have hrv : v.root = C.root := by rw [← hvC]; rfl
    rw [inBucketRoot_rootVal, hrv]
    cases hok.1.1 with
    | page _ pg _ _ hpg hid _ _ =>
      have : C.root < 2 ^ 64 := by rw [← hid]; unfold pageId; exact BitVec.isLt _
      omega
  have hr0 : inBucketRoot (rootVal v) ≠ 0 := by
    obtain ⟨C, hok, hvC⟩ := h
    have hrv : v.root = C.root := by rw [← hvC]; rfl
    rw [hr, hrv]
    cases hok.1.1 with | page _ _ h2 _ _ _ _ _ => omega
  unfold bktLeaves at hpg
  rw [if_neg hr0, hr] at hpg
  refine ⟨kb, ?_⟩
  unfold treeEntries
  refine List.mem_flatMap.mpr ⟨pg, hpg, ?_⟩
  unfold leafEnts
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, by rw [hk, hv]⟩

/-- A name of the root bucket names one top-level bucket. -/
theorem top_entry_unique (v : View) (h : viewWF v) (kb cv cv' : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (he' : bktEntry v.pages (rootVal v) kb cv') :
    cv = cv' := by
  sorry

/-- A top-level bucket's value holds its header. -/
theorem top_len (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : 16 ≤ cv.length :=
  (rBktOK_of v h cv (.inr (top_entries v h kb cv he))).1

/-- A top-level bucket stored in pages is a tree root. -/
theorem top_ownRootOK (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (hf : inBucketRoot cv ≠ 0) :
    ownRootOK v.pages (inBucketRoot cv) := by
  obtain ⟨-, ht, hk⟩ := rBktOK_of v h cv (.inr (top_entries v h kb cv he))
  obtain ⟨C, hok, hvC⟩ := h
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  refine ⟨C, hok, hpv.symm, ?_, hk hf⟩
  rcases ht with ⟨h0, _⟩ | ⟨_, hwm, hw⟩
  · exact absurd h0 hf
  · exact ⟨hwm, hw⟩

/-- A top-level bucket has no nested bucket. -/
theorem top_names_nil (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : bktNames v.pages cv = [] := by
  obtain ⟨n, hn⟩ := top_entries v h kb cv he
  have h' := h
  obtain ⟨C, hok, hvC⟩ := h'
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  obtain ⟨⟨hw, -, hk, -⟩, -, -, -, hshape, -⟩ := hok
  rw [hpv, hrv] at hn
  unfold treeEntries treeLeaves at hn
  obtain ⟨pg, hpg, hent⟩ := List.mem_flatMap.mp hn
  obtain ⟨id', lo', hi', ho, hpid, hfl, -, -⟩ :=
    leavesF_page C.pages C.hwm _ _ _ _ hw hk pg hpg
  unfold leafEnts at hent
  obtain ⟨i, hi, he'⟩ := List.mem_map.mp hent
  rw [List.mem_range] at hi
  simp only [Prod.mk.injEq] at he'
  obtain ⟨-, rfl⟩ := he'
  have hsh := (hshape id' pg ho hpid hfl i hi).2.2.2
  unfold bktNames
  rw [hpv]
  apply List.flatMap_eq_nil_iff.mpr
  intro bpg hb
  have hleaf : bktLeafPg C.pages (leafValue pg i) bpg := by
    unfold bktLeaves at hb
    split at hb
    · rename_i h0
      simp only [List.mem_singleton] at hb
      exact .inl ⟨h0, hb⟩
    · rename_i h0
      obtain ⟨C', hok', hCP', ⟨hwm', hw'⟩, hk'⟩ := top_ownRootOK v h kb _ he h0
      rw [← hCP'] at hpv
      have hw'' : treeWF C.pages hwm' (inBucketRoot (leafValue pg i)) := by
        rw [← hpv, hCP']; exact hw'
      have hk'' : treeKeys C.pages (inBucketRoot (leafValue pg i)) none none := by
        rw [← hpv, hCP']; exact hk'
      obtain ⟨p, -, -, hop, hpp, hfp, -⟩ := leavesF_page C.pages hwm' _ _ _ _ hw'' hk'' bpg hb
      exact .inr ⟨h0, p, hop, hpp, hfp⟩
  have := hsh bpg hleaf
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_range, decide_eq_true_eq]
  intro j hj
  rw [(this j hj).1]; simp [bucketLeafFlag]

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
