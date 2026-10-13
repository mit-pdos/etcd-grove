/-
A range read of the backend's `Key` bucket (`UnsafeRange(schema.Key, lo, hi, 0)`, the watchable
store's `rangeEvents`): the entries of the bucket whose key is in `[lo, hi)`, in key order. Keys
are bytes ordered lexicographically (`go.GoStringLt`: bbolt's cursor order, Perennial's
`bytes.Compare`). Lean-first; `notes/decisions.md`, "The watchable store's concurrency (unit 3)".

`bucketRange m klo khi` is a pure function (the map's entries filtered and sorted); it is
characterized by its members and its keys strictly increasing (`bucketRange_eq_iff`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- The entries of the bucket `m` whose key is in `[klo, khi)`, in key order (`go.GoStringLt`,
lexicographic on bytes). -/
def bucketRange (m : GMap GoString GoString) (klo khi : GoString) : List (GoString × GoString) :=
  (m.toList.filter fun p => decide (go.GoStringLe klo p.1) && decide (go.GoStringLt p.1 khi)).mergeSort
    fun a b => decide (go.GoStringLe a.1 b.1)

/-! Go's `≤` on strings. -/

theorem goStringLe_trans {a b c : GoString} (h1 : go.GoStringLe a b) (h2 : go.GoStringLe b c) :
    go.GoStringLe a c := by
  unfold go.GoStringLe at *
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (adt.strLt_trans h1 h2)

theorem goStringLe_total (a b : GoString) : go.GoStringLe a b ∨ go.GoStringLe b a := by
  unfold go.GoStringLe
  by_cases h1 : go.GoStringLt a b
  · exact Or.inl (Or.inr h1)
  · by_cases h2 : go.GoStringLt b a
    · exact Or.inr (Or.inr h2)
    · exact Or.inl (Or.inl (adt.strLt_eq_of_not_lt h1 h2))

theorem goStringLe_antisymm {a b : GoString} (h1 : go.GoStringLe a b) (h2 : go.GoStringLe b a) :
    a = b := by
  unfold go.GoStringLe at *
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2.symm
    · exact absurd h2 (adt.strLt_asymm h1)

/-- **`bucketRange` is characterized** by its keys strictly increasing and its members: the
entries of `m` with a key in `[klo, khi)`. -/
theorem bucketRange_eq_iff (m : GMap GoString GoString) (klo khi : GoString)
    (l : List (GoString × GoString)) :
    bucketRange m klo khi = l ↔
      (l.map Prod.fst).Pairwise go.GoStringLt ∧
      ∀ k v, (k, v) ∈ l ↔ m !! k = some v ∧ go.GoStringLe klo k ∧ go.GoStringLt k khi := by
  let F := m.toList.filter fun p => decide (go.GoStringLe klo p.1) && decide (go.GoStringLt p.1 khi)
  let le : GoString × GoString → GoString × GoString → Bool := fun a b => decide (go.GoStringLe a.1 b.1)
  have hmemF : ∀ k v, (k, v) ∈ F ↔ m !! k = some v ∧ go.GoStringLe klo k ∧ go.GoStringLt k khi := by
    intro k v
    simp only [F, List.mem_filter, GMap.mem_toList, Bool.and_eq_true, decide_eq_true_eq]
  have hndF : (F.map Prod.fst).Nodup :=
    (GMap.toList_keys_nodup m).sublist (List.Sublist.map _ List.filter_sublist)
  have hperm : List.Perm (bucketRange m klo khi) F := List.mergeSort_perm _ _
  have hsorted : (bucketRange m klo khi).Pairwise (fun a b => le a b = true) :=
    List.pairwise_mergeSort (le := le) (fun a b c h1 h2 => by
        simp only [le, decide_eq_true_eq] at *; exact goStringLe_trans h1 h2)
      (fun a b => by
        simp only [le, Bool.or_eq_true, decide_eq_true_eq]; exact goStringLe_total _ _) F
  have hndS : ((bucketRange m klo khi).map Prod.fst).Nodup := (hperm.map _).nodup_iff.2 hndF
  have hltS : ((bucketRange m klo khi).map Prod.fst).Pairwise go.GoStringLt := by
    rw [List.pairwise_map]
    have h2 := List.nodup_iff_pairwise_ne.1 hndS
    rw [List.pairwise_map] at h2
    refine (hsorted.and h2).imp ?_
    rintro a b ⟨h1, h2⟩
    simp only [le, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 h2
    · exact h1
  have hmemS : ∀ k v, (k, v) ∈ bucketRange m klo khi ↔
      m !! k = some v ∧ go.GoStringLe klo k ∧ go.GoStringLt k khi := by
    intro k v; rw [hperm.mem_iff]; exact hmemF k v
  constructor
  · rintro rfl; exact ⟨hltS, hmemS⟩
  · rintro ⟨hl, hlm⟩
    have hndl : (l.map Prod.fst).Nodup :=
      hl.imp (fun {a b} (h : go.GoStringLt a b) (hab : a = b) => adt.strLt_irrefl a (hab ▸ h))
    have hp : List.Perm (bucketRange m klo khi) l := by
      rw [List.perm_ext_iff_of_nodup (List.Pairwise.of_map Prod.fst (fun a b (h : a.1 ≠ b.1) hab => h (by rw [hab])) hndS) (List.Pairwise.of_map Prod.fst (fun a b (h : a.1 ≠ b.1) hab => h (by rw [hab])) hndl)]
      rintro ⟨k, v⟩
      rw [hmemS, hlm]
    apply hp.eq_of_pairwise (le := fun a b => le a b = true)
    · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb h1 h2
      simp only [le, decide_eq_true_eq] at h1 h2
      have he := goStringLe_antisymm h1 h2
      change a1 = b1 at he
      subst he
      have h1 := ((hmemS _ _).1 ha).1
      have h2 := ((hlm _ _).1 hb).1
      rw [h1] at h2; cases h2; rfl
    · exact hsorted
    · rw [List.pairwise_map] at hl
      exact hl.imp (fun h => by simp only [le, decide_eq_true_eq]; exact Or.inr h)


end mvcc
end EtcdGrove
end Perennial
