/-
The read path's (U6, `notes/bbolt-proof-plan.md`) search correctness over a reader's view: a
route (`rRoute`, what `Cursor.search` builds) from a bucket's root ends at a leaf of the bucket
(`bktLeaves`), and that leaf is the only one that can hold the key searched for. Also the
height bound that makes the leaves' fuel enough (`pht_lt_size`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__search_r

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section route

/-- A key within a child's bounds is within its branch's (whose keys are within them). -/
theorem keyIn_child (lo hi : Option (List w8)) (ks : Nat → List w8) (cnt j : Nat) (k : List w8)
    (hj : j < cnt) (hks : ∀ i < cnt, keyIn lo hi (ks i))
    (h : keyIn (childLo lo ks j) (childHi hi ks cnt j) k) : keyIn lo hi k := by
  obtain ⟨hge, hlt⟩ := h
  constructor
  · intro l hl hkl
    unfold childLo at hge
    split at hge
    · exact hge l hl hkl
    · have h1 := hge (ks j) rfl
      have h2 := (hks j hj).1 l hl
      by_cases hb : go.GoStringLt (ks j) k
      · exact h2 (go.goStringLt_trans hb hkl)
      · have := go.goStringLt_eq_of_not_lt hb h1
        rw [this] at h2; exact h2 hkl
  · intro h' hh
    unfold childHi at hlt
    split at hlt
    · exact go.goStringLt_trans (hlt _ rfl) ((hks _ (by omega)).2 h' hh)
    · exact hlt h' hh

variable [GooseExts]

/-- The keys of a tree's leaves are within the tree's bounds. -/
theorem leavesF_keyIn (P : Pages) : ∀ (n id : Nat) (lo hi : Option (List w8)),
    treeKeys P id lo hi → ∀ pg ∈ leavesF n P id, ∀ i < pageCount pg, keyIn lo hi (leafKey pg i)
  | 0, _, _, _, _, pg, h => by simp [leavesF] at h
  | n + 1, id, lo, hi, hk, pg', h => by
    cases hk with
    | leaf _ pg _ _ hpg hfl hkin _ =>
      simp only [leavesF, hpg, hfl, if_true, List.mem_singleton] at h
      subst h; exact hkin
    | branch _ pg _ _ kind hpg hfl _ hkin _ hch =>
      have hnl : ¬ pageFlags pg = leafPageFlag := by
        rw [hfl]; simp [branchPageFlag, leafPageFlag]
      simp only [leavesF, hpg, hnl, if_false, List.mem_flatMap, List.mem_range] at h
      obtain ⟨j, hj, hm⟩ := h
      intro i hi'
      exact keyIn_child lo hi (branchKey pg) _ j _ hj hkin
        (leavesF_keyIn P n _ _ _ (hch j hj) pg' hm i hi')

/-- **The branch index a key routes to is the only child whose bounds hold it.** -/
theorem branchRoute_unique (pg : List w8) (k : List w8) (r j : Nat)
    (lo hi : Option (List w8)) (hr : branchRoute pg k r)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (branchKey pg i) (branchKey pg j))
    (hj : j < pageCount pg)
    (h : keyIn (childLo lo (branchKey pg) j) (childHi hi (branchKey pg) (pageCount pg) j) k) :
    j = r := by
  obtain ⟨hrc, hr0, hr1⟩ := hr
  obtain ⟨hge, hlt⟩ := h
  have hj0 : j = 0 ∨ ¬ go.GoStringLt k (branchKey pg j) := by
    unfold childLo at hge
    split at hge
    · exact Or.inl ‹_›
    · exact Or.inr (hge _ rfl)
  have hj1 : j + 1 < pageCount pg → go.GoStringLt k (branchKey pg (j + 1)) := by
    intro h1
    unfold childHi at hlt
    rw [if_pos h1] at hlt
    exact hlt _ rfl
  rcases Nat.lt_trichotomy j r with hjr | hjr | hjr
  · exfalso
    have hk := hj1 (by omega)
    rcases hr0 with h0 | h0
    · omega
    · rcases Nat.lt_or_ge (j + 1) r with h2 | h2
      · exact h0 (go.goStringLt_trans hk (hs _ _ h2 hrc))
      · have : j + 1 = r := by omega
        rw [this] at hk; exact h0 hk
  · exact hjr
  · exfalso
    have hk := hr1 (by omega)
    rcases hj0 with h0 | h0
    · omega
    · rcases Nat.lt_or_ge (r + 1) j with h2 | h2
      · exact h0 (go.goStringLt_trans hk (hs _ _ h2 hj))
      · have : r + 1 = j := by omega
        rw [this] at hk; exact h0 hk

/-- **Where a route ends**: at a leaf element of the leaves `L` (a page reference, at the key's
search index), the only leaf of `L` that can hold the key. -/
def rRouteEnd (v : View) (bv : List w8) (pp : Loc) (k : List w8) (path : List elemRef)
    (L : List (List w8)) : Prop :=
  ∃ els e pid pg, path = els ++ [e] ∧ rPageAt v bv pp pid = some (e.page', pg) ∧
    e.node' = null ∧ pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧ 16 ≤ pg.length ∧
    e.index' = W64 (pageSeekIdx pg k : Int) ∧ pg ∈ L ∧
    ∀ pg' ∈ L, ∀ i < pageCount pg', leafKey pg' i = k → pg' = pg

/-- A route in a bucket stored in pages, from a well-formed position with B+tree keys. -/
theorem rRoute_tree (v : View) (bv : List w8) (pp : Loc) (k : List w8)
    (hi : inBucketRoot bv ≠ 0) (pht : Nat → Nat) (hht : pageHts v.pages pht) :
    ∀ (n pid : Nat) (path : List elemRef) (lo hi' : Option (List w8)), pht pid < n →
      (∃ hwm, treeWF v.pages hwm pid) → treeKeys v.pages pid lo hi' →
      rRoute v bv pp k pid path → rRouteEnd v bv pp k path (leavesF n v.pages pid)
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, pid, path, lo, hi', hn, ⟨hwm, hw⟩, hk, hr => by
    match path, hr with
    | [e], ⟨pg, hpa, hnode, hfl, hidx⟩ =>
      unfold rPageAt at hpa
      rw [if_neg hi] at hpa
      obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp hpa
      simp only [Prod.mk.injEq] at he
      obtain ⟨hl, rfl⟩ := he
      have hL : leavesF (n + 1) v.pages pid = [pg'] := by
        simp only [leavesF, hpg, hfl, if_true]
      rw [hL]
      cases hw with
      | page _ pg2 _ _ hpg2 _ hlen hpt =>
        rw [hpg] at hpg2; cases hpg2
        cases hpt with
        | leaf _ _ _ hlwf _ =>
          refine ⟨[], e, pid, pg', by simp, ?_, hnode, hfl, hlwf, by rw [hlen]; omega, hidx,
            List.mem_singleton_self _, fun pg'' h _ _ _ => List.mem_singleton.mp h⟩
          unfold rPageAt; rw [if_neg hi, hpg]; simp [hl]
        | branch _ _ hf _ _ => rw [hfl] at hf; simp [branchPageFlag, leafPageFlag] at hf
    | e :: e' :: es, ⟨pg, hpa, hnode, hfl, hbr, hrt⟩ =>
      unfold rPageAt at hpa
      rw [if_neg hi] at hpa
      obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp hpa
      simp only [Prod.mk.injEq] at he
      obtain ⟨hl, rfl⟩ := he
      have hnl : ¬ pageFlags pg' = leafPageFlag := by
        rw [hfl]; simp [branchPageFlag, leafPageFlag]
      have hL : leavesF (n + 1) v.pages pid = (List.range (pageCount pg')).flatMap
          fun i => leavesF n v.pages (branchPgid pg' i) := by
        simp only [leavesF, hpg, hnl, if_false]
      rw [hL]
      have hrc := hbr.1
      cases hw with
      | page _ pg2 _ _ hpg2 _ _ hpt =>
        rw [hpg] at hpg2; cases hpg2
        cases hpt with
        | leaf _ _ hf _ _ => exact absurd hf hnl
        | branch _ _ _ hbwf hch =>
          cases hk with
          | leaf _ pg3 _ _ hpg3 hf3 _ _ =>
            rw [hpg] at hpg3; cases hpg3; exact absurd hf3 hnl
          | branch _ pg3 _ _ kind hpg3 _ _ _ _ hkch =>
            rw [hpg] at hpg3; cases hpg3
            have hht' := (hht pid pg' hpg).2 hfl _ hrc
            obtain ⟨els, e2, pidL, pgL, hpe, hpaL, hnL, hfL, hwL, h16L, hiL, hmem, hfound⟩ :=
              rRoute_tree v bv pp k hi pht hht n _ (e' :: es) _ _ (by omega)
                ⟨hwm, hch _ hrc⟩ (hkch _ hrc) hrt
            refine ⟨e :: els, e2, pidL, pgL, by rw [hpe]; rfl, hpaL, hnL, hfL, hwL, h16L, hiL,
              List.mem_flatMap.mpr ⟨_, List.mem_range.mpr hrc, hmem⟩, ?_⟩
            intro pg'' hm i hic hki
            obtain ⟨j, hj, hm'⟩ := List.mem_flatMap.mp hm
            rw [List.mem_range] at hj
            have hkin := leavesF_keyIn v.pages n _ _ _ (hkch j hj) pg'' hm' i hic
            rw [hki] at hkin
            have hjr := branchRoute_unique pg' k _ j lo hi' hbr hbwf.2.2.2.2 hj hkin
            rw [hjr] at hm'
            exact hfound pg'' hm' i hic hki

/-- A route in an inline bucket: its only leaf. -/
theorem rRoute_inline (v : View) (bv : List w8) (pp : Loc) (k : List w8)
    (hi : inBucketRoot bv = 0) (ht : rTree v bv 0) (path : List elemRef)
    (hr : rRoute v bv pp k 0 path) : rRouteEnd v bv pp k path [inlinePage bv] := by
  rcases ht with ⟨_, _, hfl, hwf⟩ | ⟨hi', _⟩
  · match path, hr with
    | [e], ⟨pg, hpa, hnode, hfl', hidx⟩ =>
      unfold rPageAt at hpa
      simp only [if_pos hi, if_true, Option.some.injEq, Prod.mk.injEq] at hpa
      obtain ⟨hl, rfl⟩ := hpa
      refine ⟨[], e, 0, inlinePage bv, by simp, ?_, hnode, hfl, hwf, ?_, hidx,
        List.mem_singleton_self _, fun pg'' h _ _ _ => List.mem_singleton.mp h⟩
      · unfold rPageAt; simp [hi, hl]
      · have := hwf.2.1; unfold elemOff at this; omega
    | e :: e' :: es, ⟨pg, hpa, _, hfl', _, _⟩ =>
      unfold rPageAt at hpa
      simp only [if_pos hi, if_true, Option.some.injEq, Prod.mk.injEq] at hpa
      obtain ⟨_, rfl⟩ := hpa
      rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
  · exact absurd hi hi'

end route

end bbolt
end EtcdGrove
end Perennial
