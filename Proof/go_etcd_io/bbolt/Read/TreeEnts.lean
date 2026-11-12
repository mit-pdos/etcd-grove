/-
U6 (`notes/bbolt-proof-plan.md`): `bktEnts_treeEntries` (`Model/TreeData`), proved as
`bktEnts_treeEntries'`. A top-level bucket of `treeData C` is the first root entry of its name, and
its entries in order (`bktEntries`) are strictly sorted: an inline bucket's page is a good inline
page (`pageGood`), a file bucket's tree has B+tree keys (`treeKeys`, which the root's leaves carry
to their nested buckets) over sorted pages (`treeWF`), so each child's keys lie below the next
child's; hence `bktEnts` of its map is that list (`Ents.sorted_ext`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Ents
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace TreeEnts

open Ents

section treeEnts
variable [GooseExts]

theorem gs_lt_of_lt_nlt {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  by_cases h : c = b
  · subst h; exact h1
  · have : go.GoStringLt b c :=
      Classical.byContradiction fun hc => h (go.goStringLt_eq_of_not_lt h2 hc)
    exact go.goStringLt_trans h1 this

/-- The sortedness facts of a `treeOK` state's pages (`treeWF`'s). -/
theorem treeOK_pageWF (C : CommitSt) (hok : treeOK C) (id : Nat) (pg : List w8)
    (hpg : C.pages !! id = some pg) :
    (pageFlags pg = leafPageFlag → ∀ i j, i < j → j < pageCount pg →
      go.GoStringLt (leafKey pg i) (leafKey pg j)) ∧
    (pageFlags pg = branchPageFlag → ∀ i j, i < j → j < pageCount pg →
      go.GoStringLt (branchKey pg i) (branchKey pg j)) := by
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf hlw _ =>
      refine ⟨fun _ => hlw.2.2.2, fun hb => ?_⟩
      rw [hb] at hf; simp [branchPageFlag, leafPageFlag] at hf
    | branch _ _ hf hbw _ =>
      refine ⟨fun hl => ?_, fun _ => hbw.2.2.2.2⟩
      rw [hl] at hf; simp [branchPageFlag, leafPageFlag] at hf

theorem leafEnts_sorted (pg : List w8)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j)) :
    esSorted (leafEnts pg) := by
  unfold esSorted leafEnts
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj hij
  rw [List.mem_range] at hj
  exact hs i j hij hj

/-- A key within a child's bounds is within its branch's (`Read/Route`'s `keyIn_child`). -/
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

/-- The entries of a tree's leaves are within the tree's bounds. -/
theorem ents_keyIn (P : Pages) : ∀ (n id : Nat) (lo hi : Option (List w8)),
    treeKeys P id lo hi → ∀ e ∈ (leavesF n P id).flatMap leafEnts, keyIn lo hi e.1
  | 0, _, _, _, _, e, h => by simp [leavesF] at h
  | n + 1, id, lo, hi, hk, e, h => by
    cases hk with
    | leaf _ pg _ _ hpg hfl hkin _ =>
      simp only [leavesF, hpg, hfl, if_true, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at h
      unfold leafEnts at h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
      exact hkin i (List.mem_range.1 hi)
    | branch _ pg _ _ kind hpg hfl _ hkin _ hch =>
      have hnl : ¬ pageFlags pg = leafPageFlag := by
        rw [hfl]; simp [branchPageFlag, leafPageFlag]
      simp only [leavesF, hpg, hnl, if_false, List.mem_flatMap, List.mem_range] at h
      obtain ⟨pg', ⟨j, hj, hm⟩, he⟩ := h
      exact keyIn_child lo hi (branchKey pg) _ j _ hj hkin
        (ents_keyIn P n _ _ _ (hch j hj) e (List.mem_flatMap.2 ⟨pg', hm, he⟩))

/-- **A tree's entries in order are strictly sorted.** -/
theorem leavesF_sorted (C : CommitSt) (hok : treeOK C) : ∀ (n id : Nat) (lo hi : Option (List w8)),
    treeKeys C.pages id lo hi → esSorted ((leavesF n C.pages id).flatMap leafEnts)
  | 0, _, _, _, _ => by simp [leavesF, esSorted]
  | n + 1, id, lo, hi, hk => by
    cases hk with
    | leaf _ pg _ _ hpg hfl _ _ =>
      simp only [leavesF, hpg, hfl, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact leafEnts_sorted pg ((treeOK_pageWF C hok id pg hpg).1 hfl)
    | branch _ pg _ _ kind hpg hfl _ hkin _ hch =>
      have hnl : ¬ pageFlags pg = leafPageFlag := by
        rw [hfl]; simp [branchPageFlag, leafPageFlag]
      simp only [leavesF, hpg, hnl, if_false]
      rw [List.flatMap_assoc]
      unfold esSorted
      rw [List.pairwise_flatMap]
      have hbs := (treeOK_pageWF C hok id pg hpg).2 hfl
      refine ⟨fun i hi => leavesF_sorted C hok n _ _ _ (hch i (List.mem_range.1 hi)), ?_⟩
      apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
      intro i j hi hj hij e he e' he'
      rw [List.mem_range] at hi hj
      have hk1 := ents_keyIn C.pages n _ _ _ (hch i hi) e he
      have hk2 := ents_keyIn C.pages n _ _ _ (hch j hj) e' he'
      have hlt : go.GoStringLt e.1 (branchKey pg (i + 1)) := by
        have := hk1.2; unfold childHi at this; rw [if_pos (by omega)] at this; exact this _ rfl
      have hge : ¬ go.GoStringLt e'.1 (branchKey pg j) := by
        have := hk2.1; unfold childLo at this; rw [if_neg (by omega)] at this; exact this _ rfl
      have hij' : go.GoStringLt e.1 (branchKey pg j) := by
        by_cases he' : i + 1 = j
        · rw [← he']; exact hlt
        · exact go.goStringLt_trans hlt (hbs (i + 1) j (by omega) hj)
      exact gs_lt_of_lt_nlt hij' hge

/-- The leaves of a tree with B+tree keys: leaf pages of its own tree, whose nested buckets stored
in pages have B+tree keys. -/
theorem leavesF_leaf (P : Pages) : ∀ (n id : Nat) (lo hi : Option (List w8)),
    treeKeys P id lo hi → ∀ pg ∈ leavesF n P id,
      ∃ id', P !! id' = some pg ∧ ownHas P id id' ∧ pageFlags pg = leafPageFlag ∧
        ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
          inBucketRoot (leafValue pg i) ≠ 0 → treeKeys P (inBucketRoot (leafValue pg i)) none none
  | 0, _, _, _, _, pg, h => by simp [leavesF] at h
  | n + 1, id, lo, hi, hk, pg', h => by
    cases hk with
    | leaf _ pg _ _ hpg hfl _ hnest =>
      simp only [leavesF, hpg, hfl, if_true, List.mem_singleton] at h
      subst h
      exact ⟨id, hpg, ownHas.root _ _ hpg, hfl, hnest⟩
    | branch _ pg _ _ kind hpg hfl _ _ _ hch =>
      have hnl : ¬ pageFlags pg = leafPageFlag := by
        rw [hfl]; simp [branchPageFlag, leafPageFlag]
      simp only [leavesF, hpg, hnl, if_false, List.mem_flatMap, List.mem_range] at h
      obtain ⟨j, hj, hm⟩ := h
      obtain ⟨id', h1, h2, h3, h4⟩ := leavesF_leaf P n _ _ _ (hch j hj) pg' hm
      exact ⟨id', h1, ownHas.child _ pg j id' hpg hfl hj h2, h3, h4⟩

theorem ofList_mem {K V : Type} [DecidableEq K] :
    ∀ (L : List (K × V)) (k : K) (v : V), (GMap.ofList L) !! k = some v → (k, v) ∈ L
  | [], k, v, h => by
    have h0 : (GMap.ofList ([] : List (K × V))) !! k = none := rfl
    rw [h0] at h; cases h
  | (a1, a2) :: L, k, v, h => by
    simp only [GMap.ofList, GMap.lookup_insert_eq_iff] at h
    split at h
    · rename_i hk; cases h; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ofList_mem L k v h)

end treeEnts

end TreeEnts

open TreeEnts Ents in
/-- **`bktEnts_treeEntries`** (`Model/TreeData`), proved: in a `treeOK` state, the bucket `n` of
`treeData C` is the bucket of a root entry `n`, and its `bktEnts` are that bucket's leaves' entries
in order. -/
theorem bktEnts_treeEntries' [GooseExts] (C : CommitSt) (hok : treeOK C) (n : GoString)
    (m : BktData) (hn : treeData C !! n = some m) :
    ∃ v, (n, v) ∈ treeEntries C.pages C.root ∧ m = bktOfPage C.pages v ∧
      bktEnts m = bktEntries C.pages v := by
  unfold treeData at hn
  obtain ⟨e, he, hee⟩ := List.mem_map.1 (ofList_mem _ _ _ hn)
  simp only [Prod.mk.injEq] at hee
  obtain ⟨rfl, rfl⟩ := hee
  refine ⟨e.2, he, rfl, ?_⟩
  have hS : esSorted (bktEntries C.pages e.2) := by
    unfold treeEntries treeLeaves at he
    obtain ⟨pg, hpg, hx⟩ := List.mem_flatMap.1 he
    obtain ⟨id', hid, hown, hfl, hnest⟩ := leavesF_leaf C.pages _ _ _ _ hok.1.2.2.1 pg hpg
    obtain ⟨i, hi, hei⟩ : ∃ i < pageCount pg, (leafKey pg i, leafValue pg i) = e := by
      unfold leafEnts at hx
      obtain ⟨i, hi, h⟩ := List.mem_map.1 hx
      exact ⟨i, List.mem_range.1 hi, h⟩
    subst hei
    have hbf : leafFlags pg i % 2 = bucketLeafFlag := (hok.2.2.2.2.1 id' pg hown hid hfl i hi).1
    unfold bktEntries bktLeaves
    by_cases h0 : inBucketRoot (leafValue pg i) = 0
    · rw [if_pos h0]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hg := ((hok.1.2.1.1 id' pg hid).1 hfl i hi).2 hbf h0
      exact leafEnts_sorted _ hg.2.2.1.2.2.2
    · rw [if_neg h0]
      unfold treeLeaves
      exact leavesF_sorted C hok _ _ _ _ (hnest i hi hbf h0)
  have hnd : (bktEntries C.pages e.2).Pairwise (fun a b => a.1 ≠ b.1) :=
    hS.imp (fun hab heq => by rw [heq] at hab; exact go.goStringLt_irrefl _ hab)
  unfold bktOfPage
  apply sorted_ext _ _ (bktEnts_sorted _) hS
  intro x
  rw [mem_bktEnts, ofList_lookup_iff _ hnd]
