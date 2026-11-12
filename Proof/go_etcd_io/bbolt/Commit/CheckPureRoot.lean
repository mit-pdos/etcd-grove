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
public import Proof.go_etcd_io.bbolt.Read.TreeEnts
public import Proof.go_etcd_io.bbolt.Txn.WInit
public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov
public import Proof.go_etcd_io.bbolt.Spill.STree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

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
theorem top_entry_mem (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : (kb, cv) ∈ treeEntries v.pages v.root := by
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
  unfold treeEntries
  refine List.mem_flatMap.mpr ⟨pg, hpg, ?_⟩
  unfold leafEnts
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, by rw [hk, hv]⟩

theorem top_entries (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) : ∃ n, (n, cv) ∈ treeEntries v.pages v.root :=
  ⟨kb, top_entry_mem v h kb cv he⟩

/-- A name of the root bucket names one top-level bucket. -/
theorem top_entry_unique (v : View) (h : viewWF v) (kb cv cv' : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (he' : bktEntry v.pages (rootVal v) kb cv') :
    cv = cv' := by
  have hm := top_entry_mem v h kb cv he
  have hm' := top_entry_mem v h kb cv' he'
  obtain ⟨C, hok, hvC⟩ := h
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  rw [hpv, hrv] at hm hm'
  have hs : Ents.esSorted (treeEntries C.pages C.root) :=
    TreeEnts.leavesF_sorted C hok _ _ none none hok.1.2.2.1
  unfold Ents.esSorted at hs
  clear hvC hpv hrv
  generalize treeEntries C.pages C.root = l at hm hm' hs
  induction l with
  | nil => simp at hm
  | cons e t ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hm with rfl | hm1 <;> rcases List.mem_cons.mp hm' with he2 | hm2
    · simp only [Prod.mk.injEq] at he2; exact he2.2.symm
    · exact absurd (hs.1 _ hm2) (go.goStringLt_irrefl _)
    · subst he2; exact absurd (hs.1 _ hm1) (go.goStringLt_irrefl _)
    · exact ih hm1 hm2 hs.2

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

/-- A well-formed view is a `treeOK` state's pages and root. -/
theorem viewWF_C (v : View) (h : viewWF v) :
    ∃ C, treeOK C ∧ v.pages = C.pages ∧ v.root = C.root := by
  obtain ⟨C, hok, hvC⟩ := h
  exact ⟨C, hok, by rw [← hvC]; rfl, by rw [← hvC]; rfl⟩

/-- The view's root is a 64-bit page id, not 0. -/
theorem root_lt (v : View) (h : viewWF v) : v.root < 2 ^ 64 ∧ v.root ≠ 0 := by
  obtain ⟨C, hok, -, hrv⟩ := viewWF_C v h
  rw [hrv]
  cases hok.1.1 with
  | page _ pg h2 _ hpg hid _ _ =>
    refine ⟨?_, by omega⟩
    rw [← hid]; unfold pageId; exact BitVec.isLt _

/-- The root bucket's leaves are its tree's. -/
private theorem bktLeaves_rootVal (v : View) (h : viewWF v) :
    bktLeaves v.pages (rootVal v) = treeLeaves v.pages v.root := by
  obtain ⟨hl, h0⟩ := root_lt v h
  have hr : inBucketRoot (rootVal v) = v.root := (rootVal_root v hl).1
  unfold bktLeaves
  rw [if_neg (by rw [hr]; exact h0), hr]

/-- A top-level bucket is an element of an own leaf of the root. -/
theorem top_entry_own (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) :
    ∃ L pg i, ownHas v.pages v.root L ∧ v.pages !! L = some pg ∧ pageFlags pg = leafPageFlag ∧
      i < pageCount pg ∧ leafFlags pg i % 2 = bucketLeafFlag ∧ leafKey pg i = kb ∧
      leafValue pg i = cv := by
  obtain ⟨pg, i, hpg, hi, hk, hf, hv⟩ := he
  rw [bktLeaves_rootVal v h] at hpg
  obtain ⟨C, hok, hpv, hrv⟩ := viewWF_C v h
  rw [hpv, hrv] at hpg ⊢
  unfold treeLeaves at hpg
  obtain ⟨L, -, -, ho, hL, hfl, -, -⟩ :=
    leavesF_page C.pages C.hwm _ _ none none hok.1.1 hok.1.2.2.1 pg hpg
  exact ⟨L, pg, i, ho, hL, hfl, hi, hf, hk, hv⟩

/-- A bucket element of an own leaf of the root is a top-level bucket. -/
theorem own_top_entry (v : View) (h : viewWF v) {L : Nat} {pg : List w8} {i : Nat}
    (ho : ownHas v.pages v.root L) (hL : v.pages !! L = some pg) (hfl : pageFlags pg = leafPageFlag)
    (hi : i < pageCount pg) (hbf : leafFlags pg i % 2 = bucketLeafFlag) :
    bktEntry v.pages (rootVal v) (leafKey pg i) (leafValue pg i) ∧
      leafKey pg i ∈ bktNames v.pages (rootVal v) := by
  have hmem : pg ∈ bktLeaves v.pages (rootVal v) := by
    rw [bktLeaves_rootVal v h]
    obtain ⟨C, hok, hpv, hrv⟩ := viewWF_C v h
    have hlt := (root_lt v h).1
    rw [hpv, hrv] at ho; rw [hpv] at hL; rw [hrv] at hlt; rw [hpv, hrv]
    unfold treeLeaves
    exact leavesF_of_own C v.base hok ho pg hL hfl _ hlt
      (Nat.lt_succ_of_le (Write.treeMeasure_le _ _))
  refine ⟨⟨pg, i, hmem, hi, rfl, hbf, rfl⟩, ?_⟩
  unfold bktNames
  exact List.mem_flatMap.mpr ⟨pg, hmem, List.mem_map.mpr
    ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [hbf]⟩, rfl⟩⟩

omit [GooseExts] in
private theorem flatMap_sublist' {α β : Type} {f g : α → List β} (h : ∀ a, List.Sublist (f a) (g a)) :
    ∀ l : List α, List.Sublist (l.flatMap f) (l.flatMap g)
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons]
    exact (h a).append (flatMap_sublist' h l)

/-- The root bucket's names are distinct. -/
theorem names_nodup (v : View) (h : viewWF v) :
    (bktNames v.pages (rootVal v)).Pairwise (· ≠ ·) := by
  obtain ⟨C, hok, hpv, hrv⟩ := viewWF_C v h
  have hs : Ents.esSorted (treeEntries C.pages C.root) :=
    TreeEnts.leavesF_sorted C hok _ _ none none hok.1.2.2.1
  unfold Ents.esSorted at hs
  have hs' : ((treeEntries C.pages C.root).map Prod.fst).Pairwise (fun a b => go.GoStringLt a b) :=
    List.pairwise_map.mpr hs
  have hsub : List.Sublist (bktNames v.pages (rootVal v))
      ((treeEntries C.pages C.root).map Prod.fst) := by
    unfold bktNames treeEntries
    rw [bktLeaves_rootVal v h, hpv, hrv, List.map_flatMap]
    apply flatMap_sublist'
    intro pg
    unfold leafEnts
    rw [List.map_map]
    exact (List.filter_sublist).map _
  exact (hs'.sublist hsub).imp fun hab he => by
    subst he; exact go.goStringLt_irrefl _ hab

/-- The root's own pages are not in a top-level bucket's tree. -/
theorem top_disj_root (v : View) (h : viewWF v) (kb cv : List w8)
    (he : bktEntry v.pages (rootVal v) kb cv) (hf : inBucketRoot cv ≠ 0) (x : Nat)
    (hx : ownSlot v.pages (inBucketRoot cv) x) : ¬ ownSlot v.pages v.root x := by
  rintro ⟨id2, q2, hq2o, hq2, hx2a, hx2b⟩
  obtain ⟨C, hok, hpv, -⟩ := viewWF_C v h
  have hu : viewUnique v.pages := by rw [hpv]; exact hok.1.2.1.2
  have hd : pagesDisjoint v.pages := by rw [hpv]; exact hok.2.2.1
  obtain ⟨L1, pg1, i1, ho1, hL1, hl1, hi1, hb1, -, hv1⟩ := top_entry_own v h kb cv he
  obtain ⟨id1, q1, hq1o, hq1, hx1a, hx1b⟩ := hx
  by_cases hid : id1 = id2
  · subst hid
    exact own_not_bucket v.pages hu hq2o ho1 hL1 hl1 hi1 hb1
      (by rw [hv1]; exact bucketHas.file _ _ hf (ownHas_treeHas' hq1o))
  · rcases hd id1 q1 id2 q2 hq1 hq2 hid with h1 | h1 <;> omega

/-- **The `i`-th top-level bucket's own pages are not an earlier one's.** -/
theorem top_disj_prev (v : View) (h : viewWF v) (i : Nat) (kb cv : List w8)
    (hi : (bktNames v.pages (rootVal v))[i]? = some kb) (he : bktEntry v.pages (rootVal v) kb cv)
    (hf : inBucketRoot cv ≠ 0) (x : Nat) (hx : ownSlot v.pages (inBucketRoot cv) x) :
    ¬ chSlot v i x := by
  rintro ⟨j, hj, kb', cv', hj', he', hf', hx'⟩
  obtain ⟨C, hok, hpv, -⟩ := viewWF_C v h
  have hu : viewUnique v.pages := by rw [hpv]; exact hok.1.2.1.2
  have hd : pagesDisjoint v.pages := by rw [hpv]; exact hok.2.2.1
  obtain ⟨L1, pg1, i1, ho1, hL1, hl1, hi1, hb1, hk1, hv1⟩ := top_entry_own v h kb cv he
  obtain ⟨L2, pg2, i2, ho2, hL2, hl2, hi2, hb2, hk2, hv2⟩ := top_entry_own v h kb' cv' he'
  obtain ⟨id1, q1, hq1o, hq1, hx1a, hx1b⟩ := hx
  obtain ⟨id2, q2, hq2o, hq2, hx2a, hx2b⟩ := hx'
  by_cases hid : id1 = id2
  · subst hid
    have hd1 : bucketHas v.pages (leafValue pg1 i1) id1 := by
      rw [hv1]; exact bucketHas.file _ _ hf (ownHas_treeHas' hq1o)
    have hd2 : bucketHas v.pages (leafValue pg2 i2) id1 := by
      rw [hv2]; exact bucketHas.file _ _ hf' (ownHas_treeHas' hq2o)
    obtain ⟨rfl, rfl⟩ := bucket_unique v.pages hu ho1 ho2 hL1 hl1 hi1 hb1 hL2 hl2 hi2 hb2 hd1 hd2
    rw [hL1] at hL2; cases hL2
    have hkk : kb = kb' := hk1.symm.trans hk2
    subst hkk
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj'
    exact List.pairwise_iff_getElem.mp (names_nodup v h) j i hjl hil hj (hje.trans hie.symm)
  · rcases hd id1 q1 id2 q2 hq1 hq2 hid with h1 | h1 <;> omega

/-- **The root's and the top-level buckets' own pages cover the view's slots.** -/
theorem root_cover (v : View) (h : viewWF v) (x : Nat) :
    (ownSlot v.pages v.root x ∨ chSlot v (bktNames v.pages (rootVal v)).length x) ↔
      coversSlot v.pages x := by
  constructor
  · rintro (⟨id, pg, -, hpg, h1, h2⟩ | ⟨-, -, -, -, -, -, -, id, pg, -, hpg, h1, h2⟩) <;>
      exact ⟨id, pg, hpg, h1, by omega⟩
  · rintro ⟨id, pg, hpg, h1, h2⟩
    obtain ⟨C, hok, hpv, hrv⟩ := viewWF_C v h
    have hsh : rootShape v.pages v.root := by rw [hpv, hrv]; exact hok.2.2.2.2.1
    have hgood : ∀ id pg, v.pages !! id = some pg → pageGood pg := by
      rw [hpv]; exact hok.1.2.1.1
    have ht : treeHas v.pages v.root id := by
      have hl := Spill.treePages_lookup C.pages C.root id
      rw [hok.2.1] at hl
      rw [hpv, hrv]
      refine Classical.byContradiction fun hn => ?_
      rw [if_neg hn, ← hpv, hpg] at hl
      cases hl
    rcases treeHas_split v.pages ht with ho | ⟨L, pgL, i, hL, hpgL, hl, hi, hbf, hb⟩
    · exact .inl ⟨id, pg, ho, hpg, h1, by omega⟩
    · cases hb with
      | file _ _ h0 htr =>
        have own : ownHas v.pages (inBucketRoot (leafValue pgL i)) id := by
          refine Spill.ownHas_of_treeHas (fun p q hp hq hql j hj => ?_) htr
          have := ((hsh L pgL hL hpgL hl i hi).2.2.2 q (.inr ⟨h0, p, hp, hq, hql⟩) j hj).1
          rw [this]; decide
        obtain ⟨hent, hmem⟩ := own_top_entry v h hL hpgL hl hi hbf
        obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem hmem
        exact .inr ⟨j, hj, _, _, List.getElem?_eq_some_iff.mpr ⟨hj, hjn⟩, hent, h0,
          id, pg, own, hpg, h1, by omega⟩
      | inline _ _ h0 hph =>
        exfalso
        cases hph with
        | child _ k _ hfl _ _ =>
          have := ((hgood L pgL hpgL).1 hl i hi).2 hbf h0
          rw [this.2.1] at hfl; exact absurd hfl (by decide)
        | bucket _ k _ _ hk hbk _ =>
          have := ((hsh L pgL hL hpgL hl i hi).2.2.2 _ (.inl ⟨h0, rfl⟩) k hk).1
          rw [this] at hbk; exact absurd hbk (by decide)

end pure

end bbolt
end EtcdGrove
end Perennial
