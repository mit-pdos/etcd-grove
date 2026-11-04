/-
The public reads' (U6g, `notes/bbolt-proof-plan.md`) pure facts over a reader's top-level bucket:
the bucket `n` of a well-formed view's data is the bucket of its root entry `n` (`rd_bkt_data`),
whose entries are sorted and plain (`rootShape`: a top-level bucket holds no nested bucket); a key
looked up in it is the entry at its search index in the only leaf that can hold it
(`rd_get_lookup`, `Bucket.Get`'s result).
-/
module

public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Proof.go_etcd_io.bbolt.Read.TreeEnts
public import Proof.go_etcd_io.bbolt.Read.Pos

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section getFacts
variable [GooseExts]

open Ents in
/-- In a strictly sorted entry list, two entries of one key are one. -/
theorem esSorted_key_inj : ∀ (l : List BoltEnt), esSorted l → ∀ a b, a ∈ l → b ∈ l → a.1 = b.1 →
    a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: t, h, a, b, ha, hb, hab => by
    unfold esSorted at h
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · have := h.1 b hb'; rw [hab] at this; exact absurd this (go.goStringLt_irrefl _)
    · rcases List.mem_cons.1 hb with rfl | hb'
      · have := h.1 a ha'; rw [hab] at this; exact absurd this (go.goStringLt_irrefl _)
      · exact esSorted_key_inj t h.2 a b ha' hb' hab

/-- The root bucket's leaves are the root tree's (the view's root page is never `0`). -/
theorem bktLeaves_rootVal (v : View) (hv : viewWF v) :
    bktLeaves v.pages (rootVal v) = treeLeaves v.pages v.root := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  obtain ⟨⟨hw, -⟩, -⟩ := hok
  have hroot : inBucketRoot (rootVal v) = C.root := by
    rw [inBucketRoot_rootVal, hrv]
    cases hw with
    | page _ pg _ _ hpg hid _ _ =>
      have : C.root < 2 ^ 64 := by rw [← hid]; unfold pageId; exact BitVec.isLt _
      omega
  have hr0 : C.root ≠ 0 := by cases hw with | page _ _ h2 _ _ _ _ _ => omega
  unfold bktLeaves
  rw [hroot, if_neg hr0, hrv]

open Ents TreeEnts in
/-- **A reader's top-level bucket `n`** (its root entry `n` of value `bv`, `boltBkt`'s
`bktEntry`): `n`'s data in the view is that bucket's, a root entry; its entries are sorted. -/
theorem rd_bkt_data (v : View) (hv : viewWF v) (n : GoString) (bv : List w8) (m : BktData)
    (hbe : bktEntry v.pages (rootVal v) n bv) (hm : v.data !! n = some m) :
    (n, bv) ∈ treeEntries v.pages v.root ∧ m = bktOfPage v.pages bv ∧
      esSorted (bktEntries v.pages bv) := by
  have hlv := bktLeaves_rootVal v hv
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  have hd : v.data = treeData C := by unfold View.data treeData; rw [hpv, hrv]
  rw [hd] at hm
  obtain ⟨bv', hmem', hm', hents⟩ := bktEnts_treeEntries' C hok n m hm
  have hmem : (n, bv) ∈ treeEntries v.pages v.root := by
    obtain ⟨pg, i, hpg, hi, hk, -, hval⟩ := hbe
    rw [hlv] at hpg
    unfold treeEntries
    refine List.mem_flatMap.2 ⟨pg, hpg, ?_⟩
    unfold leafEnts
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, by rw [hk, hval]⟩
  have hsorted : esSorted (treeEntries C.pages C.root) :=
    leavesF_sorted C hok _ _ _ _ hok.1.2.2.1
  rw [hpv, hrv] at hmem
  have heq := esSorted_key_inj _ hsorted _ _ hmem hmem' rfl
  simp only [Prod.mk.injEq, true_and] at heq
  subst heq
  refine ⟨by rw [hpv, hrv]; exact hmem, by rw [hpv]; exact hm', ?_⟩
  rw [hpv, ← hents]; exact bktEnts_sorted m

/-- **A top-level bucket's entries are plain** (`rootShape`: no nested bucket below a top-level
one). -/
theorem rd_top_plain (v : View) (hv : viewWF v) (n : GoString) (bv : List w8)
    (hn : (n, bv) ∈ treeEntries v.pages v.root) (pg : List w8) (hpg : pg ∈ bktLeaves v.pages bv)
    (i : Nat) (hi : i < pageCount pg) : leafFlags pg i % 2 = 0 := by
  have hok := rBktOK_of v hv bv (Or.inr ⟨n, hn⟩)
  obtain ⟨C, hokC, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  unfold rBktOK rTree at hok
  rw [hpv] at hok hpg
  rw [hpv, hrv] at hn
  obtain ⟨⟨hw, -, hk, -⟩, -, -, -, hshape, -⟩ := hokC
  unfold treeEntries treeLeaves at hn
  obtain ⟨rpg, hrpg, hent⟩ := List.mem_flatMap.mp hn
  obtain ⟨rid, -, -, hro, hrpid, hrfl, -, -⟩ :=
    leavesF_page C.pages C.hwm _ _ _ _ hw hk rpg hrpg
  unfold leafEnts at hent
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hent
  rw [List.mem_range] at hj
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  have hsh := (hshape rid rpg hro hrpid hrfl j hj).2.2.2 pg
  have hbl : bktLeafPg C.pages (leafValue rpg j) pg := by
    obtain ⟨-, ht, hkk⟩ := hok
    unfold bktLeaves at hpg
    by_cases h0 : inBucketRoot (leafValue rpg j) = 0
    · rw [if_pos h0, List.mem_singleton] at hpg
      exact Or.inl ⟨h0, hpg⟩
    · rw [if_neg h0] at hpg
      rcases ht with ⟨h0', _⟩ | ⟨_, hwm, htw⟩
      · exact absurd h0' h0
      obtain ⟨id', lo', hi', ho, hpid, hfl, -, -⟩ :=
        leavesF_page C.pages hwm _ _ _ _ htw (hkk h0) pg hpg
      exact Or.inr ⟨h0, id', ho, hpid, hfl⟩
  exact (hsh hbl i hi).1

open Ents TreeEnts in
/-- **A key's lookup in a bucket**: the entry at its search index of the only leaf that can hold
it, if that entry's key is the key; else none. -/
theorem rd_get_lookup (P : Pages) (bv : List w8) (hS : esSorted (bktEntries P bv)) (k : List w8)
    (pg : List w8) (hpg : pg ∈ bktLeaves P bv)
    (hmem : ∀ pg' ∈ bktLeaves P bv, ∀ i < pageCount pg', leafKey pg' i = k → pg' = pg)
    (hwf : leafWF pg pg.length) :
    (bktOfPage P bv) !! k =
      if pageSeekIdx pg k < pageCount pg ∧ leafKey pg (pageSeekIdx pg k) = k then
        some (leafValue pg (pageSeekIdx pg k))
      else none := by
  have hnd : (bktEntries P bv).Pairwise (fun a b => a.1 ≠ b.1) :=
    hS.imp (fun hab heq => by rw [heq] at hab; exact go.goStringLt_irrefl _ hab)
  unfold bktOfPage
  split
  · rename_i hf
    rw [ofList_lookup_iff _ hnd]
    unfold bktEntries
    refine List.mem_flatMap.2 ⟨pg, hpg, ?_⟩
    unfold leafEnts
    exact List.mem_map.2 ⟨pageSeekIdx pg k, List.mem_range.2 hf.1, by rw [hf.2]⟩
  · rename_i hf
    rcases h : (GMap.ofList (bktEntries P bv)) !! k with _ | x
    · rfl
    · exfalso
      have hx := (ofList_lookup_iff _ hnd k x).1 h
      unfold bktEntries at hx
      obtain ⟨pg', hpg', hx⟩ := List.mem_flatMap.1 hx
      unfold leafEnts at hx
      obtain ⟨i, hi, hix⟩ := List.mem_map.1 hx
      rw [List.mem_range] at hi
      simp only [Prod.mk.injEq] at hix
      have he := hmem pg' hpg' i hi hix.1
      subst he
      have hsi := pageSeekIdx_of_key pg' _ hwf i hi k hix.1
      exact hf ⟨by rw [hsi]; exact hi, by rw [hsi]; exact hix.1⟩

open TreeEnts in
/-- **A name no nested bucket of the root has is no bucket of the view's data** (`Tx.Bucket`'s
miss). -/
theorem rd_root_lookup_none (v : View) (hv : viewWF v) (n : GoString)
    (hn : n ∉ bktNames v.pages (rootVal v)) : v.data !! n = none := by
  have hlv := bktLeaves_rootVal v hv
  rcases h : v.data !! n with _ | x
  · rfl
  · exfalso
    unfold View.data at h
    obtain ⟨e, he, hee⟩ := List.mem_map.1 (ofList_mem _ _ _ h)
    simp only [Prod.mk.injEq] at hee
    obtain ⟨rfl, -⟩ := hee
    apply hn
    obtain ⟨C, hok, hvC⟩ := hv
    have hpv : v.pages = C.pages := by rw [← hvC]; rfl
    have hrv : v.root = C.root := by rw [← hvC]; rfl
    unfold treeEntries at he
    obtain ⟨pg, hpg, hx⟩ := List.mem_flatMap.1 he
    unfold leafEnts at hx
    obtain ⟨i, hi, hei⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    unfold bktNames
    refine List.mem_flatMap.2 ⟨pg, by rw [hlv]; exact hpg, ?_⟩
    refine List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩, by rw [← hei]⟩
    rw [hpv, hrv] at hpg
    unfold treeLeaves at hpg
    obtain ⟨id', hid, hown, hfl, -⟩ := leavesF_leaf C.pages _ _ _ _ hok.1.2.2.1 pg hpg
    simp only [decide_eq_true_eq]
    exact (hok.2.2.2.2.1 id' pg hown hid hfl i hi).1

open Ents TreeEnts in
/-- **A nested bucket of the root is a bucket of the view's data** (`Tx.Bucket`'s hit). -/
theorem rd_root_lookup_some (v : View) (hv : viewWF v) (n : GoString) (cv : List w8)
    (hbe : bktEntry v.pages (rootVal v) n cv) : v.data !! n ≠ none := by
  have hlv := bktLeaves_rootVal v hv
  have hmem : (n, cv) ∈ treeEntries v.pages v.root := by
    obtain ⟨pg, i, hpg, hi, hk, -, hval⟩ := hbe
    rw [hlv] at hpg
    unfold treeEntries
    refine List.mem_flatMap.2 ⟨pg, hpg, ?_⟩
    unfold leafEnts
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, by rw [hk, hval]⟩
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  have hsorted : esSorted (treeEntries C.pages C.root) :=
    leavesF_sorted C hok _ _ _ _ hok.1.2.2.1
  rw [← hpv, ← hrv] at hsorted
  have hnd : ((treeEntries v.pages v.root).map fun e => (e.1, bktOfPage v.pages e.2)).Pairwise
      (fun a b => a.1 ≠ b.1) := by
    rw [List.pairwise_map]
    exact hsorted.imp (fun hab heq => by rw [heq] at hab; exact go.goStringLt_irrefl _ hab)
  intro h
  unfold View.data at h
  have := (ofList_lookup_iff _ hnd n (bktOfPage v.pages cv)).2
    (List.mem_map.2 ⟨(n, cv), hmem, rfl⟩)
  rw [h] at this; cases this

open Ents TreeEnts in
/-- **A reader's top-level bucket's entries in order** (`boltCur`'s `es`): its leaves' entries. -/
theorem rd_bktEnts (v : View) (hv : viewWF v) (n : GoString) (bv : List w8) (m : BktData)
    (hbe : bktEntry v.pages (rootVal v) n bv) (hm : v.data !! n = some m) :
    bktEnts m = bktEntries v.pages bv := by
  obtain ⟨-, rfl, hS⟩ := rd_bkt_data v hv n bv m hbe hm
  have hnd : (bktEntries v.pages bv).Pairwise (fun a b => a.1 ≠ b.1) :=
    hS.imp (fun hab heq => by rw [heq] at hab; exact go.goStringLt_irrefl _ hab)
  unfold bktOfPage
  apply sorted_ext _ _ (bktEnts_sorted _) hS
  intro x
  rw [mem_bktEnts, ofList_lookup_iff _ hnd]

/-- **The entries a reader's cursor positions name** (`rEnts`, as (leaf, index) pairs) are the
bucket's entries (`bktEntries`) read at those pairs. -/
theorem rEnts_bktEntries (v : View) (bv : List w8) :
    (rEnts v bv).map (fun x => (leafKey x.1 x.2, leafValue x.1 x.2)) = bktEntries v.pages bv := by
  unfold rEnts bktEntries lEnts leafEnts
  rw [List.map_flatMap]
  congr 1
  funext pg
  rw [List.map_map]
  rfl

/-- A cursor position on an entry names the bucket's entry there. -/
theorem rEnts_get (v : View) (bv : List w8) (i : Nat) (pg : List w8) (idx : Nat)
    (h : (rEnts v bv)[i]? = some (pg, idx)) :
    (bktEntries v.pages bv)[i]? = some (leafKey pg idx, leafValue pg idx) := by
  rw [← rEnts_bktEntries, List.getElem?_map, h]
  rfl

/-- The position past a cursor's last entry is past the bucket's last entry. -/
theorem rEnts_length (v : View) (bv : List w8) :
    (bktEntries v.pages bv).length = (rEnts v bv).length := by
  rw [← rEnts_bktEntries, List.length_map]

end getFacts

end bbolt
end EtcdGrove
end Perennial
