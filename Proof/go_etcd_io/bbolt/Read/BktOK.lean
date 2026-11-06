/-
The read path's (U6, `notes/bbolt-proof-plan.md`) well-formed reader buckets: the root bucket and
the top-level buckets of a well-formed view have well-formed trees with B+tree keys (`rBktOK`), so
that a route from their root ends at their only leaf that can hold the key (`rRoute_bkt`); with
the height bound that makes `bktLeaves`' fuel enough (`pht_lt_size`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Route
public import Proof.go_etcd_io.bbolt.Read.Search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section bkt
variable [GooseExts]

/-- A chain of distinct pages below a well-formed position, as long as its height. -/
theorem pht_chain (P : Pages) (hwm : Nat) (pht : Nat → Nat) (hht : pageHts P pht) :
    ∀ (m id : Nat), pht id = m → treeWF P hwm id →
      ∃ L : List Nat, L.Nodup ∧ (∀ x ∈ L, (P !! x).isSome) ∧ L.length = pht id + 1 ∧
        ∀ x ∈ L, pht x ≤ pht id := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro id hm hw
  cases hw with
  | page _ pg _ _ hpg _ _ hpt =>
    cases hpt with
    | leaf _ _ hfl _ _ =>
      refine ⟨[id], by simp, by simp [hpg], ?_, by simp⟩
      simp [(hht id pg hpg).1 hfl]
    | branch _ _ hfl hbwf hch =>
      have hc := (hht id pg hpg).2 hfl 0 hbwf.1
      obtain ⟨L, hnd, hin, hlen, hle⟩ := ih (pht (branchPgid pg 0)) (by omega) _ rfl (hch 0 hbwf.1)
      refine ⟨id :: L, List.nodup_cons.mpr ⟨fun h => by have := hle id h; omega, hnd⟩, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [hpg]
        · exact hin x hx
      · simp [hlen]; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · have := hle x hx; omega

/-- **A well-formed position's height is below the page count** (the leaves' fuel suffices). -/
theorem pht_lt_size (P : Pages) (hwm : Nat) (pht : Nat → Nat) (hht : pageHts P pht) (id : Nat)
    (hw : treeWF P hwm id) : pht id < P.size + 1 := by
  obtain ⟨L, hnd, hin, hlen, -⟩ := pht_chain P hwm pht hht _ id rfl hw
  have := List.Nodup.length_le_of_subset hnd
    (fun x hx => (GMap.mem_dom_list P x).mpr (hin x hx))
  rw [← GMap.size_eq_dom_list_length] at this
  omega

/-- A leaf of a well-formed tree with B+tree keys is one of its pages: its leaf clauses. -/
theorem leavesF_page (P : Pages) (hwm : Nat) :
    ∀ (n id : Nat) (lo hi : Option (List w8)), treeWF P hwm id → treeKeys P id lo hi →
      ∀ pg ∈ leavesF n P id, ∃ id' lo' hi', ownHas P id id' ∧ P !! id' = some pg ∧
        pageFlags pg = leafPageFlag ∧ pageTreeWF P hwm pg pg.length ∧ treeKeys P id' lo' hi'
  | 0, _, _, _, _, _, pg, h => by simp [leavesF] at h
  | n + 1, id, lo, hi, hw, hk, pg', h => by
    cases hw with
    | page _ pg _ _ hpg _ _ hpt =>
      by_cases hfl : pageFlags pg = leafPageFlag
      · simp only [leavesF, hpg, hfl, if_true, List.mem_singleton] at h
        subst h
        exact ⟨id, lo, hi, ownHas.root id pg' hpg, hpg, hfl, hpt, hk⟩
      · simp only [leavesF, hpg, hfl, if_false, List.mem_flatMap, List.mem_range] at h
        obtain ⟨j, hj, hm⟩ := h
        cases hpt with
        | leaf _ _ hf _ _ => exact absurd hf hfl
        | branch _ _ hfb _ hch =>
          cases hk with
          | leaf _ pg3 _ _ hpg3 hf3 _ _ =>
            rw [hpg] at hpg3; cases hpg3; exact absurd hf3 hfl
          | branch _ pg3 _ _ kind hpg3 _ _ _ _ hkch =>
            rw [hpg] at hpg3; cases hpg3
            obtain ⟨id', lo', hi', ho, h2⟩ :=
              leavesF_page P hwm n _ _ _ (hch j hj) (hkch j hj) pg' hm
            exact ⟨id', lo', hi', ownHas.child id pg j id' hpg hfb hj ho, h2⟩

/-- **A reader bucket whose search is correct**: its value's header, a well-formed tree at its
root, B+tree keys when stored in pages. -/
def rBktOK (v : View) (bv : List w8) : Prop :=
  16 ≤ bv.length ∧ rTree v bv (inBucketRoot bv) ∧
    (inBucketRoot bv ≠ 0 → treeKeys v.pages (inBucketRoot bv) none none)

theorem inBucketRoot_rootVal (v : View) : inBucketRoot (rootVal v) = v.root % 2 ^ 64 := by
  unfold inBucketRoot inBucketOf rootVal bytesAt
  rw [List.drop_zero, List.take_of_length_le (by simp), ByteEncoding.decode_encode]
  simp

theorem rootVal_length (v : View) : (rootVal v).length = 16 := by
  unfold rootVal; simp

/-- **The root bucket and the top-level buckets of a well-formed view are `rBktOK`.** -/
theorem rBktOK_of (v : View) (hv : viewWF v) (bv : List w8)
    (h : bv = rootVal v ∨ ∃ n, (n, bv) ∈ treeEntries v.pages v.root) : rBktOK v bv := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  obtain ⟨⟨hw, -, hk, -⟩, -, -, -, hshape, -⟩ := hok
  unfold rBktOK rTree
  rw [hpv]
  rw [hpv, hrv] at h
  rcases h with rfl | ⟨n, hn⟩
  · have hroot : inBucketRoot (rootVal v) = C.root := by
      rw [inBucketRoot_rootVal, hrv]
      cases hw with
      | page _ pg _ _ hpg hid _ _ =>
        have : C.root < 2 ^ 64 := by rw [← hid]; unfold pageId; exact BitVec.isLt _
        omega
    have hr0 : C.root ≠ 0 := by cases hw with | page _ _ h2 _ _ _ _ _ => omega
    refine ⟨by simp [rootVal_length], ?_, ?_⟩
    · rw [hroot]; exact Or.inr ⟨hr0, C.hwm, hw⟩
    · rw [hroot]; intro; exact hk
  · unfold treeEntries treeLeaves at hn
    obtain ⟨pg, hpg, hent⟩ := List.mem_flatMap.mp hn
    obtain ⟨id', lo', hi', ho, hpid, hfl, hpt, hk'⟩ :=
      leavesF_page C.pages C.hwm _ _ _ _ hw hk pg hpg
    unfold leafEnts at hent
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hent
    rw [List.mem_range] at hi
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have hbf := (hshape id' pg ho hpid hfl i hi).1
    have hbw : bucketWF C.pages C.hwm (leafValue pg i) := by
      cases hpt with
      | leaf _ _ _ _ hb => exact hb i hi hbf
      | branch _ _ hf _ _ => rw [hfl] at hf; simp [branchPageFlag, leafPageFlag] at hf
    have hkb : inBucketRoot (leafValue pg i) ≠ 0 →
        treeKeys C.pages (inBucketRoot (leafValue pg i)) none none := by
      cases hk' with
      | leaf _ pg3 _ _ hpg3 _ _ hkb =>
        rw [hpid] at hpg3; cases hpg3; exact hkb i hi hbf
      | branch _ pg3 _ _ _ hpg3 hf3 _ _ _ _ =>
        rw [hpid] at hpg3; cases hpg3; rw [hfl] at hf3; simp [branchPageFlag, leafPageFlag] at hf3
    cases hbw with
    | file _ h16 hr0 htw => exact ⟨h16, Or.inr ⟨hr0, C.hwm, htw⟩, hkb⟩
    | inline _ h16 hr0 hfi hpti =>
      refine ⟨h16, Or.inl ⟨hr0, hr0, hfi, ?_⟩, fun h => absurd hr0 h⟩
      cases hpti with
      | leaf _ _ _ hl _ => exact hl
      | branch _ _ hf _ _ => rw [hfi] at hf; simp [branchPageFlag, leafPageFlag] at hf

/-- **A route from an `rBktOK` bucket's root ends at its only leaf that can hold the key.** -/
theorem rRoute_bkt (v : View) (hv : viewWF v) (bv : List w8) (hok : rBktOK v bv) (pp : Loc)
    (k : List w8) (path : List elemRef) (hr : rRoute v bv pp k (inBucketRoot bv) path) :
    rRouteEnd v bv pp k path (bktLeaves v.pages bv) := by
  obtain ⟨-, ht, hk⟩ := hok
  unfold bktLeaves
  by_cases hi : inBucketRoot bv = 0
  · rw [if_pos hi]
    rw [hi] at hr ht
    exact rRoute_inline v bv pp k hi ht path hr
  · rw [if_neg hi]
    rcases ht with ⟨h, _⟩ | ⟨_, hwm, hw⟩
    · exact absurd h hi
    obtain ⟨C, hok, hvC⟩ := hv
    have hpv : v.pages = C.pages := by rw [← hvC]; rfl
    obtain ⟨⟨-, -, -, pht, hpht⟩, -⟩ := hok
    rw [← hpv] at hpht
    exact rRoute_tree v bv pp k hi pht hpht _ _ path none none
      (pht_lt_size v.pages hwm pht hpht _ hw) ⟨hwm, hw⟩ (hk hi) hr

/-- **A nested bucket of a reader's root or top-level bucket** has a value with a header, and
an inline page after it when inline (only the root bucket has nested buckets: `rootShape`). -/
theorem bktLeaf_bucket_value (v : View) (hv : viewWF v) (bv : List w8)
    (h : bv = rootVal v ∨ ∃ n, (n, bv) ∈ treeEntries v.pages v.root) (pg : List w8)
    (hpg : pg ∈ bktLeaves v.pages bv) (i : Nat) (hi : i < pageCount pg)
    (hf : leafFlags pg i % 2 = bucketLeafFlag) :
    16 ≤ (leafValue pg i).length ∧
      (inBucketRoot (leafValue pg i) = 0 → 16 < (leafValue pg i).length) := by
  have hok := rBktOK_of v hv bv h
  obtain ⟨C, hokC, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  have hrv : v.root = C.root := by rw [← hvC]; rfl
  unfold rBktOK rTree at hok
  rw [hpv] at hok hpg
  rw [hpv, hrv] at h
  obtain ⟨⟨hw, -, hk, -⟩, -, -, -, hshape, -⟩ := hokC
  have hfin : bucketWF C.pages C.hwm (leafValue pg i) → 16 ≤ (leafValue pg i).length ∧
      (inBucketRoot (leafValue pg i) = 0 → 16 < (leafValue pg i).length) := by
    intro hb
    cases hb with
    | file _ h16 hr0 _ => exact ⟨h16, fun h => absurd h hr0⟩
    | inline _ h16 _ _ hpt =>
      refine ⟨h16, fun _ => ?_⟩
      cases hpt with
      | leaf _ _ _ hl _ =>
        have h1 := hl.2.1
        have h2 : (inlinePage (leafValue pg i)).length = (leafValue pg i).length - 16 := by
          unfold inlinePage bucketHeaderSize; simp
        unfold elemOff at h1; omega
      | branch _ _ hf' _ _ => simp_all [branchPageFlag, leafPageFlag]
  rcases h with rfl | ⟨n, hn⟩
  · -- the root bucket: its leaves' entries are top-level buckets
    have hroot : inBucketRoot (rootVal v) = C.root := by
      rw [inBucketRoot_rootVal, hrv]
      cases hw with
      | page _ pg _ _ hpg hid _ _ =>
        have : C.root < 2 ^ 64 := by rw [← hid]; unfold pageId; exact BitVec.isLt _
        omega
    have hr0 : C.root ≠ 0 := by cases hw with | page _ _ h2 _ _ _ _ _ => omega
    unfold bktLeaves at hpg
    rw [hroot, if_neg hr0] at hpg
    obtain ⟨id', lo', hi', -, hpid, hfl, hpt, -⟩ :=
      leavesF_page C.pages C.hwm _ _ _ _ hw hk pg hpg
    apply hfin
    cases hpt with
    | leaf _ _ _ _ hb => exact hb i hi hf
    | branch _ _ hf' _ _ => rw [hfl] at hf'; simp [branchPageFlag, leafPageFlag] at hf'
  · -- a top-level bucket holds no nested bucket
    exfalso
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
    have := (hsh hbl i hi).1
    rw [hf] at this; simp [bucketLeafFlag] at this

/-- In a leaf with increasing keys, a key's search index is its index. -/
theorem pageSeekIdx_of_key (pg : List w8) (len : Nat) (hwf : leafWF pg len) (i : Nat)
    (hi : i < pageCount pg) (k : List w8) (hk : leafKey pg i = k) : pageSeekIdx pg k = i := by
  unfold pageSeekIdx
  apply Read.takeWhile_range_length _ _ _ (by omega)
  · intro m hm
    simp only [decide_eq_true_eq]
    rw [← hk]; exact hwf.2.2.2 m i hm hi
  · intro _
    simp only [decide_eq_false_iff_not]
    rw [hk]; exact go.goStringLt_irrefl k

/-- **A name not at the search index of the only leaf that can hold it is no nested bucket.** -/
theorem not_bktNames (P : Pages) (bv : List w8) (pg : List w8) (k : List w8)
    (hmem : ∀ pg' ∈ bktLeaves P bv, ∀ i < pageCount pg', leafKey pg' i = k → pg' = pg)
    (hwf : leafWF pg pg.length)
    (hn : ¬ (pageSeekIdx pg k < pageCount pg ∧ leafKey pg (pageSeekIdx pg k) = k ∧
      leafFlags pg (pageSeekIdx pg k) % 2 = bucketLeafFlag)) :
    k ∉ bktNames P bv := by
  intro h
  unfold bktNames at h
  obtain ⟨pg', hpg', hk⟩ := List.mem_flatMap.mp h
  obtain ⟨j, hj, hjk⟩ := List.mem_map.mp hk
  obtain ⟨hjr, hjf⟩ := List.mem_filter.mp hj
  rw [List.mem_range] at hjr
  simp only [decide_eq_true_eq] at hjf
  have he := hmem pg' hpg' j hjr hjk
  subst he
  have hsi := pageSeekIdx_of_key pg' _ hwf j hjr k hjk
  apply hn
  rw [hsi]; exact ⟨hjr, hjk, hjf⟩

end bkt

end bbolt
end EtcdGrove
end Perennial
