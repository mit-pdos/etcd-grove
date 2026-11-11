/-
bbolt's MVCC rule as pure facts (U0a of `notes/bbolt-proof-plan.md`; design §3.2, §3.6): views,
registered readers, and what the freelist must satisfy so that no page a view sees is reused.

Ported from `old/bbolt/.../DBPred.lean` (`mvccView`, `flBelow`, `flCurOK`, `pagesAgree`) over
records: a view is the pages of transaction `txid` at the mapping `base`.
-/
module

public import Proof.go_etcd_io.bbolt.Model.TreeData
public import Proof.go_etcd_io.bbolt.Model.FL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

section mvcc
variable [GooseExts]

/-- **A view** (a reader's, or the writer's base) of transaction `txid`, at the mapping `base`:
the pages it sees. -/
structure View where
  base : Loc
  txid : Nat
  pages : Pages
  /-- The root bucket's root page (what the view's `Tx.root` reads). -/
  root : Nat
  deriving Inhabited

instance View.countable : Pos.Countable View :=
  countableOfLeftInverse (fun v => (v.base, v.txid, v.pages, v.root))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

/-- The view of the committed state `C` at the mapping `base`. -/
def View.ofC (base : Loc) (C : CommitSt) : View := ⟨base, C.txid, C.pages, C.root⟩
proj_simps View.ofC

/-- The data a view holds (`treeData` of its pages and root): a reader's snapshot. -/
def View.data (v : View) : Data :=
  GMap.ofList ((treeEntries v.pages v.root).map fun e => (e.1, bktOfPage v.pages e.2))

/-- A view is a committed state's at its mapping (so its tree is `treeOK`). -/
def viewWF (v : View) : Prop := ∃ C, treeOK C ∧ View.ofC v.base C = v

/-- A registered reader (`pagesInv`'s registry): its view. -/
structure RdInfo where
  v : View
  deriving Inhabited

instance RdInfo.countable : Pos.Countable RdInfo :=
  countableOfLeftInverse (fun r => r.v) (fun v => ⟨v⟩) (fun _ => rfl)

/-- The slots of every pending page (`Free` records each slot of an extent). -/
def pendSlots (fl : FLPg) : List Nat := fl.pendingIds.map BitVec.toNat

/-- **bbolt's MVCC rule for a view** (old `mvccView`): its pages were allocated by its
transaction or before; a slot it covers is no meta page, not free, and pending only from a
transaction newer than the view that freed a page allocated by the view's transaction or
before. -/
def mvccView (fl : FLPg) (v : View) : Prop :=
  (∀ id pg, v.pages !! id = some pg → ∀ a, fl.allocs !! W64 (id : Int) = some a →
    a.toNat ≤ v.txid) ∧
  ∀ s, coversSlot v.pages s → 2 ≤ s ∧ W64 (s : Int) ∉ fl.free ∧
    ∀ t pd i, fl.pending !! t = some pd → pd.ids[i]? = some (W64 (s : Int)) →
      (pd.alloctx.getD i 0).toNat ≤ v.txid ∧ v.txid < t.toNat

/-- **The freelist is below the committed state** (old `flBelow`, round 4 N6: without its
writer clause, which `storeOK`'s `wtx`/`pub` clauses replace): free ids and the pending ids of
committed transactions below the high-water mark; every pending transaction committed or the
live writer's `w` (its allocations before it); the txid does not wrap; ids below `2^62`. -/
def flBelow (fl : FLPg) (C : CommitSt) (w : Option Nat) : Prop :=
  (∀ x ∈ fl.free, x.toNat < C.hwm) ∧
  (∀ t pd x, fl.pending !! t = some pd → x ∈ pd.ids → t.toNat ≤ C.txid → x.toNat < C.hwm) ∧
  (∀ t pd, fl.pending !! t = some pd →
    t.toNat ≤ C.txid ∨ (w = some t.toNat ∧ ∀ a ∈ pd.alloctx, a.toNat < t.toNat)) ∧
  C.txid + 1 < 2 ^ 64 ∧ (∀ x ∈ fl.free, x.toNat < 2 ^ 62) ∧
  (∀ x ∈ fl.pendingIds, x.toNat < 2 ^ 62)

/-- Slot `s` is pending only for the live writer `w` (a current tree's page it freed). -/
def pendingOnlyFromWriter (fl : FLPg) (w : Option Nat) (s : Nat) : Prop :=
  ∀ t pd, fl.pending !! t = some pd → W64 (s : Int) ∈ pd.ids → w = some t.toNat

/-- Two page maps that cover a slot see the same page there (views agree where they
overlap). -/
def pagesAgree (P Q : Pages) : Prop :=
  ∀ i pi j pj s, P !! i = some pi → Q !! j = some pj →
    i ≤ s → s < i + (1 + pageOverflow pi) → j ≤ s → s < j + (1 + pageOverflow pj) →
      i = j ∧ pi = pj

/-! ## Freelist pages (`freelist.Read`/`Write`, `page.go`'s `FreelistPageCount`) -/

/-- The header count of a freelist page, and the index its ids start at: a count of `0xFFFF`
means the count is the first `uint64` after the header. -/
def flCountIdx (pg : List w8) : Nat × Nat :=
  if pageCount pg < 0xFFFF then (pageCount pg, 0)
  else ((decode (bytesAt pg 16 8) : w64).toNat, 1)

/-- The ids of a freelist page. -/
def flIds (pg : List w8) : List w64 :=
  (List.range (flCountIdx pg).1).map fun i =>
    (decode (bytesAt pg (16 + 8 * (flCountIdx pg).2 + 8 * i) 8) : w64)

/-- `x` is pending for a committed transaction (`C.txid` or before). -/
def committedPending (fl : FLPg) (C : CommitSt) (x : w64) : Prop :=
  ∃ t pd, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ t.toNat ≤ C.txid

/-- **The synced freelist page `pg` can be reloaded** (old `flCurOK`, round 2 F4.2: over the
page's bytes, which are a W slot's, so it is stated in `wdbOK`): when `C` names a freelist page,
`pg` is a freelist page whose ids lie within it, are distinct, at least 2, not in its own
extent; they include every free id and every committed transaction's pending id, and each is
committed-pending or could be free (below the high-water mark, not a tree page); and the page
was allocated by a committed transaction (its `allocs` entry, if any, at most `C.txid`;
maintainer 13, for `Free`'s `canFree` at `Commit`'s free of the page); its header names its own
id (maintainer 14, from `flFileOK` at `Open`, `allocate`'s header at `commitFreelist`: `Free`
takes `p.Id()`). -/
def flCurOK (fl : FLPg) (C : CommitSt) (pg : List w8) : Prop :=
  ∀ f, C.flpg = some f →
    2 ≤ f ∧ f + (1 + pageOverflow pg) ≤ C.hwm ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧
    pageFlags pg = freelistPageFlag ∧
    16 + 8 * (flCountIdx pg).2 + 8 * (flCountIdx pg).1 ≤ pg.length ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ x.toNat) ∧
    (∀ x ∈ flIds pg, ¬ (f ≤ x.toNat ∧ x.toNat < f + (1 + pageOverflow pg))) ∧
    (∀ s, f ≤ s → s < f + (1 + pageOverflow pg) → ¬ coversSlot C.pages s ∧
      W64 (s : Int) ∉ fl.allIds) ∧
    (∀ x ∈ fl.free, x ∈ flIds pg) ∧ (∀ x, committedPending fl C x → x ∈ flIds pg) ∧
    (∀ x ∈ flIds pg, committedPending fl C x ∨
      (x.toNat < C.hwm ∧ x.toNat < 2 ^ 62 ∧ ¬ coversSlot C.pages x.toNat)) ∧
    (∀ a, fl.allocs !! W64 (f : Int) = some a → a.toNat ≤ C.txid) ∧
    pageId pg = f

/-! ## Lemma statements (U3) -/

omit [GooseExts] in
private theorem mem_flatMap_toList' {V : Type} {f : V → List w64} (m : GMap w64 V) (x : w64) :
    x ∈ m.toList.flatMap (fun kv => f kv.2) ↔ ∃ k v, m !! k = some v ∧ x ∈ f v := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨k, v⟩, hkv, hx⟩; exact ⟨k, v, (GMap.mem_toList m k v).1 hkv, hx⟩
  · rintro ⟨k, v, hkv, hx⟩; exact ⟨(k, v), (GMap.mem_toList m k v).2 hkv, hx⟩

omit [GooseExts] in
private theorem mem_sortPgids' (l : List w64) (x : w64) : x ∈ sortPgids l ↔ x ∈ l :=
  (List.mergeSort_perm _ _).mem_iff

omit [GooseExts] in
private theorem mem_zip_idx {α β : Type} {l1 : List α} {l2 : List β} {x : α × β} (h : x ∈ l1.zip l2) :
    ∃ i : Nat, l1[i]? = some x.1 ∧ l2[i]? = some x.2 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_zip_eq_some] at hi
  exact ⟨i, hi.1, hi.2⟩

omit [GooseExts] in
private theorem getD_of_getElem? {l : List w64} {i : Nat} {a : w64} (h : l[i]? = some a) :
    l.getD i 0 = a := by
  simp [List.getD_eq_getElem?_getD, h]


/-- `release(txid)` frees no page of a view of a transaction at or after `txid` (its pending
pages are newer than the view). Used by U3 (`store_release`). -/
theorem mvccView_release (fl : FLPg) (v : View) (txid : w64) (h : mvccView fl v)
    (ht : txid.toNat ≤ v.txid) : mvccView (fl.release txid) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun s hs => ?_⟩
  obtain ⟨hs2, hfree, hpend⟩ := h2 s hs
  refine ⟨hs2, ?_, ?_⟩
  · simp only [FLPg.release]
    rw [mem_sortPgids', List.mem_append, mem_flatMap_toList']
    rintro (hm | ⟨t, pd, hkv, hx⟩)
    · exact hfree hm
    · rw [GMap.lookup_filter, Option.filter_eq_some_iff] at hkv
      obtain ⟨hkv, hle⟩ := hkv
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      have := (hpend t pd i hkv hi).2
      simp at hle
      omega
  · intro t pd i hkv hi
    simp only [FLPg.release, GMap.lookup_filter, Option.filter_eq_some_iff] at hkv
    exact hpend t pd i hkv.1 hi

/-- `releaseRange(b, e)` frees no page of a view outside `[b, e]`. Used by U3
(`store_release`). -/
theorem mvccView_releaseRange (fl : FLPg) (v : View) (b e : w64) (h : mvccView fl v)
    (ht : v.txid < b.toNat ∨ e.toNat < v.txid) : mvccView (fl.releaseRange b e) v := by
  unfold FLPg.releaseRange
  split
  · exact h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun s hs => ?_⟩
  obtain ⟨hs2, hfree, hpend⟩ := h2 s hs
  refine ⟨hs2, ?_, ?_⟩
  · simp only
    rw [mem_sortPgids', List.mem_append,
      mem_flatMap_toList' (f := fun p => (releaseRangeOne b e p).1)]
    rintro (hm | ⟨t, pd, hkv, hx⟩)
    · exact hfree hm
    · rw [GMap.lookup_filter, Option.filter_eq_some_iff] at hkv
      obtain ⟨hkv, hsel⟩ := hkv
      simp only [releaseRangeOne, inRR, List.mem_map, List.mem_filter] at hx
      obtain ⟨⟨x, a⟩, ⟨hxz, hin⟩, rfl⟩ := hx
      obtain ⟨i, hi1, hi2⟩ := mem_zip_idx hxz
      have := hpend t pd i hkv hi1
      rw [getD_of_getElem? hi2] at this
      simp only [decide_eq_true_eq] at hin hsel this
      omega
  · intro t pd i hkv hi
    simp only [GMap.lookup_union, GMap.lookup_filter, GMap.lookup_fmap] at hkv
    rcases hp : fl.pending !! t with _ | pd0
    · simp [hp] at hkv
    rw [hp] at hkv
    by_cases hsel : (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b)
    · have hs' : decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b) = true :=
        decide_eq_true hsel
      simp only [Option.filter_some, hs', Bool.not_true,
        Option.none_or, ite_false, Bool.false_eq_true] at hkv
      simp only [Option.filter_eq_some_iff] at hkv
      obtain ⟨hkv, -⟩ := hkv
      cases hkv
      simp only [releaseRangeOne, List.getElem?_map, Option.map_eq_some_iff] at hi ⊢
      obtain ⟨⟨x, a⟩, hxa, rfl⟩ := hi
      have hmem := List.mem_of_getElem? hxa
      rw [mem_srLoop, List.mem_filter] at hmem
      obtain ⟨j, hj1, hj2⟩ := mem_zip_idx hmem.1
      have := hpend t pd0 j hp hj1
      rw [getD_of_getElem? hj2] at this
      have key : ∀ (L : List (w64 × w64)), L[i]? = some (W64 (s : Int), a) →
          (L.map Prod.snd).getD i 0 = a := fun L hL =>
        getD_of_getElem? (by rw [List.getElem?_map, hL]; rfl)
      rw [key _ hxa]; exact this
    · have hs' : decide (b.toNat ≤ t.toNat ∧ t.toNat ≤ e.toNat ∧ pd0.lastReleaseBegin ≠ b) = false :=
        decide_eq_false hsel
      simp only [Option.filter_some, hs', Bool.not_false, ite_true, Option.some_or] at hkv
      cases hkv
      exact hpend t _ i hp hi

omit [GooseExts] in
private theorem runIds_toNat (id : w64) (n j : Nat) (hj : j < n) (hn : id.toNat + n < 2 ^ 64) :
    (id + W64 (j : Int)).toNat = id.toNat + j := by
  simp only [W64, BitVec.toNat_add, BitVec.toNat_ofInt]; omega

omit [GooseExts] in
private theorem mem_runIds (id : w64) (n : Nat) (x : w64) :
    x ∈ runIds id n ↔ ∃ j < n, x = id + W64 (j : Int) := by
  simp only [runIds, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

/-- A writer's `Free` keeps the MVCC rule of every older view: a freed page of the view becomes
pending for a newer transaction, allocated at or before the view. Used by U3 (`store_free`).
(U3 finding 8: the view's slots below `2 ^ 64`, the freelist well-formed.) -/
theorem mvccView_free (fl : FLPg) (v : View) (txid id : w64) (n : Nat) (h : mvccView fl v)
    (ht : v.txid < txid.toNat) (hfree : fl.canFree txid id n)
    (hpg : (∃ pg, v.pages !! id.toNat = some pg ∧ 1 + pageOverflow pg = n) ∨
      ∀ j < n, ¬ coversSlot v.pages (id.toNat + j))
    (hlt : ∀ s, coversSlot v.pages s → s < 2 ^ 64)
    (hwf : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    mvccView (fl.freePages txid id n) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun id' pg hp a ha => ?_, fun s hs => ?_⟩
  · simp only [FLPg.freePages, GMap.lookup_delete_iff] at ha
    split at ha
    · cases ha
    · exact h1 id' pg hp a ha
  obtain ⟨hs2, hsf, hsp⟩ := h2 s hs
  refine ⟨hs2, hsf, fun t pd i hp hi => ?_⟩
  simp only [FLPg.freePages, GMap.lookup_insert_eq_iff] at hp
  split at hp
  · rename_i htx
    subst htx
    cases hp
    -- the old entry, or the run
    have hlen : ((fl.pending !! txid).getD ⟨[], [], 0⟩).ids.length =
        ((fl.pending !! txid).getD ⟨[], [], 0⟩).alloctx.length := by
      rcases hq : fl.pending !! txid with _ | q
      · rfl
      · exact hwf txid q hq
    generalize hP : (fl.pending !! txid).getD ⟨[], [], 0⟩ = P at hlen hi ⊢
    simp only at hi ⊢
    by_cases hil : i < P.ids.length
    · rw [List.getElem?_append_left hil] at hi
      have hold : ∃ q, fl.pending !! txid = some q ∧ q = P := by
        rcases hq : fl.pending !! txid with _ | q
        · rw [hq] at hP; simp only [Option.getD_none] at hP; subst hP; simp at hil
        · rw [hq] at hP; exact ⟨q, rfl, hP⟩
      obtain ⟨q, hq, rfl⟩ := hold
      have := hsp txid q i hq hi
      rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
    · rw [List.getElem?_append_right (by omega)] at hi
      have hj := List.mem_of_getElem? hi
      rw [mem_runIds] at hj
      obtain ⟨j, hjn, hj⟩ := hj
      have hix : i - P.ids.length < n := by
        have := (List.getElem?_eq_some_iff.1 hi).1
        simp only [runIds, List.length_map, List.length_range] at this; exact this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        List.getElem?_replicate, if_pos (by omega : i - P.alloctx.length < n), Option.getD_some]
      refine ⟨?_, ht⟩
      rcases hpg with ⟨pg, hpgv, -⟩ | hnc
      · rcases ha : fl.allocs !! id with _ | a
        · simp
        · have := h1 id.toNat pg hpgv a (by rw [show (W64 (id.toNat : Int)) = id by
            simp only [W64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]]; exact ha)
          simpa using this
      · exfalso
        have hs64 := hlt s hs
        have h1' : (W64 (s : Int)).toNat = s := by simp only [W64, BitVec.toNat_ofInt]; omega
        have h2' := runIds_toNat id n j hjn (by have := hfree.2.1; omega)
        rw [← hj, h1'] at h2'
        exact hnc j hjn (h2' ▸ hs)
  · exact hsp t pd i hp hi

/-- `Allocate` takes free ids, which no view sees. Used by U3 (`store_alloc`). (U3 finding 7: at
least one id.) -/
theorem mvccView_alloc (fl : FLPg) (v : View) (txid r : w64) (n : Nat) (h : mvccView fl v)
    (ha : fl.canAlloc r n) (hn : 0 < n) : mvccView (fl.alloc txid r n) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun id pg hp a hal => ?_, fun s hs => ?_⟩
  · simp only [FLPg.alloc, GMap.lookup_insert_eq_iff] at hal
    split at hal
    · rename_i hr
      exfalso
      have hcov : coversSlot v.pages id := ⟨id, pg, hp, Nat.le_refl _, by omega⟩
      exact (h2 id hcov).2.1 (hr ▸ ha.2 r ⟨Nat.le_refl _, by omega⟩)
    · exact h1 id pg hp a hal
  · obtain ⟨a, b, c⟩ := h2 s hs
    refine ⟨a, fun hm => b ?_, c⟩
    simp only [FLPg.alloc, List.mem_filter] at hm
    exact hm.1

end mvcc

end bbolt
end EtcdGrove
end Perennial
