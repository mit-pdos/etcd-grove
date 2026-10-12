/-
The freelist's `ReleasePendingPages` keeps bbolt's MVCC rule (`DBPred.lean`'s `mvccView`).

A pending pair `(id, a)` of transaction `t` (a page allocated by `a`, freed by `t`) is safe to
release for the open readers `R` if no reader `r` has `a ≤ r < t`: a reader that sees the page
began after `a` and before `t` (`mvccView`). `relSafe R σ σ'`: every id free in `σ'` was free
in `σ` or is a safe pending pair of `σ`, every pending pair of `σ'` was one of `σ`, the
allocations are the same. `release(minid - 1)` and `releaseRange(b, e)` over a gap between
consecutive readers are `relSafe`, so `ReleasePendingPages` is (`releasePending_relSafe`).

The readers' txids must be in `[1, 2^64 - 2]`. With a reader of txid 0, `ReleasePendingPages`
calls `releaseRange(0, 0 - 1)`: the end wraps to `2^64 - 1`, so the range covers every
transaction, the reader's included. It frees nothing of an entry whose `lastReleaseBegin` is 0
(a new entry's), so a page that reader sees is freed only if an earlier `releaseRange` already
looked at its entry; a txid-0 reader exists only in a database that fell back to meta page 0
(txid 0: at most one commit since `init`). Whether that can happen is open; the proof does not
need to decide it.
-/
module

public import Proof.go_etcd_io.bbolt.DBEnd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-- No reader `r` of `R` has `a ≤ r < t`. -/
def safeRel (R : List w64) (t a : w64) : Prop :=
  ∀ r ∈ R, ¬ (uint.Z a ≤ uint.Z r ∧ uint.Z r < uint.Z t)

/-- `σ'` frees only safe pending pairs of `σ`, keeps a subset of its pending pairs, and the same
allocations. -/
def relSafe (R : List w64) (σ σ' : FLState) : Prop :=
  σ'.allocs = σ.allocs ∧
  (∀ x, x ∈ σ'.free → x ∈ σ.free ∨
    ∃ t pd a, σ.pending !! t = some pd ∧ (x, a) ∈ pd.pairs ∧ safeRel R t a) ∧
  ∀ t pd' p, σ'.pending !! t = some pd' → p ∈ pd'.pairs →
    ∃ pd, σ.pending !! t = some pd ∧ p ∈ pd.pairs

theorem relSafe_refl (R : List w64) (σ : FLState) : relSafe R σ σ :=
  ⟨rfl, fun _ h => Or.inl h, fun _ pd' _ h hp => ⟨pd', h, hp⟩⟩

theorem relSafe_trans (R : List w64) (σ σ1 σ2 : FLState) (h1 : relSafe R σ σ1)
    (h2 : relSafe R σ1 σ2) : relSafe R σ σ2 := by
  obtain ⟨a1, f1, p1⟩ := h1
  obtain ⟨a2, f2, p2⟩ := h2
  refine ⟨a2.trans a1, fun x hx => ?_, fun t pd' p ht hp => ?_⟩
  · rcases f2 x hx with h | ⟨t, pd, a, ht, hp, hs⟩
    · exact f1 x h
    · obtain ⟨pd0, ht0, hp0⟩ := p1 t pd (x, a) ht hp
      exact Or.inr ⟨t, pd0, a, ht0, hp0, hs⟩
  · obtain ⟨pd1, ht1, hp1⟩ := p2 t pd' p ht hp
    exact p1 t pd1 p ht1 hp1

theorem ofilter_some {α : Type} (o : Option α) (p : α → Bool) (v : α) :
    o.filter p = some v ↔ o = some v ∧ p v = true := by
  cases o with
  | none => simp
  | some x =>
    simp only [Option.filter]
    split
    · rename_i h
      constructor
      · intro hv; cases hv; exact ⟨rfl, h⟩
      · rintro ⟨hv, _⟩; exact hv
    · rename_i h
      constructor
      · intro hv; cases hv
      · rintro ⟨hv, hp⟩; cases hv; exact absurd hp h

theorem zip_map_fst_snd' {α β : Type} (l : List (α × β)) : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- An id of an entry whose two lists have the same length is in one of its pairs. -/
theorem mem_pairs_of_mem_ids (pd : Pending) (x : w64) (hl : pd.ids.length = pd.alloctx.length)
    (hx : x ∈ pd.ids) : ∃ a, (x, a) ∈ pd.pairs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨pd.alloctx[i]'(by omega), ?_⟩
  unfold Pending.pairs
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp; omega, by simp⟩

/-- `release(txid)` with every reader above `txid` (and each entry's lists of one length). -/
theorem release_relSafe (R : List w64) (σ : FLState) (txid : w64)
    (hR : ∀ r ∈ R, uint.Z txid < uint.Z r)
    (hl : ∀ t pd, σ.pending !! t = some pd → pd.ids.length = pd.alloctx.length) :
    relSafe R σ (σ.release txid) := by
  refine ⟨rfl, fun x hx => ?_, fun t pd' p ht hp => ?_⟩
  · simp only [FLState.release, List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inl h
    · rw [mem_flatIds] at h
      obtain ⟨t, pd, ht, hx⟩ := h
      rw [GMap.lookup_filter, ofilter_some] at ht
      obtain ⟨hpt, hle⟩ := ht
      obtain ⟨a, ha⟩ := mem_pairs_of_mem_ids pd x (hl t pd hpt) hx
      refine Or.inr ⟨t, pd, a, hpt, ha, fun r hr hb => ?_⟩
      have := hR r hr
      simp only [decide_eq_true_eq] at hle
      omega
  · simp only [FLState.release] at ht
    rw [GMap.lookup_filter, ofilter_some] at ht
    exact ⟨pd', ht.1, hp⟩

/-- The pairs `releaseRange` keeps of an entry are some of its pairs. -/
theorem rrKeep_pairs (b e : w64) (pd : Pending) (p : w64 × w64) (h : p ∈ (rrKeep b e pd).pairs) :
    p ∈ pd.pairs := by
  unfold rrKeep Pending.pairs at h
  simp only at h
  rw [zip_map_fst_snd'] at h
  exact (List.mem_filter.1 h).1

/-- `releaseRange(b, e)` with no reader in `[b, e]`. -/
theorem releaseRange_relSafe (R : List w64) (σ : FLState) (b e : w64)
    (hR : ∀ r ∈ R, ¬ (uint.Z b ≤ uint.Z r ∧ uint.Z r ≤ uint.Z e)) :
    relSafe R σ (σ.releaseRange b e) := by
  unfold FLState.releaseRange
  split
  · exact relSafe_refl R σ
  refine ⟨rfl, fun x hx => ?_, fun t pd' p ht hp => ?_⟩
  · simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inl h
    · rw [List.mem_flatMap] at h
      obtain ⟨⟨t, pd⟩, hkv, hx⟩ := h
      rw [GMap.mem_toList, GMap.lookup_filter, ofilter_some] at hkv
      obtain ⟨hpt, htouch⟩ := hkv
      unfold rrRel at hx
      rw [List.mem_map] at hx
      obtain ⟨⟨x', a⟩, hxa, rfl⟩ := hx
      rw [List.mem_filter] at hxa
      refine Or.inr ⟨t, pd, a, hpt, hxa.1, fun r hr hb => ?_⟩
      have hta : inTxRange b e t = true := by
        unfold rrTouched at htouch; simp only [Bool.and_eq_true] at htouch; exact htouch.1
      have haa := hxa.2
      unfold inTxRange at hta haa
      simp only [decide_eq_true_eq] at hta haa
      exact hR r hr ⟨by omega, by omega⟩
  · rw [GMap.lookup_union_Some_raw] at ht
    rcases ht with ht | ⟨_, ht⟩
    · rw [GMap.lookup_filter, ofilter_some] at ht
      exact ⟨pd', ht.1, hp⟩
    · rw [GMap.lookup_filter, ofilter_some, GMap.lookup_fmap, Option.map_eq_some_iff] at ht
      obtain ⟨⟨pd0, h0, rfl⟩, _⟩ := ht
      rw [GMap.lookup_filter, ofilter_some] at h0
      exact ⟨pd0, h0.1, rrKeep_pairs b e pd0 p hp⟩

/-- The fold of `ReleasePendingPages` over the sorted read-only transactions `l` still to visit:
every reader visited is below `acc.2`, and those to visit are at least `acc.2 - 1`. -/
theorem releaseFold_relSafe (R : List w64) (σ : FLState) :
    ∀ (l : List w64) (acc : FLState × w64), l.Pairwise (fun a b => decide (uint.Z a ≤ uint.Z b)) →
    (∀ r ∈ l, 1 ≤ uint.Z r ∧ uint.Z r < 2 ^ 64 - 1) →
    relSafe R σ acc.1 → (∀ r ∈ R, uint.Z r < uint.Z acc.2 ∨ r ∈ l) →
    (∀ r ∈ l, uint.Z acc.2 ≤ uint.Z r + 1) →
    let res := l.foldl (fun (acc : FLState × w64) tid =>
      (acc.1.releaseRange acc.2 (tid - W64 1), tid + W64 1)) acc
    relSafe R σ res.1 ∧ ∀ r ∈ R, uint.Z r < uint.Z res.2 := by
  intro l
  induction l with
  | nil =>
    intro acc _ _ hs hR _
    refine ⟨hs, fun r hr => ?_⟩
    rcases hR r hr with h | h
    · exact h
    · cases h
  | cons tid l ih =>
    intro acc hsort hrng hs hR hge
    simp only [List.foldl_cons]
    have htid := hrng tid (List.mem_cons_self ..)
    have hsort' : l.Pairwise (fun a b => decide (uint.Z a ≤ uint.Z b)) := (List.pairwise_cons.1 hsort).2
    have hle : ∀ r ∈ l, uint.Z tid ≤ uint.Z r := fun r hr => by
      have := (List.pairwise_cons.1 hsort).1 r hr; simpa using this
    have htid1 : uint.Z (tid - W64 1) = uint.Z tid - 1 := by word
    have htid2 : uint.Z (tid + W64 1) = uint.Z tid + 1 := by word
    refine ih _ hsort' (fun r hr => hrng r (List.mem_cons_of_mem _ hr)) ?_ ?_ ?_
    · refine relSafe_trans R σ acc.1 _ hs (releaseRange_relSafe R acc.1 _ _ (fun r hr hb => ?_))
      rcases hR r hr with h | h
      · omega
      · rcases List.mem_cons.1 h with rfl | h
        · omega
        · have := hle r h; omega
    · intro r hr
      rcases hR r hr with h | h
      · left; simp only; rw [htid2]; have := hge tid (List.mem_cons_self ..); omega
      · rcases List.mem_cons.1 h with rfl | h
        · left; simp only; rw [htid2]; omega
        · right; exact h
    · intro r hr; simp only; rw [htid2]; have := hle r hr; omega

/-- `relSafe` through the freelist's equivalence (the order of free ids and of pending pairs). -/
theorem relSafe_equiv (R : List w64) (σ τ τ' : FLState) (h : relSafe R σ τ) (he : τ'.equiv τ) :
    relSafe R σ τ' := by
  obtain ⟨ha, hf, hp⟩ := h
  obtain ⟨efree, _, eallocs, edom, epairs⟩ := he
  refine ⟨eallocs.trans ha, fun x hx => hf x (efree.mem_iff.1 hx), fun t pd' p ht hpp => ?_⟩
  have hsome := (edom t).1 (by rw [ht]; rfl)
  cases hq : τ.pending !! t with
  | none => rw [hq] at hsome; cases hsome
  | some q =>
    have := (epairs t pd' q ht hq).1
    exact hp t q p hq (this.mem_iff.1 hpp)

/-- `ReleasePendingPages()` frees only pages no reader sees: readers with txids in
`[1, 2^64 - 2]` (and each pending entry's lists of one length). -/
theorem releasePending_relSafe (σ : FLState)
    (hrng : ∀ r ∈ σ.readonly, 1 ≤ uint.Z r ∧ uint.Z r < 2 ^ 64 - 1)
    (hl : ∀ t pd, σ.pending !! t = some pd → pd.ids.length = pd.alloctx.length) :
    relSafe σ.readonly σ σ.releasePending := by
  have hperm : (sortedTxids σ.readonly).Perm σ.readonly := List.mergeSort_perm _ _
  have hsort : (sortedTxids σ.readonly).Pairwise (fun a b => decide (uint.Z a ≤ uint.Z b)) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hrng' : ∀ r ∈ sortedTxids σ.readonly, 1 ≤ uint.Z r ∧ uint.Z r < 2 ^ 64 - 1 :=
    fun r hr => hrng r (hperm.mem_iff.1 hr)
  -- the first reader is the least
  have hmin : ∀ r ∈ σ.readonly, uint.Z ((sortedTxids σ.readonly).headD (W64 (2 ^ 64 - 1))) ≤ uint.Z r := by
    intro r hr
    have hr' := hperm.mem_iff.2 hr
    cases hs : sortedTxids σ.readonly with
    | nil => rw [hs] at hr'; cases hr'
    | cons m l =>
      rw [hs] at hr' hsort
      simp only [List.headD_cons]
      rcases List.mem_cons.1 hr' with rfl | h
      · exact Int.le_refl _
      · have := (List.pairwise_cons.1 hsort).1 r h; simpa using this
  unfold FLState.releasePending
  simp only
  generalize hm : (sortedTxids σ.readonly).headD (W64 (2 ^ 64 - 1)) = minid at hmin
  -- `release(minid - 1)`
  have h1 : relSafe σ.readonly σ (if 0 < uint.Z minid then σ.release (minid - W64 1) else σ) := by
    split
    · rename_i hpos
      refine release_relSafe _ σ _ (fun r hr => ?_) hl
      have := hmin r hr
      have : uint.Z (minid - W64 1) = uint.Z minid - 1 := by word
      omega
    · exact relSafe_refl _ σ
  -- the gaps between readers
  have h2 := releaseFold_relSafe σ.readonly σ (sortedTxids σ.readonly)
    (if 0 < uint.Z minid then σ.release (minid - W64 1) else σ, minid) hsort hrng' h1
    (fun r hr => Or.inr (hperm.mem_iff.2 hr))
    (fun r hr => by have := hmin r (hperm.mem_iff.1 hr); simp only; omega)
  obtain ⟨h2a, h2b⟩ := h2
  -- after the newest reader
  have h3 := relSafe_trans _ σ _ _ h2a (releaseRange_relSafe _ _ _ (W64 (2 ^ 64 - 1))
    (fun r hr hb => Int.lt_irrefl _ (Int.lt_of_lt_of_le (h2b r hr) hb.1)))
  exact ⟨h3.1, h3.2.1, h3.2.2⟩

section db
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- A reader's txid is a read-only transaction of the freelist. -/
theorem reader_txid_ro (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (k : Nat) (r : Reader) (hk : σ.readers !! k = some r) : r.txid ∈ σ.fl.readonly := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hro, _⟩ := h
  refine hro.mem_iff.2 (List.mem_map.2 ⟨(k, r), (GMap.mem_toList _ _ _).2 hk, rfl⟩)

/-- The freelist after `ReleasePendingPages` (any state equivalent to it), no writer open: the
database's facts kept. -/
theorem dbOK_release (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hw : σ.wr = none)
    (hrng : ∀ r ∈ σ.fl.readonly, 1 ≤ uint.Z r ∧ uint.Z r < 2 ^ 64 - 1)
    (hl : ∀ t pd, σ.fl.pending !! t = some pd → pd.ids.length = pd.alloctx.length)
    (fl' : FLState) (he : fl'.equiv σ.fl.releasePending) :
    dbOK { σ with fl := fl' } v0 v1 := by
  have hrs := relSafe_equiv _ _ _ _ (releasePending_relSafe σ.fl hrng hl) he
  obtain ⟨ha, hf, hp⟩ := hrs
  have h' := h
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h'
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow⟩ := hcur
  refine ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, ⟨cwf, cdisj, cin, ?_, ?_, ?_⟩, hrd, ?_, hsl, hfl,
    ?_, hrs, ?_⟩
  · intro id pg hid a hal
    exact calloc id pg hid a (by rw [← ha]; exact hal)
  · intro s hs
    obtain ⟨h2, h3, h4⟩ := cfree s hs
    refine ⟨h2, fun hfree => ?_, fun t pd' a ht hpp => ?_⟩
    · rcases hf _ hfree with h | ⟨t, pd, a, ht, hpp, _⟩
      · exact h3 h
      · exact h4 t pd a ht hpp
    · obtain ⟨pd, ht0, hpp0⟩ := hp t pd' _ ht hpp
      exact h4 t pd a ht0 hpp0
  · -- the freelist stays below the high-water mark: the freed pages were committed ones'
    obtain ⟨b1, b2, b3, b4⟩ := cbelow
    refine ⟨fun x hx => ?_, fun t pd' p ht hp' htx => ?_, fun _ t pd' p ht hp' => ?_, b4⟩
    · rcases hf x hx with h | ⟨t, pd, a, ht, hpp, _⟩
      · exact b1 x h
      · exact b2 t pd (x, a) ht hpp (b3 hw t pd (x, a) ht hpp)
    · obtain ⟨pd, ht0, hpp0⟩ := hp t pd' p ht hp'
      exact b2 t pd p ht0 hpp0 htx
    · obtain ⟨pd, ht0, hpp0⟩ := hp t pd' p ht hp'
      exact b3 hw t pd p ht0 hpp0
  · intro k r hk
    obtain ⟨malloc, mfree⟩ := hmv k r hk
    have hR := reader_txid_ro σ v0 v1 h k r hk
    refine ⟨fun id pg hid a hal => malloc id pg hid a (by rw [← ha]; exact hal), fun s hs => ?_⟩
    obtain ⟨h2, h3, h4⟩ := mfree s hs
    refine ⟨h2, fun hfree => ?_, fun t pd' a ht hpp => ?_⟩
    · rcases hf _ hfree with h | ⟨t, pd, a, ht, hpp, hsafe⟩
      · exact h3 h
      · exact hsafe r.txid hR (h4 t pd a ht hpp)
    · obtain ⟨pd, ht0, hpp0⟩ := hp t pd' _ ht hpp
      exact h4 t pd a ht0 hpp0
  · obtain ⟨_, ero, _⟩ := he
    exact ero.trans ((List.mergeSort_perm _ _).trans hro)
  · refine ⟨hwr.1, fun w hw' => ?_⟩
    rw [hw] at hw'; cases hw'

end db

end bbolt
end EtcdGrove
end Perennial
