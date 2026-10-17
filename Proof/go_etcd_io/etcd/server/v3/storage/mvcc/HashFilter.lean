/-
The hasher's filter (`kvHasher.WriteKeyValue`, `hash.go`; `kvHashIncludes` in the fork), as
etcd-io/etcd#22562 changes it (pr-verify/etcd-22562): which pairs of the `Key` bucket the hash
of a revision covers, and why the PR's filter makes the two ways etcd computes that hash agree.

The hash of revision `rev` with compaction revision `c` is computed two ways: by
`store.hashByRev` (`HashKV`), over the bucket with the kept set `treeIndex.Keep(rev)`
(`keepOfIs`), at any time while `c` is the store's compaction revision; and by the compaction
job at `rev` (`scheduleCompaction(rev, c)`), over the bucket it is compacting, with the kept set
`treeIndex.Compact(rev)` (`keepSetIs`), whose result `hashStorage` stores and `HashByRev(rev)`
then returns. etcd's corruption checks compare them across members (same `rev` and `c`).

- `hashIncl_keep_compact`: with the PR's filter, the two kept sets give the same answer for
  every pair (they differ only at revisions with main `rev`, above `c`, where the filter does
  not look at the set).
- `hashIncl_not_del`: with the PR's filter, no pair compaction at `c` may delete is hashed,
  with either kept set, so how far the deletion has gone does not change the hash; it needs
  `NoDelPutAt log c`, the premise of the existing finding
  `issues/etcd-compaction-delete-then-put.md` (without it compaction at `c` deletes a key's
  live revision, which `Keep(rev)` keeps).
- `hashInclOld_empty_ne`: the price, which the PR states ("empty-keep-set hashes intentionally
  change"): after a finished compaction, with nothing kept at `rev`, the stored revisions at or
  below `c` the old filter hashed are no longer hashed, so older members compute another hash.
- `hashInclOld_keep_compact_differ`: the filter before the PR (`hashInclOld`: an empty kept set
  filters nothing) does not have the first property: a key put at 2 and deleted at 3, `c = 2`,
  `rev = 3`: `Keep(3)` is empty, `Compact(3)` keeps the tombstone, and the put at 2 is hashed
  by `hashByRev` but not by the compaction job (the mismatch the PR's fuzz seed found).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open go_etcd_io.etcd.server.v3.storage.mvcc

section hash
variable [ext : FfiSyntax]

/-- A kept set (`map[Revision]struct{}`) keeps the revision `r`. -/
def keptBy (A : GMap Revision Unit) (r : Rev) : Prop := (A.lookup (revVal r)).isSome = true

/-- **What the hasher hashes** (the PR's filter): of a hasher at revision `rev` with compaction
revision `c` and kept set `K`, the pair whose key is revision `r` (`t`: a tombstone) when `r`
is at or below `rev`, kept by `K` if at or below `c`, and not a tombstone at `c`. -/
def hashIncl (c rev : Int) (K : Rev → Prop) (r : Rev) (t : Bool) : Prop :=
  sint.Z r.main ≤ rev ∧ (c < sint.Z r.main ∨ K r) ∧ ¬ (sint.Z r.main = c ∧ t = true)

instance keptBy_dec (A : GMap Revision Unit) : DecidablePred (keptBy A) :=
  fun r => inferInstanceAs (Decidable (_ = true))

instance hashIncl_dec (c rev : Int) (K : Rev → Prop) [DecidablePred K] (r : Rev) (t : Bool) :
    Decidable (hashIncl c rev K r t) := by
  unfold hashIncl; infer_instance

/-- The filter before the PR: an empty kept set skips nothing (`&& len(h.keep) > 0`). -/
def hashInclOld (c rev : Int) (K : Rev → Prop) (r : Rev) (t : Bool) : Prop :=
  sint.Z r.main ≤ rev ∧ (c < sint.Z r.main ∨ (∀ r', ¬ K r') ∨ K r) ∧ ¬ (sint.Z r.main = c ∧ t = true)

/-- The PR's filter depends on the kept set only below `c`. -/
theorem hashIncl_congr {c rev : Int} {K K' : Rev → Prop}
    (h : ∀ r : Rev, sint.Z r.main ≤ c → (K r ↔ K' r)) (r : Rev) (t : Bool) :
    hashIncl c rev K r t ↔ hashIncl c rev K' r t := by
  unfold hashIncl
  by_cases hr : c < sint.Z r.main
  · simp [hr]
  · have := h r (by omega)
    simp [hr, this]

/-! ### `Keep` and `Compact` at the same revision -/

/-- What compaction at `a` keeps of a key below `a`, `keep` at `a` keeps too: they differ only
at a tombstone ending a generation that is not the last, whose main is `a`. -/
theorem kiKeep_of_kiAvail_lt {a : w64} {ki : KeyIndex} {r : Rev} (h : kiAvail a ki = some r)
    (hlt : sint.Z r.main < sint.Z a) : kiKeep a ki = some r := by
  unfold kiKeep
  split
  · rename_i he; rw [kiAvail_isEmpty he] at h; cases h
  unfold kiAvail at h
  simp only at h ⊢
  generalize hgi : compactGenIdx a ki.gens = gi at *
  generalize hg : ki.gens.getD gi Gen.empty = g at *
  generalize hrid : genWalk g.revs (pAbove a) = ri at *
  split at h
  · cases h
  rename_i hri
  rw [ite_eq_right hri]
  split
  · rename_i hc
    exfalso
    obtain ⟨hne, hj, hgil⟩ := hc
    have hG : ki.gens ≠ [] := by
      intro hh; apply hne; rw [← hg, hh]; rfl
    have hlast : g.revs.getD ri.toNat Rev.zero = g.revs.getLastD Rev.zero := by
      rw [hj, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
      simp
    cases h
    rcases compactGenIdx_stop a ki.gens hG with h1 | h1
    · rw [hgi] at h1; omega
    · rw [hgi, hg] at h1; unfold tombZ at h1; rw [← hlast] at h1; omega
  · exact h

/-- **`Keep(rev)` and `Compact(rev)` agree below `rev`.** -/
theorem keepOf_iff_keepAt (log : Log) (rev : w64) (r : Rev) (hlt : sint.Z r.main < sint.Z rev) :
    (∃ k, kiKeep rev (kiOfKey (evsOf log) k) = some r) ↔ keepAt log (sint.Z rev) r := by
  unfold keepAt
  rw [show (W64 (sint.Z rev)) = rev by word]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rcases kiKeep_eq rev (kiOfKey (evsOf log) k) with h | h
    · rw [h] at hk; cases hk
    · rw [← h]; exact hk
  · rintro ⟨k, hk⟩
    exact ⟨k, kiKeep_of_kiAvail_lt hk hlt⟩

/-- **The two hashes of revision `rev` agree on every pair** (the PR's filter): `hashByRev`'s
(the kept set `treeIndex.Keep(rev)`) and the compaction job's at `rev` (the kept set
`treeIndex.Compact(rev)`), at a compaction revision `c` below `rev`. -/
theorem hashIncl_keep_compact (log : Log) (c : Int) (rev : w64) (hc : c < sint.Z rev)
    (A B : GMap Revision Unit) (hA : keepOfIs A log rev) (hB : keepSetIs B log (sint.Z rev))
    (r : Rev) (t : Bool) :
    hashIncl c (sint.Z rev) (keptBy A) r t ↔ hashIncl c (sint.Z rev) (keptBy B) r t := by
  apply hashIncl_congr
  intro r' hr'
  unfold keptBy
  rw [hA r', hB r']
  exact keepOf_iff_keepAt log rev r' (by omega)


/-- What `keep` at `c` keeps depends only on the log up to `c` (`kiAvail_prefix`'s twin). -/
theorem kiKeep_prefix (log log' : Log) (hpre : log <+: log') (hb' : LogB log') (c : Int)
    (hc0 : -1 ≤ c) (hc : c < log.length) (k : GoString) :
    kiKeep (W64 c) (kiOfKey (evsOf log') k) = kiKeep (W64 c) (kiOfKey (evsOf log) k) := by
  obtain ⟨t, rfl⟩ := hpre
  revert hb'
  refine snoc_induction (P := fun t => LogB (log ++ t) →
    kiKeep (W64 c) (kiOfKey (evsOf (log ++ t)) k) = kiKeep (W64 c) (kiOfKey (evsOf log) k)) ?_ ?_ t
  · intro _; rw [List.append_nil]
  intro t cs ih hb
  rw [← List.append_assoc] at hb ⊢
  rw [evsOf_append, kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  have hlen : (log ++ t).length + 1 < 2 ^ 63 := by have := hb.1; simp at this ⊢; omega
  rw [kiKeep_fold _ k _ _ (kiOfKey_struct k _).1]
  · exact ih hb.prefix
  · intro e he
    rw [evsOfRev_main _ cs e he]
    have hcb : c < 2 ^ 63 := by simp at hlen; omega
    have : sint.Z (W64 c) = c := by word
    have h2 : sint.Z (W64 ((log ++ t).length : Int)) = (log ++ t).length := by word
    rw [this, h2]; simp; omega

/-- **`hashIncl_keep_compact` for the real situation**: `HashKV`'s `Keep(rev)` read of one log
(the reader's), the compaction job's `Compact(rev)` of another (the job's, later or earlier), one
a prefix of the other, both past `rev`. -/
theorem hashIncl_keep_compact_logs (log₁ log₂ : Log) (hpre : log₁ <+: log₂ ∨ log₂ <+: log₁)
    (hb₁ : LogB log₁) (hb₂ : LogB log₂) (c : Int) (rev : w64) (h0 : 0 ≤ sint.Z rev)
    (hc : c < sint.Z rev) (h₁ : sint.Z rev < log₁.length) (h₂ : sint.Z rev < log₂.length)
    (A B : GMap Revision Unit) (hA : keepOfIs A log₁ rev) (hB : keepSetIs B log₂ (sint.Z rev))
    (r : Rev) (t : Bool) :
    hashIncl c (sint.Z rev) (keptBy A) r t ↔ hashIncl c (sint.Z rev) (keptBy B) r t := by
  have hw : W64 (sint.Z rev) = rev := by word
  have hB' : keepSetIs B log₁ (sint.Z rev) := by
    intro r'
    rw [hB r']
    unfold keepAt
    rcases hpre with hp | hp
    · simp only [kiAvail_prefix log₁ log₂ hp hb₂ (sint.Z rev) (by omega) h₁]
    · simp only [kiAvail_prefix log₂ log₁ hp hb₁ (sint.Z rev) (by omega) h₂]
  exact hashIncl_keep_compact log₁ c rev hc A B hA hB' r t

/-! ### What compaction may delete is not hashed -/

/-- What `keep` at `rev` keeps of a key at or below `c ≤ rev`, compaction at `c` keeps, when
revision `c` does not delete a key and put it again. -/
theorem kiKeep_avail (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c) (hc : c < log.length)
    (hnd : NoDelPutAt log c) (k : GoString) (rev : w64) (hcr : c ≤ sint.Z rev) (r : Rev)
    (hkeep : kiKeep rev (kiOfKey (evsOf log) k) = some r) (hr : sint.Z r.main ≤ c) :
    kiAvail (W64 c) (kiOfKey (evsOf log) k) = some r := by
  have hs := kiOfKey_KiS log hb k
  have hev := (kiOfKey_struct k (evsOf log)).2.2
  have hord := evsOf_ord log hb
  have hcw : sint.Z (W64 c) = c := by have := hb.1; word
  generalize hki : kiOfKey (evsOf log) k = ki at *
  unfold kiKeep at hkeep
  split at hkeep
  · cases hkeep
  simp only at hkeep
  generalize hgxd : compactGenIdx rev ki.gens = gx at *
  have hgxlt : gx < ki.gens.length := by rw [← hgxd]; exact compactGenIdx_lt rev _ hs.wf.ne
  generalize hg : ki.gens.getD gx Gen.empty = g at *
  rcases genWalk_pAbove_spec g.revs rev with ⟨hw, -⟩ | ⟨j, hj, hw, hjm, hjafter⟩
  · simp [hw] at hkeep
  rw [hw] at hkeep
  simp only [Int.toNat_natCast] at hkeep
  rw [ite_eq_right (by omega)] at hkeep
  split at hkeep
  · cases hkeep
  rename_i hnotlast
  simp only [Option.some.injEq] at hkeep
  rw [getD_lt _ hj] at hkeep
  subst hkeep
  have hrmem : g.revs[j] ∈ (ki.gens.getD gx Gen.empty).revs := by rw [hg]; exact List.getElem_mem hj
  -- `r` is not a tombstone ending a generation
  have hnottomb : ¬ (gx + 1 < ki.gens.length ∧ j + 1 = g.revs.length) := by
    rintro ⟨h1, h2⟩
    apply hnotlast
    refine ⟨fun h => by simp [h] at hj, by omega, by omega⟩
  have hidx : compactGenIdx (W64 c) ki.gens = gx := by
    apply compactGenIdx_eq _ _ _ hgxlt
    · intro j' hj'
      have hne' : (ki.gens.getD j' Gen.empty).revs ≠ [] := hs.wf.nonlast j' (by omega)
      have htm := getLastD_mem _ Rev.zero hne'
      have hlt := hs.cross hj' hgxlt htm hrmem
      unfold tombZ
      rw [hcw]
      have hle := Rev.lt_main_le hlt
      rcases Int.lt_or_eq_of_le (Int.le_trans hle hr) with h1 | h1
      · exact h1
      exfalso
      -- a delete and a put of the key in revision `c`
      generalize ht : (ki.gens.getD j' Gen.empty).revs.getLastD Rev.zero = tomb at *
      have hlenj := List.length_pos_iff.2 hne'
      have hgj : ki.gens[j']? = some (ki.gens.getD j' Gen.empty) := by
        rw [List.getElem?_eq_getElem (by omega), getD_lt _ (by omega)]
      have htp : (ki.gens.getD j' Gen.empty).revs[(ki.gens.getD j' Gen.empty).revs.length - 1]? = some tomb := by
        rw [← ht, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
      obtain ⟨e1, he1, he1r, he1k, he1t⟩ := hev j' _ _ tomb hgj htp
      have he1t' : e1.tomb = true := he1t.2 ⟨by omega, by omega⟩
      have hgx : ki.gens[gx]? = some g := by rw [← hg, List.getElem?_eq_getElem hgxlt, getD_lt _ hgxlt]
      obtain ⟨e2, he2, he2r, he2k, he2t⟩ := hev gx j g _ hgx (List.getElem?_eq_getElem hj)
      have he2t' : e2.tomb = false := by
        cases h' : e2.tomb
        · rfl
        · exact absurd (he2t.1 h') hnottomb
      have hc1 := change_of_tomb he1k he1t'
      obtain ⟨v2, l2, hc2⟩ := change_of_not_tomb he2k he2t'
      obtain ⟨-, -, hs1, cs1, hl1, hcs1⟩ := hord.2 e1 he1
      obtain ⟨-, -, hs2, cs2, hl2, hcs2⟩ := hord.2 e2 he2
      rw [he1r] at hl1 hcs1 hs1
      rw [he2r] at hl2 hcs2 hs2
      have hmeq : tomb.main = g.revs[j].main := by
        have : sint.Z tomb.main = sint.Z g.revs[j].main := by omega
        word
      rw [hmeq] at hl1
      rw [hl1] at hl2; cases hl2
      have hsub : sint.Z tomb.sub < sint.Z g.revs[j].sub := by
        rcases hlt with h3 | ⟨-, h3⟩
        · omega
        · exact h3
      have hcn : c.toNat = g.revs[j].main.toNat := by
        have : sint.Z g.revs[j].main = c := by omega
        have h0 : 0 ≤ c := by have := hs.mem_nonneg hgxlt hrmem; omega
        word
      rw [hc1] at hcs1
      rw [hc2] at hcs2
      exact hnd cs1 tomb.sub.toNat g.revs[j].sub.toNat k v2 l2
        (by have := hs.mem_nonneg hgxlt hrmem; omega) (by rw [hcn]; exact hl1) (by word) hcs1 hcs2
    · rcases compactGenIdx_stop rev ki.gens hs.wf.ne with h1 | h1
      · left; rw [hgxd] at h1; exact h1
      · right; rw [hgxd, hg] at h1; rw [hg, hcw]; omega
  unfold kiAvail
  simp only []
  rw [hidx, hg]
  have hwc : genWalk g.revs (pAbove (W64 c)) = j := by
    apply genWalk_eq_some j hj
    · simp only [pAbove, hcw, decide_eq_false_iff_not, Int.not_lt]; omega
    · intro k' hk' hjk'
      have := hjafter k' hk' hjk'
      simp only [pAbove, hcw, decide_eq_true_eq]; omega
  rw [hwc, ite_eq_right (by omega)]
  simp only [Int.toNat_natCast]
  rw [getD_lt _ hj]

/-- **What compaction at `c` may delete, `hashByRev` at `rev ≥ c` does not hash** (the PR's
filter, kept set `treeIndex.Keep(rev)`), when revision `c` does not delete a key and put it
again: the hash does not depend on how far compaction has gone. -/
theorem hashIncl_not_del (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c)
    (hnd : NoDelPutAt log c) (rev : w64) (hcr : c ≤ sint.Z rev)
    (A : GMap Revision Unit) (hA : keepOfIs A log rev) (r : Rev) (t : Bool)
    (hdel : KeyDel log c (revBytes r t)) :
    ¬ hashIncl c (sint.Z rev) (keptBy A) r t := by
  obtain ⟨hc, r', t', hk, h0, h1, hkeep⟩ := hdel
  have := revBytes_rev_inj hk
  subst this
  rintro ⟨-, h2 | h2, -⟩
  · omega
  · unfold keptBy at h2
    rw [hA r] at h2
    obtain ⟨k, hk'⟩ := h2
    exact hkeep ⟨k, kiKeep_avail log hb c hc0 hc hnd k rev hcr r hk' h1⟩

/-- The same of the compaction job's kept set `treeIndex.Compact(rev)`, `c < rev`. -/
theorem hashIncl_not_del_compact (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c)
    (hnd : NoDelPutAt log c) (rev : w64) (hcr : c < sint.Z rev)
    (A B : GMap Revision Unit) (hA : keepOfIs A log rev) (hB : keepSetIs B log (sint.Z rev))
    (r : Rev) (t : Bool) (hdel : KeyDel log c (revBytes r t)) :
    ¬ hashIncl c (sint.Z rev) (keptBy B) r t := by
  rw [← hashIncl_keep_compact log c rev hcr A B hA hB]
  exact hashIncl_not_del log hb c hc0 hnd rev (by omega) A hA r t hdel

/-- So the pairs hashed of a bucket are those hashed of it less any pairs compaction at `c` may
delete (`D`): the bucket's `Key` entries as revisions with their tombstone mark. -/
theorem hash_filter_del (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c)
    (hnd : NoDelPutAt log c) (rev : w64) (hcr : c ≤ sint.Z rev)
    (A : GMap Revision Unit) (hA : keepOfIs A log rev)
    (L : List (Rev × Bool)) (D : Rev × Bool → Prop) [DecidablePred D]
    (hD : ∀ x ∈ L, D x → KeyDel log c (revBytes x.1 x.2)) :
    L.filter (fun x => decide (hashIncl c (sint.Z rev) (keptBy A) x.1 x.2)) =
      (L.filter (fun x => !decide (D x))).filter
        (fun x => decide (hashIncl c (sint.Z rev) (keptBy A) x.1 x.2)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  by_cases hd : D x
  · have := hashIncl_not_del log hb c hc0 hnd rev hcr A hA x.1 x.2 (hD x hx hd)
    simp [this, hd]
  · simp [hd]

/-! ### The filter before the PR -/

/-- **What the PR changes** of the hash after a finished compaction: with nothing kept, a stored
revision at or below `c` (not a tombstone at `c`) was hashed and no longer is. After compaction
at `c` the bucket holds what it kept there (`keepAt log c`), so this is a revision kept at `c`
whose key was deleted by `rev` (`Keep(rev)` empty: no key live at `rev`); an older member and a
member with the PR then hash the same data differently. -/
theorem hashInclOld_empty_ne (c rev : Int) (K : Rev → Prop) (hK : ∀ r', ¬ K r') (r : Rev) (t : Bool)
    (hrev : sint.Z r.main ≤ rev) (hc : sint.Z r.main ≤ c) (ht : ¬ (sint.Z r.main = c ∧ t = true)) :
    hashInclOld c rev K r t ∧ ¬ hashIncl c rev K r t := by
  refine ⟨⟨hrev, Or.inr (Or.inl hK), ht⟩, ?_⟩
  rintro ⟨-, h | h, -⟩
  · omega
  · exact hK r h

/-- A key put at `(2, 0)` and deleted at `(3, 0)` (its generations: `[2, 3]` ended by the
tombstone, then an empty one). -/
def kiPutDel : KeyIndex :=
  { modified := ⟨W64 3, W64 0⟩,
    gens := [{ ver := W64 2, created := ⟨W64 2, W64 0⟩, revs := [⟨W64 2, W64 0⟩, ⟨W64 3, W64 0⟩] },
             Gen.empty] }

theorem kiPutDel_keep : kiKeep (W64 3) kiPutDel = none := by decide

theorem kiPutDel_avail : kiAvail (W64 3) kiPutDel = some ⟨W64 3, W64 0⟩ := by decide

/-- **The filter before the PR makes the two hashes differ**: of `kiPutDel` alone, `Keep(3)`
keeps nothing and `Compact(3)` keeps the tombstone, so at `c = 2` the put at `(2, 0)` (in the
bucket: compaction at 2 kept it) is hashed with the first and not with the second. -/
theorem hashInclOld_keep_compact_differ :
    let K₁ : Rev → Prop := fun r => kiKeep (W64 3) kiPutDel = some r
    let K₂ : Rev → Prop := fun r => kiAvail (W64 3) kiPutDel = some r
    hashInclOld 2 3 K₁ ⟨W64 2, W64 0⟩ false ∧ ¬ hashInclOld 2 3 K₂ ⟨W64 2, W64 0⟩ false ∧
    hashIncl 2 3 K₁ ⟨W64 2, W64 0⟩ false = hashIncl 2 3 K₂ ⟨W64 2, W64 0⟩ false := by
  simp only [hashInclOld, hashIncl, kiPutDel_keep, kiPutDel_avail]
  refine ⟨⟨by decide, Or.inr (Or.inl fun r h => by cases h), by decide⟩, ?_, ?_⟩
  · rintro ⟨-, h | h | h, -⟩
    · revert h; decide
    · exact h ⟨W64 3, W64 0⟩ rfl
    · cases h
  · apply propext
    constructor
    · rintro ⟨-, h | h, -⟩
      · revert h; decide
      · cases h
    · rintro ⟨-, h | h, -⟩
      · revert h; decide
      · cases h

/-! ### etcd-io/etcd#22515: `exactKeep`, and `hashByRev`'s fallback to `Keep(compactRev)`

#22515 (pr-verify/etcd-22515) keeps the hasher's `len(h.keep) > 0` guard but adds a flag
`exactKeep` that applies the kept set even when it is empty (`hashInclF`, the filter with flag
`exactKeep || len(keep) > 0`), and `hashByRev` (`hashByRevKeep` in the fork) passes
`Keep(compactRev)` with the flag set when `Keep(rev)` is empty and `compactRev > 0`
(`hashIncl22515`). The compaction job's hasher is unchanged (flag unset: `hashInclOld`). -/

/-- The filter with #22515's flag `f` (`exactKeep || len(keep) > 0`): below `c`, `K` filters only
when `f` is set. -/
def hashInclF (c rev : Int) (K : Rev → Prop) (f : Bool) (r : Rev) (t : Bool) : Prop :=
  sint.Z r.main ≤ rev ∧ (c < sint.Z r.main ∨ f = false ∨ K r) ∧ ¬ (sint.Z r.main = c ∧ t = true)

instance hashInclF_dec (c rev : Int) (K : Rev → Prop) [DecidablePred K] (f : Bool) (r : Rev)
    (t : Bool) : Decidable (hashInclF c rev K f r t) := by
  unfold hashInclF; infer_instance

/-- With the flag set, the filter is #22562's. -/
theorem hashInclF_true (c rev : Int) (K : Rev → Prop) (r : Rev) (t : Bool) :
    hashInclF c rev K true r t ↔ hashIncl c rev K r t := by
  simp [hashInclF, hashIncl]

/-- With the flag "the set is not empty", the filter is the one before both PRs. -/
theorem hashInclF_old (c rev : Int) (K : Rev → Prop) (f : Bool) (hf : f = true ↔ ∃ r', K r')
    (r : Rev) (t : Bool) : hashInclF c rev K f r t ↔ hashInclOld c rev K r t := by
  unfold hashInclF hashInclOld
  cases f
  · have : ∀ r', ¬ K r' := fun r' h => absurd (hf.2 ⟨r', h⟩) (by simp)
    simp [this]
  · obtain ⟨r', h⟩ := hf.1 rfl
    have : ¬ ∀ r', ¬ K r' := fun hn => hn r' h
    simp [this]

/-- `len(keep) > 0` of a kept set: it keeps some revision. -/
theorem keptBy_size (A : GMap Revision Unit) : 0 < GMap.size A ↔ ∃ r, keptBy A r := by
  constructor
  · intro h
    obtain ⟨k, v, hk⟩ := (GMap.map_size_ne_0_lookup A).1 (by omega)
    refine ⟨revOf k, ?_⟩
    unfold keptBy
    have : revVal (revOf k) = k := by cases k; rfl
    rw [this]
    exact Option.isSome_iff_exists.2 ⟨v, hk⟩
  · rintro ⟨r, hr⟩
    exact GMap.map_size_nonzero A (revVal r) hr

/-- `Keep(rev)` keeps `r` (the set `treeIndex.Keep(rev)` returns of the log: `keepOfIs`). -/
def keepRevOf (log : Log) (rev : w64) (r : Rev) : Prop :=
  ∃ k, kiKeep rev (kiOfKey (evsOf log) k) = some r

theorem keptBy_keepOfIs {A : GMap Revision Unit} {log : Log} {rev : w64} (hA : keepOfIs A log rev)
    (r : Rev) : keptBy A r ↔ keepRevOf log rev r := hA r

/-- **What `HashKV` hashes with #22515** (`hashByRev` at revision `rev`, compaction revision
`c`): with `Keep(rev)` if it keeps something; else, if `c > 0`, with `Keep(c)`, applied though
empty; else as before (`c ≤ 0`: nothing at or below `c` is stored). -/
def hashIncl22515 (log : Log) (c rev : w64) (r : Rev) (t : Bool) : Prop :=
  ((∃ r', keepRevOf log rev r') ∧ hashIncl (sint.Z c) (sint.Z rev) (keepRevOf log rev) r t) ∨
  ((∀ r', ¬ keepRevOf log rev r') ∧ 0 < sint.Z c ∧
      hashIncl (sint.Z c) (sint.Z rev) (keepRevOf log c) r t) ∨
  ((∀ r', ¬ keepRevOf log rev r') ∧ sint.Z c ≤ 0 ∧
      hashInclOld (sint.Z c) (sint.Z rev) (keepRevOf log rev) r t)

/-- **The code computes `hashIncl22515`**: `hashByRevKeep(rev, c)`'s result (`exact` and a set of
`Keep(c)` if `exact`, of `Keep(rev)` otherwise: its spec) given to `kvHashIncludes`
(`exactKeep || len(keep) > 0`: its spec). -/
theorem hashByRevKeep_filter (log : Log) (c rev : w64) (A : GMap Revision Unit) (ex : Bool)
    (hex : ex = true ↔ ((∀ r, ¬ keepRevOf log rev r) ∧ 0 < sint.Z c))
    (hA : keepOfIs A log (if ex then c else rev)) (r : Rev) (t : Bool) :
    hashInclF (sint.Z c) (sint.Z rev) (keptBy A) (ex || decide (0 < GMap.size A)) r t ↔
      hashIncl22515 log c rev r t := by
  have hK : keptBy A = keepRevOf log (if ex then c else rev) :=
    funext fun r => propext (keptBy_keepOfIs hA r)
  unfold hashIncl22515
  by_cases hn : ∃ r', keepRevOf log rev r'
  · obtain ⟨r₀, h₀⟩ := hn
    have hex' : ex = false := by
      cases ex
      · rfl
      · exact absurd h₀ ((hex.1 rfl).1 r₀)
    subst hex'
    simp only [Bool.false_eq_true, ite_false] at hK
    have hs : decide (0 < GMap.size A) = true := by
      rw [decide_eq_true_iff, keptBy_size, hK]; exact ⟨r₀, h₀⟩
    rw [Bool.false_or, hs, hashInclF_true, hK]
    constructor
    · intro h; exact Or.inl ⟨⟨r₀, h₀⟩, h⟩
    · rintro (⟨-, h⟩ | ⟨hn', -⟩ | ⟨hn', -⟩)
      · exact h
      · exact absurd h₀ (hn' r₀)
      · exact absurd h₀ (hn' r₀)
  · have hn' : ∀ r', ¬ keepRevOf log rev r' := fun r' h => hn ⟨r', h⟩
    by_cases hc : 0 < sint.Z c
    · have hex' : ex = true := hex.2 ⟨hn', hc⟩
      subst hex'
      simp only [ite_true] at hK
      rw [hK, Bool.true_or, hashInclF_true]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨hn', hc, h⟩)
      · rintro (⟨hh, -⟩ | ⟨-, -, h⟩ | ⟨-, hc', -⟩)
        · exact absurd hh hn
        · exact h
        · omega
    · have hex' : ex = false := by
        cases ex
        · rfl
        · exact absurd (hex.1 rfl).2 hc
      subst hex'
      simp only [Bool.false_eq_true, ite_false] at hK
      rw [Bool.false_or]
      rw [hashInclF_old _ _ _ _ (by rw [decide_eq_true_iff, keptBy_size, hK]), hK]
      have hc' : sint.Z c ≤ 0 := by omega
      constructor
      · intro h; exact Or.inr (Or.inr ⟨hn', hc', h⟩)
      · rintro (⟨hh, -⟩ | ⟨-, hc'', -⟩ | ⟨-, -, h⟩)
        · exact absurd hh hn
        · omega
        · exact h

/-- What `keep` at `rk ≥ c` keeps at or below `c`, compaction at `c` keeps (when revision `c` does
not delete a key and put it again), so the filter with it hashes nothing compaction at `c` may
delete, at any hashed revision (`hashIncl_not_del` with the kept set's revision apart from the
hasher's). -/
theorem hashIncl_not_del_at (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c)
    (hnd : NoDelPutAt log c) (rk : w64) (hcr : c ≤ sint.Z rk) (rev : Int) (r : Rev) (t : Bool)
    (hdel : KeyDel log c (revBytes r t)) :
    ¬ hashIncl c rev (keepRevOf log rk) r t := by
  obtain ⟨hc, r', t', hk, h0, h1, hkeep⟩ := hdel
  have := revBytes_rev_inj hk
  subst this
  rintro ⟨-, h2 | h2, -⟩
  · omega
  · obtain ⟨k, hk'⟩ := h2
    exact hkeep ⟨k, kiKeep_avail log hb c hc0 hc hnd k rk hcr r hk' h1⟩

/-- **#22515's `HashKV` hashes nothing compaction at `c` may delete** (so it does not depend on
how far that compaction has gone), when revision `c` does not delete a key and put it again,
and `c > 0` or `Keep(rev)` keeps something (`c ≤ 0`: the filter before the PR, which hashes
whatever is stored at or below `c`; etcd stores nothing at revision 0). -/
theorem hashIncl22515_not_del (log : Log) (hb : LogB log) (c rev : w64) (hc0 : -1 ≤ sint.Z c)
    (hnd : NoDelPutAt log (sint.Z c)) (hcr : sint.Z c ≤ sint.Z rev)
    (hpos : 0 < sint.Z c ∨ ∃ r', keepRevOf log rev r') (r : Rev) (t : Bool)
    (hdel : KeyDel log (sint.Z c) (revBytes r t)) :
    ¬ hashIncl22515 log c rev r t := by
  rintro (⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hn, hc, -⟩)
  · exact hashIncl_not_del_at log hb _ hc0 hnd rev hcr _ r t hdel h
  · exact hashIncl_not_del_at log hb _ hc0 hnd c (Int.le_refl _) _ r t hdel h
  · rcases hpos with h | ⟨r', h⟩
    · omega
    · exact hn r' h

/-- So #22515's `HashKV` filters a bucket the same with any part of what compaction at `c` may
delete gone (`hash_filter_del` of #22515's filter). -/
theorem hash22515_filter_del (log : Log) (hb : LogB log) (c rev : w64) (hc0 : -1 ≤ sint.Z c)
    (hnd : NoDelPutAt log (sint.Z c)) (hcr : sint.Z c ≤ sint.Z rev)
    (hpos : 0 < sint.Z c ∨ ∃ r', keepRevOf log rev r')
    (L : List (Rev × Bool)) (D : Rev × Bool → Prop) [DecidablePred D]
    (P : Rev → Bool → Prop) [∀ r t, Decidable (P r t)] (hP : ∀ r t, P r t ↔ hashIncl22515 log c rev r t)
    (hD : ∀ x ∈ L, D x → KeyDel log (sint.Z c) (revBytes x.1 x.2)) :
    L.filter (fun x => decide (P x.1 x.2)) =
      (L.filter (fun x => !decide (D x))).filter (fun x => decide (P x.1 x.2)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  by_cases hd : D x
  · have := hashIncl22515_not_del log hb c rev hc0 hnd hcr hpos x.1 x.2 (hD x hx hd)
    rw [← hP] at this
    simp [this, hd]
  · simp [hd]

/-- What compaction at `a` keeps of a key and is not a tombstone (no event of the revision is a
delete), `keep` at `a` keeps too (they differ only at a tombstone ending a generation that is not
the last). -/
theorem kiKeep_of_kiAvail_ntomb (log : Log) (hb : LogB log) (a : w64) (k : GoString) {r : Rev}
    (h : kiAvail a (kiOfKey (evsOf log) k) = some r)
    (hnt : ∀ e ∈ evsOf log, e.rev = r → e.tomb = false) :
    kiKeep a (kiOfKey (evsOf log) k) = some r := by
  have hs := kiOfKey_KiS log hb k
  have hev := (kiOfKey_struct k (evsOf log)).2.2
  generalize hki : kiOfKey (evsOf log) k = ki at *
  unfold kiKeep
  split
  · rename_i he; rw [kiAvail_isEmpty he] at h; cases h
  unfold kiAvail at h
  simp only at h ⊢
  generalize hgi : compactGenIdx a ki.gens = gi at *
  generalize hg : ki.gens.getD gi Gen.empty = g at *
  generalize hrid : genWalk g.revs (pAbove a) = ri at *
  split at h
  · cases h
  rename_i hri
  rw [ite_eq_right hri]
  split
  · rename_i hc
    exfalso
    obtain ⟨hne, hj, hgil⟩ := hc
    cases h
    have hgilt : gi < ki.gens.length := by rw [← hgi]; exact compactGenIdx_lt a _ hs.wf.ne
    have hgx : ki.gens[gi]? = some g := by
      rw [← hg, List.getElem?_eq_getElem hgilt, getD_lt _ hgilt]
    have hpos := List.length_pos_iff.2 hne
    have hlen : ri.toNat < g.revs.length := by omega
    have hget : g.revs[ri.toNat]? = some (g.revs.getD ri.toNat Rev.zero) := by
      rw [getD_lt _ hlen, List.getElem?_eq_getElem hlen]
    obtain ⟨e, he, her, -, het⟩ := hev gi ri.toNat g _ hgx hget
    have ht : e.tomb = true := het.2 ⟨by omega, by omega⟩
    rw [hnt e he her] at ht
    cases ht
  · exact h

/-- **#22515 keeps the hash after a finished compaction**: after compaction at `c` the bucket
holds, at or below `c`, what compaction kept (`keepAt log c`), each pair a revision of the log
with its event's tombstone mark; on such a pair #22515's `HashKV` filter is the filter before the
PR (`hashInclOld`, of `Keep(rev)`), so members with and without the PR agree on finished
compactions (contrast `hashInclOld_empty_ne`, #22562's change). -/
theorem hashIncl22515_compat (log : Log) (hb : LogB log) (c rev : w64)
    (hc : sint.Z c < log.length) (r : Rev) (t : Bool)
    (hstored : sint.Z r.main ≤ sint.Z c → keepAt log (sint.Z c) r)
    (hev : ∃ e ∈ evsOf log, e.rev = r ∧ e.tomb = t) :
    hashIncl22515 log c rev r t ↔ hashInclOld (sint.Z c) (sint.Z rev) (keepRevOf log rev) r t := by
  unfold hashIncl22515
  by_cases hn : ∃ r', keepRevOf log rev r'
  · obtain ⟨r₀, h₀⟩ := hn
    have hn' : ¬ ∀ r', ¬ keepRevOf log rev r' := fun h => h r₀ h₀
    constructor
    · rintro (⟨-, ⟨h1, h2, h3⟩⟩ | ⟨hh, -⟩ | ⟨hh, -⟩)
      · exact ⟨h1, h2.elim Or.inl (fun h => Or.inr (Or.inr h)), h3⟩
      · exact absurd hh hn'
      · exact absurd hh hn'
    · rintro ⟨h1, h2, h3⟩
      refine Or.inl ⟨⟨r₀, h₀⟩, h1, ?_, h3⟩
      rcases h2 with h | h | h
      · exact Or.inl h
      · exact absurd h hn'
      · exact Or.inr h
  · have hn' : ∀ r', ¬ keepRevOf log rev r' := fun r' h => hn ⟨r', h⟩
    by_cases hc0 : 0 < sint.Z c
    · constructor
      · rintro (⟨hh, -⟩ | ⟨-, -, ⟨h1, -, h3⟩⟩ | ⟨-, hc', -⟩)
        · exact absurd hh hn
        · exact ⟨h1, Or.inr (Or.inl hn'), h3⟩
        · omega
      · rintro ⟨h1, -, h3⟩
        refine Or.inr (Or.inl ⟨hn', hc0, h1, ?_, h3⟩)
        by_cases hlt : sint.Z c < sint.Z r.main
        · exact Or.inl hlt
        right
        obtain ⟨k, hk⟩ := hstored (by omega)
        have hw : W64 (sint.Z c) = c := by word
        rw [hw] at hk
        refine ⟨k, ?_⟩
        by_cases hlt' : sint.Z r.main < sint.Z c
        · exact kiKeep_of_kiAvail_lt hk hlt'
        · have hmc : sint.Z r.main = sint.Z c := by omega
          have ht : t = false := by
            cases t
            · rfl
            · exact absurd ⟨hmc, rfl⟩ h3
          obtain ⟨e, he, her, het⟩ := hev
          apply kiKeep_of_kiAvail_ntomb log hb c k hk
          intro e' he' her'
          rw [evsOf_rev_inj log hb he' he (by rw [her, her']), het, ht]
    · have hc0' : sint.Z c ≤ 0 := by omega
      constructor
      · rintro (⟨hh, -⟩ | ⟨-, hc', -⟩ | ⟨-, -, h⟩)
        · exact absurd hh hn
        · omega
        · exact h
      · intro h; exact Or.inr (Or.inr ⟨hn', hc0', h⟩)

theorem kiPutDel_keep2 : kiKeep (W64 2) kiPutDel = some ⟨W64 2, W64 0⟩ := by decide

/-- **#22515 leaves the mismatch of `HashKV` and the compaction's stored hash**
(`issues/etcd-hash-empty-keep.md`, symptom 1): of `kiPutDel` alone at `c = 2`, `rev = 3`,
`Keep(3)` keeps nothing, so `HashKV(3)` falls back to `Keep(2)`, which keeps the put at `(2, 0)`,
and hashes it; the compaction job at 3 (its hasher without the flag: `hashInclOld`, with
`Compact(3)`, which keeps the tombstone) does not. -/
theorem hashIncl22515_keep_compact_differ :
    let K₁ : Rev → Prop := fun r => kiKeep (W64 3) kiPutDel = some r
    let Kc : Rev → Prop := fun r => kiKeep (W64 2) kiPutDel = some r
    let K₂ : Rev → Prop := fun r => kiAvail (W64 3) kiPutDel = some r
    (∀ r, ¬ K₁ r) ∧ hashIncl 2 3 Kc ⟨W64 2, W64 0⟩ false ∧
      ¬ hashInclOld 2 3 K₂ ⟨W64 2, W64 0⟩ false := by
  intro K₁ Kc K₂
  refine ⟨fun r h => ?_, ?_, hashInclOld_keep_compact_differ.2.1⟩
  · have h' : kiKeep (W64 3) kiPutDel = some r := h
    rw [kiPutDel_keep] at h'; cases h'
  · refine ⟨by decide, Or.inr kiPutDel_keep2, by decide⟩

end hash

end mvcc
end EtcdGrove
end Perennial
