/-
**Compaction keeps every change of a revision that writes each key once** (watches across a
compaction, the Probe, 2026-11-01; `notes/watch-compaction-plan.md`). Compaction at `c` keeps, of
each key, its latest change at or below `c` (`kiAvail`); when revision `c` changes a key twice the
earlier change is dropped (`issues/etcd-compaction-delete-then-put.md`,
`issues/etcd-txn-check-intervals-sibling.md`), so a watch from `c` would miss it. With each key
changed at most once at `c` (`oneChangePerKeyAt`), nothing at `c` is dropped: a bucket key
compaction at `c` may delete (`KeyDel`) has a main below `c` (`KeyDel_lt_of_noDup`), which is what
`rangeEvents` from the compaction revision needs.

* `kiAvail_unique` (the key index): a key's only revision with main `c` is the one compaction
  keeps.
* `keepAt_of_noDup` (the log): with revision `c` changing each key once, compaction at `c` keeps
  every revision at `c` of a key's index; `KeyDel_lt_of_noDup`: a deletable bucket key of such a
  revision is below `c`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- Revision `c` of the log changes each key at most once (pure). -/
def oneChangePerKeyAt (log : Log) (c : Int) : Prop :=
  ∀ cs, 0 ≤ c → log[c.toNat]? = some cs → (cs.map Change.key).Nodup

/-- Every revision of the log changes each key at most once. -/
def oneChangePerKey (log : Log) : Prop := ∀ c : Int, oneChangePerKeyAt log c

theorem Rev.lt_irrefl' (a : Rev) : ¬ Rev.lt a a := by
  rintro (h | ⟨-, h⟩) <;> omega

/-- **A key's only revision at main `c` is the one compaction at `c` keeps** (the key index):
for a structured key index (`KiS`) whose revision `r` (generation `gx`, position `j`) is the only
one with main `c`, `doCompact` stops at `r`'s generation (an earlier generation's tombstone is
below `r`, so below `c`; a later generation would need a re-creation at `c`, a second revision at
`c`) and walks to `r` (a later revision of its generation is above `c`). -/
theorem kiAvail_unique {ki : KeyIndex} (hs : KiS ki) (c : w64) {gx j : Nat}
    (hgx : gx < ki.gens.length) (hj : j < (ki.gens.getD gx Gen.empty).revs.length)
    (hr : sint.Z ((ki.gens.getD gx Gen.empty).revs[j]).main = sint.Z c)
    (huniq : ∀ r' ∈ kiRevs ki, sint.Z r'.main = sint.Z c →
      r' = (ki.gens.getD gx Gen.empty).revs[j]) :
    kiAvail c ki = some (ki.gens.getD gx Gen.empty).revs[j] := by
  have hmemg : ∀ {i : Nat} (_ : i < ki.gens.length) {x : Rev},
      x ∈ (ki.gens.getD i Gen.empty).revs → x ∈ kiRevs ki := by
    intro i hi x hx
    exact kiRevs_mem (g := ki.gens.getD i Gen.empty) (by rw [getD_lt _ hi]; exact List.getElem_mem hi) hx
  generalize hg : ki.gens.getD gx Gen.empty = g at *
  have hrmem : g.revs[j] ∈ (ki.gens.getD gx Gen.empty).revs := by
    rw [hg]; exact List.getElem_mem hj
  have hsg : g.revs.Pairwise Rev.lt := by rw [← hg]; exact hs.gen_sorted hgx
  have hidx : compactGenIdx c ki.gens = gx := by
    apply compactGenIdx_eq _ _ _ hgx
    · intro j' hj'
      have hne' : (ki.gens.getD j' Gen.empty).revs ≠ [] := hs.wf.nonlast j' (by omega)
      have htm := getLastD_mem _ Rev.zero hne'
      have hlt := hs.cross hj' hgx htm hrmem
      have hle := Rev.lt_main_le hlt
      apply genAdv_of_lt
      unfold tombZ
      rcases Int.lt_or_eq_of_le (Int.le_trans hle (Int.le_of_eq hr)) with h1 | h1
      · exact h1
      · exfalso
        have he := huniq _ (hmemg (by omega) htm) h1
        rw [he] at hlt
        exact Rev.lt_irrefl' _ hlt
    · by_cases hl : gx + 1 = ki.gens.length
      · exact Or.inl hl
      · right
        have hne : g.revs ≠ [] := List.ne_nil_of_mem (List.getElem_mem hj)
        have hlast : g.revs.getLastD Rev.zero = g.revs[g.revs.length - 1]'(by
            have := List.length_pos_iff.2 hne; omega) := by
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
          rfl
        have htle : sint.Z g.revs[j].main ≤ sint.Z (g.revs.getLastD Rev.zero).main := by
          rw [hlast]; exact sorted_main_le hsg (by omega) _
        rcases Int.lt_or_eq_of_le (Int.le_trans (Int.le_of_eq hr.symm) htle) with h1 | h1
        · rw [hg]; apply genAdv_ge; unfold tombZ; exact h1
        · -- the tombstone at `c` is `r` itself; a re-creation at `c` would be a second revision
          have hn1 : gx + 1 < ki.gens.length := by omega
          rw [hg]
          unfold genAdv genRecreatedAt
          rcases hf : (ki.gens.getD (gx + 1) Gen.empty).revs with _ | ⟨f, fs⟩
          · simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
              or_true, and_true]
            unfold tombZ; omega
          simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          refine ⟨by unfold tombZ; omega, Or.inr ?_⟩
          intro hfc
          have hfmem : f ∈ (ki.gens.getD (gx + 1) Gen.empty).revs := by
            rw [hf]; exact List.mem_cons_self
          have he := huniq f (hmemg hn1 hfmem) hfc
          have hlt := hs.cross (Nat.lt_succ_self gx) hn1 hrmem hfmem
          rw [he] at hlt
          exact Rev.lt_irrefl' _ hlt
  unfold kiAvail
  simp only []
  rw [hidx, hg]
  have hwc : genWalk g.revs (pAbove c) = j := by
    apply genWalk_eq_some j hj
    · simp only [pAbove, hr, decide_eq_false_iff_not]; omega
    · intro k hk hjk
      simp only [pAbove, decide_eq_true_eq]
      have hle := sorted_main_le hsg (Nat.le_of_lt hjk) hk
      rcases Int.lt_or_eq_of_le (Int.le_trans (Int.le_of_eq hr.symm) hle) with h1 | h1
      · exact h1
      · exfalso
        have hkmem : g.revs[k] ∈ (ki.gens.getD gx Gen.empty).revs := by
          rw [hg]; exact List.getElem_mem hk
        have he := huniq _ (hmemg hgx hkmem) h1.symm
        have hlt := List.pairwise_iff_getElem.1 hsg j k hj hk hjk
        rw [← he] at hlt
        exact Rev.lt_irrefl' _ hlt
  rw [hwc, ite_eq_right (by omega)]
  simp only [Int.toNat_natCast]
  rw [getD_lt _ hj]

/-- Two events of one key at revision `c` of a log whose revision `c` changes each key once are
one event. -/
theorem ev_unique_of_noDup (log : Log) (hb : LogB log) (c : Int) (hnd : oneChangePerKeyAt log c)
    {e1 e2 : Ev} (h1 : e1 ∈ evsOf log) (h2 : e2 ∈ evsOf log) (hk : e1.key = e2.key)
    (hm1 : sint.Z e1.rev.main = c) (hm2 : sint.Z e2.rev.main = c) : e1 = e2 := by
  obtain ⟨-, o2⟩ := evsOf_ord log hb
  obtain ⟨a0, -, s0, cs1, hcs1, hx1⟩ := o2 e1 h1
  obtain ⟨-, -, s0', cs2, hcs2, hx2⟩ := o2 e2 h2
  have hmeq : e1.rev.main = e2.rev.main := by
    apply BitVec.eq_of_toInt_eq
    have h1' : sint.Z e1.rev.main = e1.rev.main.toInt := rfl
    have h2' : sint.Z e2.rev.main = e2.rev.main.toInt := rfl
    omega
  rw [hmeq] at hcs1
  rw [hcs1] at hcs2
  cases hcs2
  have hcN : (e2.rev.main.toNat : Int) = c := by
    have h2' : sint.Z e2.rev.main = e2.rev.main.toInt := rfl
    have := BitVec.toInt_eq_toNat_of_msb (x := e2.rev.main)
    rw [← hm2, h2']
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · rfl
    · rename_i hh
      have : 0 ≤ e2.rev.main.toInt := by rw [← h2']; omega
      rw [BitVec.toInt_eq_toNat_cond] at this
      simp only [hh, ↓reduceIte] at this
      omega
  have hcs : log[c.toNat]? = some cs1 := by
    have : c.toNat = e2.rev.main.toNat := by omega
    rw [this]; exact hcs1
  have hnd' := hnd cs1 (by omega) hcs
  have hi1 := (List.getElem?_eq_some_iff.1 hx1)
  have hi2 := (List.getElem?_eq_some_iff.1 hx2)
  have hsub : e1.rev.sub.toNat = e2.rev.sub.toNat := by
    obtain ⟨hl1, he1⟩ := hi1
    obtain ⟨hl2, he2⟩ := hi2
    have hm1' : (cs1.map Change.key)[e1.rev.sub.toNat]'(by simp; exact hl1) =
        (cs1.map Change.key)[e2.rev.sub.toNat]'(by simp; exact hl2) := by
      simp only [List.getElem_map, he1, he2]; exact hk
    exact List.Nodup.eq_of_getElem_eq hnd' _ _ hm1'
  have hseq : e1.rev.sub = e2.rev.sub := BitVec.eq_of_toNat_eq hsub
  have hceq : e1.change = e2.change := by
    rw [hsub] at hx1; rw [hx1] at hx2; exact Option.some.inj hx2
  obtain ⟨⟨m1, s1⟩, ch1⟩ := e1
  obtain ⟨⟨m2, s2⟩, ch2⟩ := e2
  simp only at hmeq hseq hceq
  subst hmeq hseq hceq
  rfl

/-- **Compaction at `c` keeps every revision at `c` of a key's index** when revision `c` changes
each key once. -/
theorem keepAt_of_noDup (log : Log) (hb : LogB log) (c : Int) (hc0 : 0 ≤ c)
    (hnd : oneChangePerKeyAt log c) (k : GoString) (r : Rev)
    (hr : r ∈ kiRevs (kiOfKey (evsOf log) k)) (hm : sint.Z r.main = c) : keepAt log c r := by
  have hs := kiOfKey_KiS log hb k
  generalize hki : kiOfKey (evsOf log) k = ki at *
  have hcw : sint.Z (W64 c) = c := by
    have := hb.1
    have : c < 2 ^ 63 := by
      obtain ⟨e, he, rfl, -⟩ := kiRevs_kiOfKey (hki ▸ hr)
      have := (evsOf_ord log hb).2 e he
      omega
    word
  unfold kiRevs at hr
  rw [List.mem_flatten] at hr
  obtain ⟨rs, hrs, hrr⟩ := hr
  rw [List.mem_map] at hrs
  obtain ⟨g, hg, rfl⟩ := hrs
  obtain ⟨gx, hgx, hgxe⟩ := List.getElem_of_mem hg
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hrr
  have hgd : ki.gens.getD gx Gen.empty = g := by rw [getD_lt _ hgx, hgxe]
  refine ⟨k, ?_⟩
  have hj' : j < (ki.gens.getD gx Gen.empty).revs.length := by rw [hgd]; exact hj
  have hrj : (ki.gens.getD gx Gen.empty).revs[j] = r := by simp only [hgd]; exact hje
  rw [hki, ← hrj]
  apply kiAvail_unique hs (W64 c) hgx hj'
  · rw [hrj, hcw, hm]
  · intro r' hr' hm'
    rw [hrj]
    rw [hcw] at hm'
    obtain ⟨e1, he1, hr1, hk1⟩ := kiRevs_kiOfKey (hki ▸ hr')
    obtain ⟨e2, he2, hr2, hk2⟩ := kiRevs_kiOfKey (k := k) (r := r) (by
      rw [hki]; unfold kiRevs; rw [List.mem_flatten]
      exact ⟨g.revs, List.mem_map_of_mem hg, hrr⟩)
    have := ev_unique_of_noDup log hb c hnd he1 he2 (hk1.trans hk2.symm)
      (by rw [hr1]; exact hm') (by rw [hr2]; exact hm)
    rw [← hr1, ← hr2, this]

/-- **A bucket key at revision `c` of a key's index is not one compaction at `c` may delete**,
when revision `c` changes each key once: so a scan from the compaction revision reads every
revision at or above it (`rangeEvents` from `minRev = c`, watches across a compaction). -/
theorem not_KeyDel_of_noDup (log : Log) (hb : LogB log) (c : Int) (hc0 : 0 ≤ c)
    (hnd : oneChangePerKeyAt log c) (k : GoString) (r : Rev)
    (hr : r ∈ kiRevs (kiOfKey (evsOf log) k)) (hm : sint.Z r.main = c) (t : Bool) :
    ¬ KeyDel log c (revBytes r t) := by
  rintro ⟨-, r', t', hk, -, -, hkeep⟩
  have := revBytes_rev_inj hk
  subst this
  exact hkeep (keepAt_of_noDup log hb c hc0 hnd k r hr hm)

end mvcc
end EtcdGrove
end Perennial
