/-
U7j (`notes/bbolt-proof-plan.md`): **`wOK` after `CreateBucket`'s put** (`c.node().put(newKey,
newKey, value, 0, BucketLeafFlag)` into the root bucket's leaf where the new name lands): by U7i's
`wOK_setLeaf` at the root bucket. The new entry is a bucket entry (the root's leaves hold buckets
only) whose value is the empty inline bucket (`emptyBktVal`, `bvalOK`), its name within
`MaxKeySize` (the public spec's premise) and within the leaf's bounds (`leafFor`); the root's
opened buckets keep their entries (`entryIn_createPut`: the name is not opened, being absent from
the data, and a leaf's change leaves the page positions alone).
-/
module

public import Proof.go_etcd_io.bbolt.Write.WOkLeaf
public import Proof.go_etcd_io.bbolt.Write.CreateBktVal
public import Proof.go_etcd_io.bbolt.Write.Data

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section createbktok
variable [GooseExts]

/-- An entry of a key other than `e.key` stays in `wsPut`. -/
theorem mem_wsPut_of_ne (ws : List WEntry) (e w : WEntry) (hs : wsPw ws) (hw : w ∈ ws)
    (hk : w.key ≠ e.key) : w ∈ wsPut ws e := by
  have : w ∈ ws.filter (fun w => decide (w.key ≠ e.key)) := List.mem_filter.2 ⟨hw, by simpa using hk⟩
  rw [← filter_lt_gt ws e.key hs] at this
  rw [wsPut_split]
  rcases List.mem_append.1 this with h | h
  · exact List.mem_append.2 (Or.inl h)
  · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h))

/-- **A leaf's entries replaced by a superset (but for one key) keeps `entryIn`** of the other
keys. -/
theorem entryIn_setLeaf (vw : View) (B : BRec) (l : Loc) (r r' : NRec) (k n v : List w8)
    (hr : B.ns !! l = some r) (hlf : r.nv.isLeaf' = true) (hlf' : r'.nv.isLeaf' = true)
    (hsub : ∀ w ∈ r.ws, w.key ≠ n → w ∈ r'.ws) (hkn : k ≠ n) (h : entryIn vw B k v) :
    entryIn vw { B with ns := B.ns.insert l r' } k v := by
  rcases h with ⟨l0, r0, w, hr0, hl0, hw, hk, hf, hv⟩ |
    ⟨c, p, pg, i, hpr, hown, hpg, hfl, hi, hkey, hbf, hval⟩
  · left
    by_cases e : l0 = l
    · subst e
      rw [hr] at hr0; cases hr0
      refine ⟨l0, r', w, by simp, hlf', hsub w hw (by rw [hk]; exact hkn), hk, hf, hv⟩
    · exact ⟨l0, r0, w, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hr0, hl0, hw, hk, hf, hv⟩
  · right
    refine ⟨c, p, pg, i, ?_, hown, hpg, hfl, hi, hkey, hbf, hval⟩
    rcases hpr with h1 | ⟨l1, i1, ⟨r1, w1, hr1, hl1, hw1, hp1, hn1⟩, hlt⟩
    · exact Or.inl h1
    · right
      have hne : l1 ≠ l := by
        intro e; subst e; rw [hr] at hr1; cases hr1; rw [hlf] at hl1; cases hl1
      exact ⟨l1, i1, ⟨r1, w1, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hr1, hl1, hw1,
        hp1, hn1⟩, hlt⟩

/-- **`wOK` after `CreateBucket`'s put** (see the module doc). -/
theorem wOK_createPut (X : WX) (l : Loc) (B : BRec) (r : NRec) (e : WEntry) (ib : InBucket)
    (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hd : objsDisj X.t) (hlf : leafFor X X.rl e.key l)
    (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r)
    (hnew : bktLoc X e.key = none) (hnr : ∀ k c, B.bm !! k = some c → c ≠ X.rl)
    (hk : 0 < e.key.length) (hkm : e.key.length ≤ maxKeySize) (hfl : isBktFlag e.flags)
    (hval : e.value = emptyBktVal ib) (h0 : ib.root' = W64 0) (hpg : e.pgid = W64 0)
    (hks : e.ks ≠ Src.stale) (hvs : e.vs = Src.own DFrac.discard)
    (hins : ins.length = (wsPutAt r.ws e.key e).length) :
    wOK (X.setNode X.rl l (r.withEnts s ins (wsPutAt r.ws e.key e))) := by
  obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, hbk, hkin⟩ := hlf
  obtain rfl : B0 = B := (Option.some.inj (hB0.symm.trans hB))
  obtain rfl : r0 = r := (Option.some.inj (hr0.symm.trans hr))
  have hcl := ((hok.1.2.2.2.2.2 X.rl B0 hB).1).2.2.2.2.2.2.2.1 l r0 hr
  have hpw : wsPw r0.ws := wsSorted_pw _ hcl.2.2.2.1
  have hput : wsPutAt r0.ws e.key e = wsPut r0.ws e := wsPutAt_wsPut _ _ hpw
  have hmem := fun w (hw : w ∈ (r0.withEnts s ins (wsPutAt r0.ws e.key e)).ws) =>
    mem_wsPutAt' (show w ∈ wsPutAt r0.ws e.key e from hw)
  have hlen : e.value.length = 32 := by rw [hval]; exact emptyBktVal_length ib
  have hroot0 : inBucketRoot e.value = 0 := by rw [hval]; exact emptyBktVal_root ib h0
  apply wOK_setLeaf X X.rl l B0 r0 _ bnd hok hd hB hr hlf0 (sameShapeU_withEnts r0 s ins _) hbk
  · exact hins
  · show wsSorted (wsPutAt r0.ws e.key e)
    rw [hput]; exact wsSorted_of_pw _ (wsPw_wsPut _ _ hpw)
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact hcl.2.2.2.2.2.1 w h
    · exact ⟨hks, by rw [hvs]; intro h; cases h⟩
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact (hok.2.2.2.1 X.rl B0 hB l r0 hr w h)
    · refine ⟨hk, ?_, fun _ => hkm⟩
      rw [hlen]; unfold bboltEntryMax maxKeySize at *; omega
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact hok.1.2.1.2.2.1 X.rl B0 hB l r0 hr hlf0 w h
    · exact ⟨fun _ => rfl, fun _ => hfl⟩
  · intro w hw hf
    rcases hmem w hw with h | rfl
    · exact hcl.2.2.2.2.2.2.2.2.2.2.2.1 hlf0 w h hf
    · exact ⟨fun _ => by rw [hval]; exact emptyBktVal_ok _ _ ib h0, Or.inr hvs⟩
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact (hbk.2.2 l r0 hr).1 w h
    · exact hkin
  · intro w hw hf hne hno
    rcases hmem w hw with h | rfl
    · exact (hbk.2.2 l r0 hr).2.2.2.2.2 hlf0 w h hf hne hno
    · exact absurd hroot0 hne
  · intro w hw
    rcases hmem w hw with h | rfl
    · exact ((hok.2.2.1 X.rl B0 hB l r0 hr).1 hlf0).1 w h
    · exact hpg
  · intro _ _
    show 0 < (wsPutAt r0.ws e.key e).length
    rw [hput, wsPut_split]; simp only [List.length_append, List.length_cons]; omega
  · -- the root's opened buckets keep their entries
    intro k c hkc
    obtain ⟨C, v, hC, hin, h16, hgood, hroot, hib, hipg⟩ := (hok.2.1 X.rl B0 hB).2 k c hkc
    have hkn : k ≠ e.key := by
      intro hke; subst hke
      unfold bktLoc at hnew; rw [hB] at hnew; simp only [Option.bind_some] at hnew
      rw [hnew] at hkc; cases hkc
    have hcr : c ≠ X.rl := hnr k c hkc
    refine ⟨C, v, ?_, ?_, h16, hgood, hroot, hib, hipg⟩
    · show (X.t.bs.insert X.rl _) !! c = some C
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hcr)]; exact hC
    · show entryIn X.v { B0 with ns := B0.ns.insert l (r0.withEnts s ins (wsPutAt r0.ws e.key e)) } k v
      apply entryIn_setLeaf X.v B0 l r0 _ k e.key v hr hlf0 (by simpa [NRec.withEnts] using hlf0)
        _ hkn hin
      intro w hw hwk
      show w ∈ wsPutAt r0.ws e.key e
      rw [hput]; exact mem_wsPut_of_ne _ _ _ hpw hw hwk

end createbktok

end Write

end bbolt
end EtcdGrove
end Perennial
