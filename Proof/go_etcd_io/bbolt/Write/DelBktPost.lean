/-
U7p (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s post, its parts** (for `Write/DelBktPure`'s
`dbk_post`). After `c.node().del(newKey)` in the root bucket's leaf `l` where the name `n` lands:
- `wOK_delRoot`: the records stay well-formed (`wOK_setLeaf` at the root; the root's opened
  buckets keep their entries, `n` being unopened);
- `rootEnts_delRoot`, `wtxData_delRoot`: the root's bucket entries lose `n` alone (no other block
  holds `n`, `leafFor_blocks`), so the data loses `n`;
- `leaves_congr`: two well-formed records with one logical tree of a bucket have its leaves (the
  walks' fuel aside: `rtOK_init`, `ltIs_det`), for the data across `delMid`.
-/
module

public import Proof.go_etcd_io.bbolt.Write.CreateBktOK
public import Proof.go_etcd_io.bbolt.Write.CreateBktData
public import Proof.go_etcd_io.bbolt.Write.DataBkt
public import Proof.go_etcd_io.bbolt.Write.DelBktWOk
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeRep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section delpost
variable [GooseExts]

/-- An entry of another key stays in `wsDelAt`. -/
theorem mem_wsDelAt_of_ne (ws : List WEntry) (k : List w8) (w : WEntry) (hw : w ∈ ws)
    (hk : w.key ≠ k) : w ∈ wsDelAt ws k := by
  unfold wsDelAt
  split
  · rename_i hf
    rw [← List.eraseIdx_eq_take_drop_succ, List.mem_eraseIdx_iff_getElem]
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    refine ⟨i, hi, ?_, rfl⟩
    rintro rfl
    unfold wsFound at hf
    rw [List.getElem?_eq_getElem hi] at hf
    simp only [Option.map_some, Option.some.injEq] at hf
    exact hk hf
  · exact hw

/-- **`wOK` after the root's entry `n` is deleted** (see the module doc). -/
theorem wOK_delRoot (X : WX) (l : Loc) (B : BRec) (r : NRec) (n : List w8) (s : GoSlice)
    (ins : List Inode) (hok : wOK X) (hd : objsDisj X.t) (hlf : leafFor X X.rl n l)
    (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r) (hbmn : B.bm !! n = none)
    (hnr : ∀ k c, B.bm !! k = some c → c ≠ X.rl)
    (hins : ins.length = (wsDelAt r.ws n).length) :
    wOK (X.setNode X.rl l (r.withEntsU s ins (wsDelAt r.ws n) true)) := by
  obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, hbk, -⟩ := hlf
  obtain rfl : B0 = B := (Option.some.inj (hB0.symm.trans hB))
  obtain rfl : r0 = r := (Option.some.inj (hr0.symm.trans hr))
  have hcl := ((hok.1.2.2.2.2.2 X.rl B0 hB).1).2.2.2.2.2.2.2.1 l r0 hr
  have hsub := wsDelAt_sublist r0.ws n
  have hmem : ∀ w ∈ (r0.withEntsU s ins (wsDelAt r0.ws n) true).ws, w ∈ r0.ws :=
    fun w hw => hsub.subset hw
  apply wOK_setLeaf X X.rl l B0 r0 _ bnd hok hd hB hr hlf0 (sameShapeU_withEntsU r0 s ins _ true) hbk
  · exact hins
  · show wsSorted (wsDelAt r0.ws n)
    exact wsSorted_of_pw _ ((wsSorted_pw _ hcl.2.2.2.1).sublist hsub)
  · intro w hw; exact hcl.2.2.2.2.2.1 w (hmem w hw)
  · intro w hw; exact hok.2.2.2.1 X.rl B0 hB l r0 hr w (hmem w hw)
  · intro w hw; exact hok.1.2.1.2.2.1 X.rl B0 hB l r0 hr hlf0 w (hmem w hw)
  · intro w hw hf; exact hcl.2.2.2.2.2.2.2.2.2.2.2.1 hlf0 w (hmem w hw) hf
  · intro w hw; exact (hbk.2.2 l r0 hr).1 w (hmem w hw)
  · intro w hw hf hne hno; exact (hbk.2.2 l r0 hr).2.2.2.2.2 hlf0 w (hmem w hw) hf hne hno
  · intro w hw; exact ((hok.2.2.1 X.rl B0 hB l r0 hr).1 hlf0).1 w (hmem w hw)
  · intro h; cases h
  · intro k c hkc
    obtain ⟨C, v, hC, hin, hrest⟩ := (hok.2.1 X.rl B0 hB).2 k c hkc
    have hkn : k ≠ n := by intro e; subst e; rw [hbmn] at hkc; cases hkc
    have hcr := hnr k c hkc
    refine ⟨C, v, ?_, ?_, hrest⟩
    · show (X.t.bs.insert X.rl _) !! c = some C
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hcr)]; exact hC
    · apply entryIn_setLeaf X.v B0 l r0 _ k n v hr hlf0 (by simpa [NRec.withEntsU] using hlf0) _
        hkn hin
      intro w hw hwk
      exact mem_wsDelAt_of_ne r0.ws n w hw hwk

/-- **The root's bucket entries after the delete**: those of key `n` gone, the others kept. -/
theorem rootEnts_delRoot (X : WX) (l : Loc) (B : BRec) (r : NRec) (bnd : Loc → Bnd) (n : List w8)
    (hok : wOK X) (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (hbk : bktKeysB X.v B bnd)
    (hkin : keyIn (bnd l).1 (bnd l).2 n) :
    rootEnts (X.withWs X.rl l (wsDel r.ws n)) = (rootEnts X).filter fun x => decide (x.1 ≠ n) := by
  obtain ⟨-, h2⟩ := leafFor_blocks X X.rl l n B r bnd hok hB hr hleaf hbk hkin
  rw [rootEnts_blocks]
  have hrl : (X.withWs X.rl l (wsDel r.ws n)).rl = X.rl := rfl
  rw [hrl, withWs_blocks X X.rl l (wsDel r.ws n) B r hB hr hleaf X.rl, List.flatMap_map,
    rootEnts_blocks, List.filter_flatMap]
  apply fm_congr; intro x hx
  by_cases h : resolve B x.1 = some l
  · simp only [h, and_self, decide_true, ↓reduceIte]
    rw [block_ws X X.rl l B r hB hr _ _ _ x hx h]
    unfold wsDel; exact filterMap_bktOf_filter r.ws n
  · simp only [h, and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    symm
    apply List.filter_eq_self.2
    intro y hy
    obtain ⟨w, hw, hwy⟩ := List.mem_filterMap.1 hy
    have hk := h2 x hx (by simp [h]) w hw
    rw [bktOf_key w y hwy]; simpa using hk

/-- **The data after the root's entry `n` is deleted** loses `n`. -/
theorem wtxData_delRoot (X : WX) (l : Loc) (B : BRec) (r : NRec) (bnd : Loc → Bnd) (n : List w8)
    (hok : wOK X) (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (hbk : bktKeysB X.v B bnd)
    (hkin : keyIn (bnd l).1 (bnd l).2 n)
    (hnr : ∀ m c, bktLoc X m = some c → c ≠ X.rl) :
    wtxData (X.withWs X.rl l (wsDel r.ws n)) = (wtxData X).delete n := by
  have hblk : ∀ c, c ≠ X.rl → lbktEnts (X.withWs X.rl l (wsDel r.ws n)) c = lbktEnts X c := by
    intro c hc
    rw [lbktEnts_blocks, lbktEnts_blocks, withWs_blocks X X.rl l (wsDel r.ws n) B r hB hr hleaf c,
      List.flatMap_map]
    apply fm_congr; intro x _; simp [hc]
  have hloc' : ∀ m, bktLoc (X.withWs X.rl l (wsDel r.ws n)) m = bktLoc X m :=
    withWs_bktLoc X X.rl l _ B r hB hr
  have hdo : ∀ m v, bktDataOf (X.withWs X.rl l (wsDel r.ws n)) m v = bktDataOf X m v := by
    intro m v
    rw [bktDataOf_eq, bktDataOf_eq, hloc']
    cases hc : bktLoc X m with
    | none => rfl
    | some c => simp only; rw [hblk c (hnr m c hc)]
  have hF := rootEnts_delRoot X l B r bnd n hok hB hr hleaf hbk hkin
  apply GMap.ext; intro m
  show (wtxData (X.withWs X.rl l (wsDel r.ws n))) !! m = (GMap.delete n (wtxData X)) !! m
  rw [GMap.lookup_delete_iff, wtxData_lookup (X.withWs X.rl l (wsDel r.ws n)) m]
  unfold bktData
  rw [hF]
  by_cases hm : n = m
  · subst hm
    rw [if_pos rfl]
    have : ((rootEnts X).filter fun x => decide (x.1 ≠ n)).find? (fun x => decide (x.1 = n)) =
        none := by
      apply List.find?_eq_none.2
      intro x hx
      have := (List.mem_filter.1 hx).2
      simpa using this
    rw [this]; rfl
  · rw [if_neg hm, wtxData_lookup X m]
    unfold bktData
    have himp : ∀ x : GoString × List w8, decide (x.1 = m) = true → decide (x.1 ≠ n) = true := by
      intro x hx; simp only [decide_eq_true_eq] at hx ⊢; rw [hx]; exact Ne.symm hm
    rw [← find?_filter_of_imp _ _ himp]
    cases (rootEnts X).find? (fun x => decide (x.1 = m)) with
    | none => rfl
    | some x => simp only [Option.map_some]; rw [hdo]

/-- **Two well-formed records with one logical tree of a bucket have its leaves.** -/
theorem leaves_congr (X Y : WX) (bl : Loc) (hokX : wOK X) (hokY : wOK Y)
    (hbX : (X.t.bs !! bl).isSome) (hbY : (Y.t.bs !! bl).isSome)
    (hL : ltree Y bl = ltree X bl) (hrp : Y.rootPid bl = X.rootPid bl) :
    Y.leaves bl = X.leaves bl := by
  obtain ⟨tX, htX, hpX, hhX, -⟩ := rtOK_init X bl hokX hokX.2.2.2.2.2.2.2 hbX
  obtain ⟨tY, htY, hpY, hhY, -⟩ := rtOK_init Y bl hokY hokY.2.2.2.2.2.2.2 hbY
  have hc : ∀ q, ltree X bl q = ltree Y bl q := fun q => by rw [hL]
  have e1 := lleaves_ltIs (ltree X) bl tX (X.fuel + Y.fuel) htX (by omega)
  have e2 := lleaves_ltIs (ltree Y) bl tY (X.fuel + Y.fuel) htY (by omega)
  rw [WOpen.lleaves_congr' _ _ bl hc, hpX, ← hrp, ← hpY, e2] at e1
  rw [leaves_rt Y bl tY htY hpY hhY, leaves_rt X bl tX htX hpX hhX, e1]

end delpost

end Write

end bbolt
end EtcdGrove
end Perennial
