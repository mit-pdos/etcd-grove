/-
U7j (`notes/bbolt-proof-plan.md`): `CreateBucket`'s data. A new bucket entry `e` (key `n`, an
empty bucket's value) put into the root bucket's leaf where `n` lands (`leafFor`), `n` absent from
the data: the writer's data gains the empty bucket `n` (`wtxData_createPut`). The root's bucket
entries other than `n` are kept (`rootEnts_filter_ne`: a leaf's `wsPut` changes only the entries
of key `n`, and no other block holds `n`), and `n`'s only bucket entry is `e`
(`rootEnts_key_eq`); no opened bucket's entries change (the root is not an opened bucket).
-/
module

public import Proof.go_etcd_io.bbolt.Write.Data

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section createbktdata
variable [GooseExts]

/-- Filtering keys before or after taking the bucket entries is the same. -/
theorem filterMap_bktOf_filter (ws : List WEntry) (n : List w8) :
    (ws.filter fun w => decide (w.key ≠ n)).filterMap bktOf =
      (ws.filterMap bktOf).filter fun x => decide (x.1 ≠ n) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    by_cases ha : a.key = n
    · rw [List.filter_cons_of_neg (by simp [ha])]
      cases hb : bktOf a with
      | none => rw [List.filterMap_cons_none hb, ih]
      | some x =>
        rw [List.filterMap_cons_some hb, List.filter_cons_of_neg, ih]
        have := bktOf_key a x hb; simp [this, ha]
    · rw [List.filter_cons_of_pos (by simp [ha])]
      cases hb : bktOf a with
      | none => rw [List.filterMap_cons_none hb, List.filterMap_cons_none hb, ih]
      | some x =>
        rw [List.filterMap_cons_some hb, List.filterMap_cons_some hb, List.filter_cons_of_pos, ih]
        have := bktOf_key a x hb; simp [this, ha]

/-- `find?` of a predicate that implies `q` sees only the elements `q` keeps. -/
theorem find?_filter_of_imp {α : Type} (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, l.find? p = (l.filter q).find? p
  | [] => rfl
  | a :: l => by
    by_cases hp : p a = true
    · rw [List.find?_cons_of_pos hp, List.filter_cons_of_pos (h a hp), List.find?_cons_of_pos hp]
    · rw [List.find?_cons_of_neg hp]
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq, List.find?_cons_of_neg hp]
        exact find?_filter_of_imp p q h l
      · rw [List.filter_cons_of_neg hq]
        exact find?_filter_of_imp p q h l

section put
variable (X : WX) (l : Loc) (B : BRec) (r : NRec) (bnd : Loc → Bnd) (e : WEntry)
  (hok : wOK X) (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r)
  (hleaf : r.nv.isLeaf' = true) (hbk : bktKeysB X.v B bnd)
  (hkin : keyIn (bnd l).1 (bnd l).2 e.key)

include hB hr hleaf in
/-- The root's bucket entries after the put, by blocks. -/
theorem rootEnts_createPut :
    rootEnts (X.withWs X.rl l (wsPut r.ws e)) =
      (lleavesB (ltree X) X.rl X.fuel (X.rootPid X.rl) (none, none)).flatMap fun x =>
        (if decide (resolve B x.1 = some l) then wsPut r.ws e else x.2.2).filterMap bktOf := by
  rw [rootEnts_blocks]
  have hrl : (X.withWs X.rl l (wsPut r.ws e)).rl = X.rl := rfl
  rw [hrl, withWs_blocks X X.rl l (wsPut r.ws e) B r hB hr hleaf X.rl, List.flatMap_map]
  apply fm_congr; intro x _
  by_cases h : resolve B x.1 = some l <;> simp [h]

include hok hB hr hleaf hbk hkin in
/-- **The root's bucket entries of keys other than `e.key` are kept** by the put. -/
theorem rootEnts_filter_ne :
    (rootEnts (X.withWs X.rl l (wsPut r.ws e))).filter (fun x => decide (x.1 ≠ e.key)) =
      (rootEnts X).filter (fun x => decide (x.1 ≠ e.key)) := by
  have hs : wsPw r.ws :=
    wsSorted_pw _ ((wOK_bktClean X hok X.rl B hB).2.2.2.2.2.2.2.1 l r hr).2.2.2.1
  rw [rootEnts_createPut X l B r e hB hr hleaf, rootEnts_blocks, List.filter_flatMap,
    List.filter_flatMap]
  apply fm_congr; intro x hx
  split
  · rename_i h
    rw [block_ws X X.rl l B r hB hr _ _ _ x hx (of_decide_eq_true h)]
    rw [wsPut_split, List.filterMap_append, List.filterMap_cons]
    cases hbe : bktOf e with
    | none =>
      rw [← List.filterMap_append, filter_lt_gt r.ws e.key hs, filterMap_bktOf_filter,
        List.filter_filter]
      congr 1; funext x; simp
    | some y =>
      have hk : y.1 = e.key := bktOf_key e y hbe
      simp only [List.filter_append, List.filter_cons, hk, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [← List.filter_append, ← List.filterMap_append, filter_lt_gt r.ws e.key hs,
        filterMap_bktOf_filter, List.filter_filter]
      congr 1; funext x; simp
  · rfl

include hok hB hr hleaf hbk hkin in
/-- **The put's root bucket entries of key `e.key`** are `e`'s (given that it is a bucket
entry). -/
theorem rootEnts_key_eq (hflag : isBktFlag e.flags) :
    (∀ x ∈ rootEnts (X.withWs X.rl l (wsPut r.ws e)), x.1 = e.key → x = (e.key, e.value)) ∧
      (e.key, e.value) ∈ rootEnts (X.withWs X.rl l (wsPut r.ws e)) := by
  obtain ⟨h3, h2⟩ := leafFor_blocks X X.rl l e.key B r bnd hok hB hr hleaf hbk hkin
  have hbe : bktOf e = some (e.key, e.value) := by unfold bktOf; simp [hflag]
  rw [rootEnts_createPut X l B r e hB hr hleaf]
  constructor
  · intro x hx hk
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.1 hx
    obtain ⟨w, hw, hwx⟩ := List.mem_filterMap.1 hxb
    have hwk : w.key = e.key := by rw [← bktOf_key w x hwx, hk]
    split at hw
    · rw [wsPut_split] at hw
      simp only [List.mem_append, List.mem_cons, List.mem_filter] at hw
      rcases hw with ⟨-, hlt⟩ | he | ⟨-, hlt⟩
      · simp only [decide_eq_true_eq, hwk] at hlt; exact absurd hlt (go.goStringLt_irrefl _)
      · rw [he, hbe] at hwx; cases hwx; rfl
      · simp only [decide_eq_true_eq, hwk] at hlt; exact absurd hlt (go.goStringLt_irrefl _)
    · rename_i hs
      exact absurd hwk (h2 b hb (by simpa using hs) w hw)
  · obtain ⟨b, hb, hsel⟩ := h3
    refine List.mem_flatMap.2 ⟨b, hb, ?_⟩
    rw [if_pos hsel]
    refine List.mem_filterMap.2 ⟨e, ?_, hbe⟩
    rw [wsPut_split]; simp

include hok hB hr hleaf hbk hkin in
/-- **`CreateBucket`'s put**: the data gains the empty bucket `e.key`. -/
theorem wtxData_createPut (hflag : isBktFlag e.flags) (hloc : bktLoc X e.key = none)
    (hempty : bktOfPage X.v.pages e.value = ∅)
    (hnr : ∀ m c, bktLoc X m = some c → c ≠ X.rl) :
    wtxData (X.withWs X.rl l (wsPut r.ws e)) = (wtxData X).insert e.key ∅ := by
  have hblk : ∀ c, c ≠ X.rl → lbktEnts (X.withWs X.rl l (wsPut r.ws e)) c = lbktEnts X c := by
    intro c hc
    rw [lbktEnts_blocks, lbktEnts_blocks, withWs_blocks X X.rl l (wsPut r.ws e) B r hB hr hleaf c,
      List.flatMap_map]
    apply fm_congr; intro x _; simp [hc]
  have hloc' : ∀ m, bktLoc (X.withWs X.rl l (wsPut r.ws e)) m = bktLoc X m := withWs_bktLoc X X.rl l _ B r hB hr
  have hdo : ∀ m v, bktDataOf (X.withWs X.rl l (wsPut r.ws e)) m v = bktDataOf X m v := by
    intro m v
    rw [bktDataOf_eq, bktDataOf_eq, hloc']
    cases hc : bktLoc X m with
    | none => rfl
    | some c => simp only; rw [hblk c (hnr m c hc)]
  have hF := rootEnts_filter_ne X l B r bnd e hok hB hr hleaf hbk hkin
  obtain ⟨hA, hBm⟩ := rootEnts_key_eq X l B r bnd e hok hB hr hleaf hbk hkin hflag
  apply GMap.ext; intro m
  show (wtxData (X.withWs X.rl l (wsPut r.ws e))) !! m = (GMap.insert e.key ∅ (wtxData X)) !! m
  rw [GMap.lookup_insert_eq_iff, wtxData_lookup (X.withWs X.rl l (wsPut r.ws e)) m]
  by_cases hm : e.key = m
  · subst hm
    rw [if_pos rfl]
    unfold bktData
    have hfind : (rootEnts (X.withWs X.rl l (wsPut r.ws e))).find? (fun x => decide (x.1 = e.key)) = some (e.key, e.value) := by
      cases hf : (rootEnts (X.withWs X.rl l (wsPut r.ws e))).find? (fun x => decide (x.1 = e.key)) with
      | none =>
        exfalso
        have := List.find?_eq_none.1 hf _ hBm
        simp at this
      | some x =>
        have hx := List.mem_of_find?_eq_some hf
        have hk := List.find?_some hf
        simp only [decide_eq_true_eq] at hk
        rw [hA x hx hk]
    rw [hfind]
    simp only [Option.map_some]
    rw [bktDataOf_eq, hloc', hloc]
    exact congrArg some hempty
  · rw [if_neg hm, wtxData_lookup X m]
    unfold bktData
    have himp : ∀ x : GoString × List w8, decide (x.1 = m) = true → decide (x.1 ≠ e.key) = true := by
      intro x hx; simp only [decide_eq_true_eq] at hx ⊢; rw [hx]; exact Ne.symm hm
    rw [find?_filter_of_imp _ _ himp (rootEnts (X.withWs X.rl l (wsPut r.ws e))), hF, ← find?_filter_of_imp _ _ himp]
    cases (rootEnts X).find? (fun x => decide (x.1 = m)) with
    | none => rfl
    | some x => simp only [Option.map_some]; rw [hdo]

end put

end createbktdata

end Write

end bbolt
end EtcdGrove
end Perennial
