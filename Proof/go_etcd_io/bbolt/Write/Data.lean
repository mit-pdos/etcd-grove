/-
U7k (`notes/bbolt-proof-plan.md`): `Put`'s and `Delete`'s data, `wtxData_put` and `wtxData_del`
(`Model/LTree`), as primed copies. The leaf `l` where the key lands is a block of its bucket's
walk, with the bounds `bnd l` that hold the key (`leaf_block`); every other block's bounds are
disjoint from them (`bInv_walk`), so no other block holds the key; replacing `l`'s entries then
changes the bucket's plain entries by `insert`/`delete` (`blocks_put`/`blocks_del`), keeps the
root's bucket entries (the key is no bucket's) and no other bucket (`hinj`); and the bucket is a
root entry (`entryIn_block`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DataReach
public import Proof.go_etcd_io.bbolt.Write.DataBkt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section data
variable [GooseExts]

theorem lleavesB_leaf (L : LTree) (bl : Loc) :
    ∀ n p b, ∀ x ∈ lleavesB L bl n p b, L bl x.1 = some (true, x.2.2)
  | 0, _, _, x, hx => by simp [lleavesB] at hx
  | n + 1, p, b, x, hx => by
    simp only [lleavesB] at hx
    cases hL : L bl p with
    | none => rw [hL] at hx; cases hx
    | some y =>
      obtain ⟨lf, ws⟩ := y
      rw [hL] at hx
      cases lf with
      | true =>
        simp only [List.mem_singleton] at hx
        subst hx; exact hL
      | false =>
        simp only at hx
        obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
        exact lleavesB_leaf L bl n _ _ x hx

/-- A block at `l`'s position holds `l`'s entries. -/
theorem block_ws (X : WX) (bl l : Loc) (B : BRec) (r : NRec) (hB : X.t.bs !! bl = some B)
    (hr : B.ns !! l = some r) (n : Nat) (p : w64) (b : Bnd)
    (x : w64 × Bnd × List WEntry) (hx : x ∈ lleavesB (ltree X) bl n p b)
    (hres : resolve B x.1 = some l) : x.2.2 = r.ws := by
  have := lleavesB_leaf _ _ _ _ _ x hx
  unfold ltree at this
  rw [hB] at this
  simp only [hres, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
  exact this.2.symm

theorem bktDataOf_eq (X : WX) (n : GoString) (v : List w8) :
    bktDataOf X n v = match bktLoc X n with
      | some c => GMap.ofList (lbktEnts X c)
      | none => bktOfPage X.v.pages v := rfl

/-- An opened top-level bucket is a root entry. -/
theorem bktLoc_rootEnt (X : WX) (hok : wOK X) (n : GoString) (bl : Loc)
    (hb : bktLoc X n = some bl) : ∃ v, (n, v) ∈ rootEnts X := by
  unfold bktLoc at hb
  cases hR : X.t.bs !! X.rl with
  | none => rw [hR] at hb; cases hb
  | some R =>
    rw [hR] at hb
    simp only [Option.bind_some] at hb
    obtain ⟨⟨bndR, hbkR⟩, hnest⟩ := hok.2.1 X.rl R hR
    obtain ⟨C, v, -, hin, -⟩ := hnest n bl hb
    obtain ⟨x, hx, w, hw, hk, hf, hv⟩ := entryIn_block X X.rl R bndR hok hR hbkR n v hin
    refine ⟨v, ?_⟩
    rw [rootEnts_blocks, List.mem_flatMap]
    refine ⟨x, hx, List.mem_filterMap.2 ⟨w, hw, ?_⟩⟩
    unfold bktOf; simp [hf, hk, hv]

/-- **A leaf's entries changed**: when the bucket `n`'s plain entries change by `g` and the
root's bucket entries are kept, the data changes at `n` by `g`. -/
theorem wtxData_leaf (X : WX) (n : GoString) (bl l : Loc) (ws' : List WEntry)
    (g : BktData → BktData) (hok : wOK X) (hb : bktLoc X n = some bl)
    (hinj : ∀ n', bktLoc X n' = some bl → n' = n) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (hplain : GMap.ofList ((lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none)).flatMap
        fun x => (if decide (resolve B x.1 = some l) then ws' else x.2.2).filterMap plainOf) =
      g (GMap.ofList (lbktEnts X bl)))
    (hbkt : ws'.filterMap bktOf = r.ws.filterMap bktOf) :
    wtxData (X.withWs bl l ws') = (wtxData X).insert n (g (((wtxData X) !! n).getD ∅)) := by
  have hblk : ∀ {α : Type} c (F : List WEntry → List α),
      (lleavesB (ltree (X.withWs bl l ws')) c (X.withWs bl l ws').fuel
          ((X.withWs bl l ws').rootPid c) (none, none)).flatMap (fun x => F x.2.2) =
        (lleavesB (ltree X) c X.fuel (X.rootPid c) (none, none)).flatMap fun x =>
          F (if decide (c = bl ∧ resolve B x.1 = some l) then ws' else x.2.2) := by
    intro α c F
    rw [withWs_blocks X bl l ws' B r hB hr hleaf c, List.flatMap_map]
    apply fm_congr; intro x _
    split <;> rfl
  have hother : ∀ c, c ≠ bl → lbktEnts (X.withWs bl l ws') c = lbktEnts X c := by
    intro c hc
    rw [lbktEnts_blocks, lbktEnts_blocks, hblk c (fun ws => ws.filterMap plainOf)]
    apply fm_congr; intro x _; simp [hc]
  have hthis : GMap.ofList (lbktEnts (X.withWs bl l ws') bl) = g (GMap.ofList (lbktEnts X bl)) := by
    rw [lbktEnts_blocks, hblk bl (fun ws => ws.filterMap plainOf), ← hplain]
    congr 1; apply fm_congr; intro x _; simp
  have hroot : rootEnts (X.withWs bl l ws') = rootEnts X := by
    have hrl : (X.withWs bl l ws').rl = X.rl := rfl
    rw [rootEnts_blocks, rootEnts_blocks, hrl, hblk X.rl (fun ws => ws.filterMap bktOf)]
    apply fm_congr; intro x hx
    split
    · rename_i h
      obtain ⟨hc, hres⟩ := of_decide_eq_true h
      subst hc
      rw [block_ws X _ l B r hB hr _ _ _ x hx hres, hbkt]
    · rfl
  have hloc : ∀ m, bktLoc (X.withWs bl l ws') m = bktLoc X m :=
    withWs_bktLoc X bl l ws' B r hB hr
  have hdo : ∀ m v, m ≠ n → bktDataOf (X.withWs bl l ws') m v = bktDataOf X m v := by
    intro m v hm
    rw [bktDataOf_eq, bktDataOf_eq, hloc]
    cases hc : bktLoc X m with
    | none => rfl
    | some c =>
      have : c ≠ bl := fun h => hm (hinj m (h ▸ hc))
      simp only; rw [hother c this]
  have hdn : ∀ v, bktDataOf (X.withWs bl l ws') n v = g (GMap.ofList (lbktEnts X bl)) := by
    intro v; rw [bktDataOf_eq, hloc, hb]; exact hthis
  obtain ⟨v0, hv0⟩ := bktLoc_rootEnt X hok n bl hb
  apply GMap.ext; intro m
  show (wtxData (X.withWs bl l ws')) !! m = (GMap.insert n _ (wtxData X)) !! m
  rw [GMap.lookup_insert_eq_iff, wtxData_lookup (X.withWs bl l ws') m]
  by_cases hm : n = m
  · subst hm
    rw [if_pos rfl, wtxData_lookup X n]
    unfold bktData
    rw [hroot]
    cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 hf (n, v0) hv0
      simp at this
    | some e =>
      simp only [Option.map_some, Option.getD_some, hdn]
      rw [bktDataOf_eq, hb]
  · rw [if_neg hm, wtxData_lookup X m]
    unfold bktData
    rw [hroot]
    cases (rootEnts X).find? (fun e => decide (e.1 = m)) with
    | none => rfl
    | some e => simp only [Option.map_some]; rw [hdo m e.2 (Ne.symm hm)]

/-- The facts of the leaf where a key lands: its block, every block at its position holds its
entries, and no other block holds the key. -/
theorem leafFor_blocks (X : WX) (bl l : Loc) (k : List w8) (B : BRec) (r : NRec) (bnd : Loc → Bnd)
    (hok : wOK X) (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (hleaf : r.nv.isLeaf' = true) (hbk : bktKeysB X.v B bnd) (hkin : keyIn (bnd l).1 (bnd l).2 k) :
    (∃ x ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none),
        decide (resolve B x.1 = some l) = true) ∧
      ∀ x ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none),
        decide (resolve B x.1 = some l) = false → ∀ w ∈ x.2.2, w.key ≠ k := by
  obtain ⟨-, hres⟩ := node_reach X bl B bnd hok hB hbk l r hr
  have hxl := leaf_block X bl B bnd hok hB hbk l r hr hleaf
  obtain ⟨hP1, -, hP2⟩ := bInv_walk X bl B bnd hok hB hbk X.fuel _ _
    (bInv_root X bl B bnd hok hB hbk)
  refine ⟨⟨_, hxl, by simp [hres]⟩, ?_⟩
  intro x hx hs w hw hk
  have hne : x ≠ (r.nv.pgid', bnd l, r.ws) := by
    intro h; subst h; simp [hres] at hs
  have := pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hP2 x hx _ hxl hne
  exact this k (hk ▸ hP1 x hx w hw) hkin

theorem wtxData_put' (X : WX) (n : GoString) (bl l : Loc) (ws : List WEntry) (e : WEntry)
    (hok : wOK X) (hb : bktLoc X n = some bl) (hinj : ∀ n', bktLoc X n' = some bl → n' = n)
    (hl : leafFor X bl e.key l)
    (hws : nodeWs X bl l = some ws) (hflag : ¬ isBktFlag e.flags) (hk : e.key ≠ [])
    (hnb : ∀ w ∈ ws, w.key = e.key → ¬ isBktFlag w.flags) :
    wtxData (X.withWs bl l (wsPut ws e)) =
      (wtxData X).insert n (((wtxData X) !! n).getD ∅ |>.insert e.key e.value) := by
  obtain ⟨B, r, bnd, hB, hr, hleaf, hbk, hkin⟩ := hl
  have hws' : r.ws = ws := by
    unfold nodeWs at hws; rw [hB] at hws; simp [hr] at hws; exact hws
  subst hws'
  have hs : wsPw r.ws :=
    wsSorted_pw _ ((wOK_bktClean X hok bl B hB).2.2.2.2.2.2.2.1 l r hr).2.2.2.1
  obtain ⟨h3, h2⟩ := leafFor_blocks X bl l e.key B r bnd hok hB hr hleaf hbk hkin
  apply wtxData_leaf X n bl l (wsPut r.ws e) (fun d => d.insert e.key e.value) hok hb hinj B r
    hB hr hleaf
  · rw [lbktEnts_blocks]
    have := blocks_put _ (fun x : w64 × Bnd × List WEntry => decide (resolve B x.1 = some l))
      (fun x : w64 × Bnd × List WEntry => x.2.2) e hflag
      (fun x hx h => by rw [block_ws X bl l B r hB hr _ _ _ x hx (of_decide_eq_true h)]; exact hs)
      h2 h3
    rw [← this]
    congr 1; apply fm_congr; intro x hx
    split
    · rename_i h; rw [block_ws X bl l B r hB hr _ _ _ x hx (of_decide_eq_true h)]
    · rfl
  · exact bkt_wsPut r.ws e hs hflag hnb

theorem wtxData_del' (X : WX) (n : GoString) (bl l : Loc) (ws : List WEntry) (k : List w8)
    (hok : wOK X) (hb : bktLoc X n = some bl) (hinj : ∀ n', bktLoc X n' = some bl → n' = n)
    (hl : leafFor X bl k l)
    (hws : nodeWs X bl l = some ws) (hnb : ∀ w ∈ ws, w.key = k → ¬ isBktFlag w.flags) :
    wtxData (X.withWs bl l (wsDel ws k)) =
      (wtxData X).insert n (((wtxData X) !! n).getD ∅ |>.delete k) := by
  obtain ⟨B, r, bnd, hB, hr, hleaf, hbk, hkin⟩ := hl
  have hws' : r.ws = ws := by
    unfold nodeWs at hws; rw [hB] at hws; simp [hr] at hws; exact hws
  subst hws'
  obtain ⟨-, h2⟩ := leafFor_blocks X bl l k B r bnd hok hB hr hleaf hbk hkin
  apply wtxData_leaf X n bl l (wsDel r.ws k) (fun d => d.delete k) hok hb hinj B r hB hr hleaf
  · rw [lbktEnts_blocks]
    have := blocks_del _ (fun x : w64 × Bnd × List WEntry => decide (resolve B x.1 = some l))
      (fun x : w64 × Bnd × List WEntry => x.2.2) k h2
    rw [← this]
    congr 1; apply fm_congr; intro x hx
    split
    · rename_i h; rw [block_ws X bl l B r hB hr _ _ _ x hx (of_decide_eq_true h)]
    · rfl
  · exact bkt_wsDel r.ws k hnb

end data

end Write

end bbolt
end EtcdGrove
end Perennial
