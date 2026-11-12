/-
U7k (`notes/bbolt-proof-plan.md`): the walk of a bucket's logical tree as blocks (`lleavesB`: each
leaf with its position and the bounds the walk gives it), its leaves `lleaves`; and the writer
`X.withWs bl l ws'` (a leaf's entries replaced), whose walk replaces the blocks at `l`'s
positions.
-/
module

public import Proof.go_etcd_io.bbolt.Write.DataMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section datawalk
variable [GooseExts]

/-- Key bounds. -/
abbrev Bnd := Option (List w8) × Option (List w8)

/-- The leaves of the walk from `pid` with bounds `b`: each with its position and bounds. -/
def lleavesB (L : LTree) (bl : Loc) : Nat → w64 → Bnd → List (w64 × Bnd × List WEntry)
  | 0, _, _ => []
  | n + 1, pid, b =>
    match L bl pid with
    | some (true, ws) => [(pid, b, ws)]
    | some (false, ws) => (List.range ws.length).flatMap fun i =>
        lleavesB L bl n (ws.getD i default).pgid (wEntryBnd b ws i)
    | none => []

theorem range_flatMap_getD {α β : Type} [Inhabited α] (ws : List α) (g : α → List β) :
    ((List.range ws.length).flatMap fun i => g (ws.getD i default)) = ws.flatMap g := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih]

theorem lleavesB_snd (L : LTree) (bl : Loc) :
    ∀ n pid b, (lleavesB L bl n pid b).map (fun x => x.2.2) = lleaves L bl n pid
  | 0, _, _ => rfl
  | n + 1, pid, b => by
    simp only [lleavesB, lleaves]
    cases L bl pid with
    | none => rfl
    | some x =>
      obtain ⟨lf, ws⟩ := x
      cases lf with
      | true => rfl
      | false =>
        simp only
        rw [List.map_flatMap]
        rw [← range_flatMap_getD ws (fun w => lleaves L bl n w.pgid)]
        apply fm_congr; intro i _
        exact lleavesB_snd L bl n _ _

/-- The plain entries of bucket `bl`, from its walk's blocks. -/
theorem lbktEnts_blocks (X : WX) (bl : Loc) :
    lbktEnts X bl = (lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none)).flatMap
      fun x => x.2.2.filterMap plainOf := by
  unfold lbktEnts WX.leaves
  rw [← lleavesB_snd, List.flatMap_map]; rfl

theorem rootEnts_blocks (X : WX) :
    rootEnts X = (lleavesB (ltree X) X.rl X.fuel (X.rootPid X.rl) (none, none)).flatMap
      fun x => x.2.2.filterMap bktOf := by
  unfold rootEnts WX.leaves
  rw [← lleavesB_snd, List.flatMap_map]; rfl

/-- **Replacing a leaf's entries replaces its blocks.** -/
theorem lleavesB_replace (L L' : LTree) (bl : Loc) (sel : w64 → Bool) (ws' : List WEntry)
    (hL : ∀ p, L' bl p = if sel p then some (true, ws') else L bl p)
    (hleaf : ∀ p, sel p = true → ∃ ws, L bl p = some (true, ws)) :
    ∀ n pid b, lleavesB L' bl n pid b = (lleavesB L bl n pid b).map
      fun x => if sel x.1 then (x.1, x.2.1, ws') else x
  | 0, _, _ => rfl
  | n + 1, pid, b => by
    simp only [lleavesB]
    rw [hL pid]
    cases hs : sel pid
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases L bl pid with
      | none => rfl
      | some x =>
        obtain ⟨lf, ws⟩ := x
        cases lf with
        | true => simp [hs]
        | false =>
          simp only
          rw [List.map_flatMap]
          apply fm_congr; intro i _
          exact lleavesB_replace L L' bl sel ws' hL hleaf n _ _
    · obtain ⟨ws, hws⟩ := hleaf pid hs
      simp [hws, hs]

/-! ## The writer with a leaf's entries replaced -/

theorem withWs_bs (X : WX) (bl l : Loc) (ws' : List WEntry) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) :
    (X.withWs bl l ws').t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l { r with ws := ws' } } := by
  unfold WX.withWs; simp only [hB, hr]

theorem withWs_ltree (X : WX) (bl l : Loc) (ws' : List WEntry) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (bl' : Loc) (p : w64) :
    ltree (X.withWs bl l ws') bl' p =
      if bl' = bl ∧ resolve B p = some l then some (true, ws') else ltree X bl' p := by
  unfold ltree
  rw [withWs_bs X bl l ws' B r hB hr]
  have hv : (X.withWs bl l ws').v = X.v := rfl
  rw [hv]
  by_cases hb : bl = bl'
  · subst hb
    rw [GMap.lookup_insert, hB]
    have hres : resolve { B with ns := B.ns.insert l { r with ws := ws' } } p = resolve B p := rfl
    have hwp : wpageAt X.v { B with ns := B.ns.insert l { r with ws := ws' } } p =
      wpageAt X.v B p := rfl
    simp only [hres, hwp]
    cases hp : resolve B p with
    | none => simp
    | some m =>
      by_cases hm : m = l
      · subst hm; simp [hleaf]
      · simp only [Option.some.injEq, hm, and_false, ↓reduceIte]
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hm)]
  · rw [GMap.lookup_insert_ne _ _ hb]
    simp [Ne.symm hb]

theorem withWs_fuel (X : WX) (bl l : Loc) (ws' : List WEntry) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) :
    (X.withWs bl l ws').fuel = X.fuel := by
  unfold WX.fuel
  rw [withWs_bs X bl l ws' B r hB hr, GMap.map_size_insert_Some _ _ _ _ hB]; rfl

theorem withWs_rootPid (X : WX) (bl l : Loc) (ws' : List WEntry) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (c : Loc) :
    (X.withWs bl l ws').rootPid c = X.rootPid c := by
  unfold WX.rootPid
  rw [withWs_bs X bl l ws' B r hB hr]
  by_cases hc : bl = c
  · subst hc; rw [GMap.lookup_insert, hB]; rfl
  · rw [GMap.lookup_insert_ne _ _ hc]

theorem withWs_bktLoc (X : WX) (bl l : Loc) (ws' : List WEntry) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (n : GoString) :
    bktLoc (X.withWs bl l ws') n = bktLoc X n := by
  unfold bktLoc
  rw [withWs_bs X bl l ws' B r hB hr]
  have hrl : (X.withWs bl l ws').rl = X.rl := rfl
  rw [hrl]
  by_cases hc : bl = X.rl
  · rw [← hc, GMap.lookup_insert, hB]; rfl
  · rw [GMap.lookup_insert_ne _ _ hc]

/-- The blocks of `X.withWs bl l ws'`'s walk of any bucket: `X`'s, with `l`'s replaced. -/
theorem withWs_blocks (X : WX) (bl l : Loc) (ws' : List WEntry) (B : BRec) (r : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (c : Loc) :
    lleavesB (ltree (X.withWs bl l ws')) c (X.withWs bl l ws').fuel
        ((X.withWs bl l ws').rootPid c) (none, none) =
      (lleavesB (ltree X) c X.fuel (X.rootPid c) (none, none)).map
        fun x => if decide (c = bl ∧ resolve B x.1 = some l) then (x.1, x.2.1, ws') else x := by
  rw [withWs_fuel X bl l ws' B r hB hr, withWs_rootPid X bl l ws' B r hB hr]
  apply lleavesB_replace (ltree X) _ c (fun p => decide (c = bl ∧ resolve B p = some l)) ws'
  · intro p
    rw [withWs_ltree X bl l ws' B r hB hr hleaf]
    simp
  · intro p hp
    simp only [decide_eq_true_eq] at hp
    obtain ⟨rfl, hp⟩ := hp
    refine ⟨r.ws, ?_⟩
    unfold ltree; simp [hB, hp, hr, hleaf]

end datawalk

end Write

end bbolt
end EtcdGrove
end Perennial
