/-
U7's (`notes/bbolt-proof-plan.md`) materialization lemmas: a `nodeAdded` step keeps the logical
tree by data and the writer's data.

The shared `ltree_nodeAdded`/`wtxData_matGrow` (false as first stated: `nodeAdded` does not say
that the new node is no cached node of its bucket, nor, for an inline bucket, that it had no root
node, and an inline bucket's `resolve` ignores the position) are these: `ltree_nodeAdded'` over
`matFresh` (`Model/WOps`), `wtxData_matGrow` over `wOK` (2026-11-04).
-/
module

public import Proof.go_etcd_io.bbolt.Write.WOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section mat
variable [GooseExts]

/-- A logical tree's position by data. -/
def ldat (x : Option (Bool × List WEntry)) : Option (Bool × List (w32 × w64 × List w8 × List w8)) :=
  x.map fun y => (y.1, y.2.map wDat)

theorem pageWsAs_wDat (pg : List w8) (src : Src) :
    (pageWsAs pg src).map wDat = (pageWs pg).map wDat := by
  unfold pageWsAs; simp only [List.map_map]; rfl

-- `matFresh` is in `Model/WOps.lean` (shared, 2026-11-04).

/-- **Materialization keeps the logical tree by data** (`ltree_nodeAdded`, at every position of a
file bucket, at position `0` of an inline one). -/
theorem ltree_nodeAdded' (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (h : nodeAdded X X' bl l pgid parent) (hf : matFresh X bl l) (bl' : Loc) (pid : w64)
    (hpid : bl' = bl → ∀ B, X.t.bs !! bl = some B → B.ib.root' = W64 0 → pid = W64 0) :
    ldat (ltree X' bl' pid) = ldat (ltree X bl' pid) := by
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp, hrid, hrleaf, hru, hrs, hrcs, hrco,
    hrws, hrlive, hrkey, hrks, hcase, rfl⟩ := h
  obtain ⟨hfnm, hfroot⟩ := hf B hB
  by_cases hbl : bl' = bl
  · subst hbl
    have hpid := hpid rfl B hB
    simp only [ltree, GMap.lookup_insert]
    simp only [hB]
    have hns_l : ns' !! l = some r := by
      rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, rfl⟩ <;>
        simp
    have hns_o : ∀ l0, l0 ≠ l → ldat ((ns' !! l0).map fun r => (r.nv.isLeaf', r.ws)) =
        ldat ((B.ns !! l0).map fun r => (r.nv.isLeaf', r.ws)) := by
      intro l0 hl0'
      rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, hws, -, -, -, hnv, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0')]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0')]
        by_cases hp : parent = l0
        · subst hp
          rw [GMap.lookup_insert, hrp]
          simp only [ldat, Option.map_some, hws]
          rw [hnv]
        · rw [GMap.lookup_insert_ne _ _ hp]
    by_cases hin : B.ib.root' = W64 0
    · have hrn := hfroot hin
      have hpid0 := hpid hin
      subst hpid0
      have hpg0 : pgid = W64 0 := by
        unfold wpageAt at hpg; rw [if_pos hin] at hpg; split at hpg
        · assumption
        · simp at hpg
      subst hpg0
      unfold resolve
      simp only [hin, ↓reduceIte, hrn]
      rcases hcase with ⟨hpn, hbv, hns⟩ | ⟨hpn, hbv, -⟩
      · rw [hbv]
        simp only [hl0, ↓reduceIte, hns_l]
        rw [hpg]
        simp only [ldat, Option.map_some, hrleaf, hrws, pageWsAs_wDat]
      · rw [hbv]
        simp only [hrn, ↓reduceIte]
        unfold wpageAt
        simp only [hin, ↓reduceIte]
    · unfold resolve
      simp only [hin, ↓reduceIte]
      by_cases hp : pid = pgid
      · subst hp
        rw [GMap.lookup_insert, hnm]
        simp only [hns_l]
        unfold wpageAt at hpg ⊢
        simp only [hin, ↓reduceIte] at hpg ⊢
        rw [hpg]
        simp only [ldat, Option.map_some, Option.map_map, Function.comp_def, hrleaf, hrws,
          pageWsAs_wDat]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hp)]
        cases hc : B.nm !! pid with
        | none =>
          simp only
          unfold wpageAt
          simp only [hin, ↓reduceIte]
        | some l0 =>
          simp only
          have : l0 ≠ l := by intro e; subst e; exact hfnm pid hc
          exact hns_o l0 this
  · simp only [ltree, GMap.lookup_insert_ne _ _ (Ne.symm hbl)]

theorem flatMap_dat (f g : w64 → List (List WEntry))
    (hfg : ∀ p, (f p).map (List.map wDat) = (g p).map (List.map wDat)) :
    ∀ ws1 ws2 : List WEntry, ws1.map wDat = ws2.map wDat →
      ((ws1.flatMap fun w => f w.pgid)).map (List.map wDat) =
        (ws2.flatMap fun w => g w.pgid).map (List.map wDat)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hab, hs⟩ := h
    have hp : a.pgid = b.pgid := by
      have := congrArg (fun x => x.2.1) hab; simpa [wDat] using this
    simp only [List.flatMap_cons, List.map_append, hp, hfg b.pgid, flatMap_dat f g hfg xs ys hs]

/-- Two logical trees of bucket `bl` agreeing by data everywhere have the same leaves by data. -/
theorem lleaves_dat (L L' : LTree) (bl : Loc) (h : ∀ pid, ldat (L' bl pid) = ldat (L bl pid)) :
    ∀ n pid, (lleaves L' bl n pid).map (List.map wDat) = (lleaves L bl n pid).map (List.map wDat)
  | 0, _ => rfl
  | n + 1, pid => by
    have hp := h pid
    simp only [lleaves]
    cases h1 : L bl pid with
    | none =>
      rw [h1] at hp
      cases h2 : L' bl pid with
      | none => rfl
      | some y => rw [h2] at hp; simp [ldat] at hp
    | some x =>
      rw [h1] at hp
      cases h2 : L' bl pid with
      | none => rw [h2] at hp; simp [ldat] at hp
      | some y =>
        rw [h2] at hp
        simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨x1, x2⟩ := x
        obtain ⟨y1, y2⟩ := y
        obtain ⟨e1, e2⟩ := hp
        simp only at e1 e2 ⊢
        subst e1
        cases y1 with
        | true => simp [e2]
        | false =>
          exact flatMap_dat _ _ (lleaves_dat L L' bl h n) y2 x2 e2

/-- Leaves' plain entries and bucket entries by data. -/
theorem flatMap_filterMap_dat {β : Type} (G : w32 × w64 × List w8 × List w8 → Option β)
    (L1 L2 : List (List WEntry)) (h : L1.map (List.map wDat) = L2.map (List.map wDat)) :
    (L1.flatMap fun ws => ws.filterMap fun w => G (wDat w)) =
      (L2.flatMap fun ws => ws.filterMap fun w => G (wDat w)) := by
  have e : ∀ L : List (List WEntry), (L.flatMap fun ws => ws.filterMap fun w => G (wDat w)) =
      (L.map (List.map wDat)).flatMap (List.filterMap G) := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih => simp [List.flatMap_cons, ih, List.filterMap_map, Function.comp_def]
  rw [e, e, h]

theorem rootEnts_eq_of_dat (X X' : WX) (h : (X'.leaves X'.rl).map (List.map wDat) =
    (X.leaves X.rl).map (List.map wDat)) : rootEnts X' = rootEnts X :=
  flatMap_filterMap_dat (fun d => if decide (isBktFlag d.1) then some (d.2.2.1, d.2.2.2) else none)
    _ _ h

theorem lbktEnts_eq_of_dat (X X' : WX) (c : Loc) (h : (X'.leaves c).map (List.map wDat) =
    (X.leaves c).map (List.map wDat)) : lbktEnts X' c = lbktEnts X c :=
  flatMap_filterMap_dat (fun d => if decide (isBktFlag d.1) then none else some (d.2.2.1, d.2.2.2))
    _ _ h

/-- **A materialization keeps the writer's data** (one `nodeAdded` step; `wtxData_matGrow` by
induction, with `matFresh` and an inline page a leaf at each step: `wOK` gives both). -/
theorem wtxData_nodeAdded' (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (h : nodeAdded X X' bl l pgid parent) (hf : matFresh X bl l)
    (hleaf : ∀ B pa pg, X.t.bs !! bl = some B → B.ib.root' = W64 0 → B.bv.rootNode' = null →
      wpageAt X.v B pgid = some (pa, pg) → pageFlags pg = leafPageFlag) :
    wtxData X' = wtxData X := by
  have hlt := ltree_nodeAdded' X X' bl l pgid parent h hf
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp, hrid, hrleaf, hru, hrs, hrcs, hrco,
    hrws, hrlive, hrkey, hrks, hcase, hX'⟩ := h
  have hv : X'.v = X.v := by rw [hX']
  have hrl : X'.rl = X.rl := by rw [hX']
  have hfuel : X'.fuel = X.fuel := by
    rw [hX']; unfold WX.fuel; simp only
    rw [GMap.map_size_insert_Some _ _ _ _ hB]
  have hbs : ∀ c, (X'.t.bs !! c).map (fun B => (B.ib, B.bm)) = (X.t.bs !! c).map
      (fun B => (B.ib, B.bm)) := by
    intro c; rw [hX']; simp only
    by_cases hc : bl = c
    · subst hc; rw [GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ hc]
  have hrp' : ∀ c, X'.rootPid c = X.rootPid c := by
    intro c; unfold WX.rootPid
    have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> rw [h1, h2] at this <;> simp_all
  have hleaves : ∀ c, (X'.leaves c).map (List.map wDat) = (X.leaves c).map (List.map wDat) := by
    intro c
    unfold WX.leaves
    rw [hfuel, hrp' c]
    by_cases hin : c = bl ∧ B.ib.root' = W64 0
    · obtain ⟨rfl, hin⟩ := hin
      have hrn := (hf B hB).2 hin
      have hpg0 : pgid = W64 0 := by
        unfold wpageAt at hpg; rw [if_pos hin] at hpg; split at hpg
        · assumption
        · simp at hpg
      subst hpg0
      have hroot : X.rootPid c = W64 0 := by simp [WX.rootPid, hB, hin]
      rw [hroot]
      have h0 := hlt c (W64 0) (fun _ _ _ _ => rfl)
      have hX0 : ltree X c (W64 0) = some (true, pageWs pg) := by
        simp only [ltree, hB, resolve, hin, ↓reduceIte, hrn, hpg, Option.map_some]
        rw [hleaf B pa pg hB hin hrn hpg]; rfl
      rw [hX0] at h0
      cases hX'0 : ltree X' c (W64 0) with
      | none => rw [hX'0] at h0; simp [ldat] at h0
      | some y =>
        rw [hX'0] at h0
        obtain ⟨y1, y2⟩ := y
        simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, e2⟩ := h0
        cases hn : X.fuel with
        | zero => rfl
        | succ n => simp only [lleaves]; rw [hX'0, hX0]; simp [e2]
    · apply lleaves_dat
      intro pid
      apply hlt
      intro hc B' hB' hin'
      rw [hB] at hB'; cases hB'
      exact absurd ⟨hc, hin'⟩ hin
  have hroot := rootEnts_eq_of_dat X X' (by rw [hrl]; exact hleaves X.rl)
  unfold wtxData
  rw [hroot]
  congr 1
  apply List.map_congr_left
  intro e _
  congr 1
  unfold bktDataOf
  have hb := hbs X'.rl
  rw [hrl] at hb ⊢
  have hbm : (X'.t.bs !! X.rl).bind (fun B => B.bm !! e.1) =
      (X.t.bs !! X.rl).bind (fun B => B.bm !! e.1) := by
    cases h1 : X'.t.bs !! X.rl <;> cases h2 : X.t.bs !! X.rl <;> rw [h1, h2] at hb <;> simp_all
  rw [hbm, hv]
  cases (X.t.bs !! X.rl).bind (fun B => B.bm !! e.1) with
  | none => rfl
  | some c => simp only; rw [lbktEnts_eq_of_dat X X' c (hleaves c)]

/-- **Materializations keep the writer's data** (`Model/WOps`' former `wtxData_matGrow`, with
`wOK` at the start: each step keeps it, `wOK_nodeAdded`, and gives the step's freshness). -/
theorem wtxData_matGrow (X X' : WX) (bl : Loc) (hok : wOK X) (h : matGrow X X' bl) :
    wtxData X' = wtxData X := by
  revert hok
  induction h with
  | refl => intro _; rfl
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    intro hok
    rw [ih (wOK_nodeAdded X Y bl l pgid parent hok hadd hpos)]
    exact wtxData_nodeAdded' X Y bl l pgid parent hadd
      (wOK_matFresh X Y bl l pgid parent hok hadd hpos) (wOK_inlineLeaf X bl pgid hok)

end mat

end Write

end bbolt
end EtcdGrove
end Perennial
