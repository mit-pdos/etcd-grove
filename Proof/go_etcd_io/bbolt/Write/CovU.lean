/-
`covU` (every covered base slot covered once, `flViewU`'s second part) under the writer's leaf
updates (U7h, the review's U1: `Put`/`Delete` keep the exclusive part's `flViewU`): it depends only
on each bucket's positions and their extents, the root bucket's entries and the opened buckets
(`covU_congr`); a leaf's new entries keep them (`covU_withWs`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.FlView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section covu
variable [GooseExts]

/-- **`covU` from its parts.** -/
theorem covU_congr (X X' : WX) (hv : X'.v = X.v) (hroot : rootEnts X' = rootEnts X)
    (hbkt : ∀ n, bktLoc X' n = bktLoc X n)
    (hbs : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hpos : ∀ c, (X.t.bs !! c).isSome → X'.positions c = X.positions c)
    (hpe : ∀ c pid, (X.t.bs !! c).isSome → X'.posExtent c pid = X.posExtent c pid)
    (h : covU X) : covU X' := by
  have hne : ∀ c, (X'.t.bs !! c ≠ none ↔ X.t.bs !! c ≠ none) := by
    intro c; have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> simp_all
  have hsome : ∀ c, X.t.bs !! c ≠ none → (X.t.bs !! c).isSome := by
    intro c hc; cases e : X.t.bs !! c <;> simp_all
  have hcw : ∀ s c, coverW X' s c → coverW X s c := by
    intro s c hc
    cases c with
    | pos bl pid =>
      obtain ⟨h1, h2, e, h3, h4⟩ := hc
      have h1' := (hne bl).1 h1
      refine ⟨h1', ?_, e, ?_, h4⟩
      · rw [← hpos bl (hsome bl h1')]; exact h2
      · rw [← hpe bl pid (hsome bl h1')]; exact h3
    | bkt n =>
      obtain ⟨v, h1, h2, h3⟩ := hc
      refine ⟨v, ?_, ?_, ?_⟩
      · rw [← hroot]; exact h1
      · rw [← hbkt]; exact h2
      · rw [← hv]; exact h3
  intro s c1 c2 h1 h2
  exact h s c1 c2 (hcw s c1 h1) (hcw s c2 h2)

/-- **A leaf's new entries keep `covU`** (a non-root bucket's leaf; as `flView_withWs'`). -/
theorem covU_withWs (X : WX) (bl l : Loc) (ws' : List WEntry) (hv : covU X)
    (hleaf : ∀ B r, X.t.bs !! bl = some B → B.ns !! l = some r → r.nv.isLeaf' = true)
    (hroot : bl ≠ X.rl) : covU (X.withWs bl l ws') := by
  have hvv : (X.withWs bl l ws').v = X.v := rfl
  have hbsc : ∀ c, c ≠ bl → (X.withWs bl l ws').t.bs !! c = X.t.bs !! c := by
    intro c hc; rw [withWs_bs_at]; cases X.t.bs !! c <;> simp [hc]
  have hrl : (X.withWs bl l ws').t.bs !! X.rl = X.t.bs !! X.rl := hbsc _ (Ne.symm hroot)
  have hfuel : (X.withWs bl l ws').fuel = X.fuel := by
    unfold WX.fuel WX.withWs; simp only
    cases h : X.t.bs !! bl with
    | none => rfl
    | some B => rw [GMap.map_size_insert_Some _ _ _ _ h]
  have hlt_rl : ∀ pid, ltree (X.withWs bl l ws') X.rl pid = ltree X X.rl pid := by
    intro pid; simp only [ltree, hrl]; rfl
  have hroots : rootEnts (X.withWs bl l ws') = rootEnts X := by
    unfold rootEnts WX.leaves WX.rootPid
    simp only [show (X.withWs bl l ws').rl = X.rl from rfl]
    rw [hfuel, hrl]
    have e : ∀ n pid, lleaves (ltree (X.withWs bl l ws')) X.rl n pid = lleaves (ltree X) X.rl n pid := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih => intro pid; simp only [lleaves, hlt_rl, ih]
    rw [e]
  have hbkt : ∀ n, bktLoc (X.withWs bl l ws') n = bktLoc X n := by
    intro n; unfold bktLoc; rw [show (X.withWs bl l ws').rl = X.rl from rfl, hrl]
  refine covU_congr X (X.withWs bl l ws') rfl hroots hbkt ?_ ?_ ?_ hv
  · intro c; rw [withWs_bs_at]; cases X.t.bs !! c <;> simp
  · intro c _
    have hshape : ∀ pid, shp (ltree (X.withWs bl l ws') c pid) = shp (ltree X c pid) := by
      intro pid
      by_cases hc : c = bl
      · subst hc
        unfold ltree
        rw [withWs_bs_at, hvv]
        cases hB : X.t.bs !! c with
        | none => rfl
        | some B =>
          simp only [Option.map_some, ↓reduceIte]
          rw [show resolve (brecWithWs B l ws') pid = resolve B pid from rfl,
            show wpageAt X.v (brecWithWs B l ws') pid = wpageAt X.v B pid from rfl]
          cases hr : resolve B pid with
          | none => rfl
          | some l0 =>
            simp only
            rw [brecWithWs_ns]
            cases hrl0 : B.ns !! l0 with
            | none => rfl
            | some r0 =>
              by_cases hl0 : l0 = l
              · subst hl0
                have := hleaf B r0 hB hrl0
                simp [shp, this]
              · simp [hl0]
      · unfold ltree; rw [hbsc c hc, hvv]
    unfold WX.positions
    have hrp : (X.withWs bl l ws').rootPid c = X.rootPid c := by
      unfold WX.rootPid; rw [withWs_bs_at]
      cases X.t.bs !! c <;> simp only [Option.map_none, Option.map_some]
      split <;> rfl
    rw [hfuel, hrp]
    exact lposF_congr _ _ c hshape _ _
  · intro c pid _
    unfold WX.posExtent
    rw [withWs_bs_at, hvv]
    cases hB : X.t.bs !! c with
    | none => rfl
    | some B =>
      simp only [Option.map_some]
      by_cases hc : c = bl
      · simp only [hc, ↓reduceIte]
        rw [show resolve (brecWithWs B l ws') pid = resolve B pid from rfl]
        cases hr : resolve B pid with
        | none => rfl
        | some l0 =>
          simp only
          rw [brecWithWs_ns]
          cases B.ns !! l0 with
          | none => rfl
          | some r0 => by_cases hl0 : l0 = l <;> simp [hl0]
      · simp only [hc, ↓reduceIte]

end covu

end Write

end bbolt
end EtcdGrove
end Perennial
