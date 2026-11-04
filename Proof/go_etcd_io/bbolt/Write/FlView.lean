/-
U7's (`notes/bbolt-proof-plan.md`) `flView` lemmas: the logical tree's cover (`lCovers`) depends
only on the tree's shape (branch positions and their children), the nodes' page ids, the root
bucket's entries and the opened buckets; a leaf's new entries (`flView_withWs'`) and a
materialization (`flView_nodeAdded'`) keep them.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Mat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section flview
variable [GooseExts]

/-- What a walk of positions reads of a position: a branch's children. -/
def shp (x : Option (Bool × List WEntry)) : Option (List w64) :=
  match x with
  | some (false, ws) => some (ws.map WEntry.pgid)
  | _ => none

theorem shp_of_ldat (x y : Option (Bool × List WEntry)) (h : ldat x = ldat y) : shp x = shp y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some _ => simp [ldat] at h
  | some a => cases y with
    | none => simp [ldat] at h
    | some b =>
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have : a2.map WEntry.pgid = b2.map WEntry.pgid := by
        have := congrArg (List.map fun d => d.2.1) h2
        simpa [List.map_map, Function.comp_def, wDat] using this
      cases a1 <;> simp [shp, this]

theorem flatMap_pgid_congr (f : w64 → List w64) (ws1 ws2 : List WEntry)
    (h : ws1.map WEntry.pgid = ws2.map WEntry.pgid) :
    ws1.flatMap (fun w => f w.pgid) = ws2.flatMap (fun w => f w.pgid) := by
  induction ws1 generalizing ws2 with
  | nil => cases ws2 <;> simp_all
  | cons a xs ih =>
    cases ws2 with
    | nil => simp at h
    | cons b ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.flatMap_cons, h.1, ih ys h.2]

/-- The positions of a walk depend only on the shape. -/
theorem lposF_congr (L L' : LTree) (bl : Loc) (h : ∀ pid, shp (L' bl pid) = shp (L bl pid)) :
    ∀ n pid, lposF L' bl n pid = lposF L bl n pid
  | 0, _ => rfl
  | n + 1, pid => by
    have hp := h pid
    simp only [lposF]
    congr 1
    have ih := lposF_congr L L' bl h n
    cases h1 : L bl pid with
    | none =>
      rw [h1] at hp
      cases h2 : L' bl pid with
      | none => rfl
      | some y =>
        obtain ⟨y1, y2⟩ := y
        rw [h2] at hp
        cases y1 <;> simp_all [shp]
    | some x =>
      obtain ⟨x1, x2⟩ := x
      rw [h1] at hp
      cases h2 : L' bl pid with
      | none => rw [h2] at hp; cases x1 <;> simp_all [shp]
      | some y =>
        obtain ⟨y1, y2⟩ := y
        rw [h2] at hp
        cases x1 <;> cases y1 <;> simp only [shp, Option.some.injEq, reduceCtorEq] at hp ⊢
        · simp only [funext ih]
          exact flatMap_pgid_congr _ _ _ hp

/-- **The cover from its parts.** -/
theorem lCovers_congr (X X' : WX) (hv : X'.v = X.v) (hroot : rootEnts X' = rootEnts X)
    (hbkt : ∀ n, bktLoc X' n = bktLoc X n)
    (hbs : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hext : ∀ c, (X.t.bs !! c).isSome → X'.extents c = X.extents c) :
    ∀ s, lCovers X' s ↔ lCovers X s := by
  intro s
  have hne : ∀ c, (X'.t.bs !! c ≠ none ↔ X.t.bs !! c ≠ none) := by
    intro c; have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> simp_all
  unfold lCovers
  rw [hroot, hv]
  simp only [hbkt]
  constructor
  · rintro (⟨c, e, hc, he, h1⟩ | h)
    · have hc' := (hne c).1 hc
      rw [hext c (by cases h : X.t.bs !! c <;> simp_all)] at he
      exact Or.inl ⟨c, e, hc', he, h1⟩
    · exact Or.inr h
  · rintro (⟨c, e, hc, he, h1⟩ | h)
    · have hc' := (hne c).2 hc
      rw [← hext c (by cases h : X.t.bs !! c <;> simp_all)] at he
      exact Or.inl ⟨c, e, hc', he, h1⟩
    · exact Or.inr h

theorem flView_congr (X X' : WX) (fl : FLPg) (hv : X'.v = X.v)
    (hcov : ∀ s, lCovers X' s ↔ lCovers X s) (h : flView X fl) : flView X' fl := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun s hs => ?_, by rw [hv]; exact h2, h3, h4⟩
  rw [hv] at hs
  rw [hcov]; exact h1 s hs

/-- A bucket with node `l`'s entries `ws'` (`WX.withWs`'s bucket record). -/
def brecWithWs (B : BRec) (l : Loc) (ws' : List WEntry) : BRec :=
  { B with ns := match B.ns !! l with
    | none => B.ns
    | some r => B.ns.insert l { r with ws := ws' } }

theorem withWs_bs (X : WX) (bl l : Loc) (ws' : List WEntry) (c : Loc) :
    (X.withWs bl l ws').t.bs !! c =
      (X.t.bs !! c).map fun B => if c = bl then brecWithWs B l ws' else B := by
  unfold WX.withWs brecWithWs
  simp only
  cases hB : X.t.bs !! bl with
  | none =>
    by_cases hc : c = bl
    · subst hc; simp [hB]
    · simp [hc]
  | some B =>
    by_cases hc : c = bl
    · subst hc; simp only [hB, GMap.lookup_insert, Option.map_some, ↓reduceIte]
      congr 2
    · simp [Ne.symm hc, hc]

theorem brecWithWs_ns (B : BRec) (l : Loc) (ws' : List WEntry) (l0 : Loc) :
    (brecWithWs B l ws').ns !! l0 = (B.ns !! l0).map fun r => if l0 = l then { r with ws := ws' } else r := by
  unfold brecWithWs
  simp only
  cases hl : B.ns !! l with
  | none =>
    by_cases h : l0 = l
    · subst h; simp [hl]
    · cases B.ns !! l0 <;> simp [h]
  | some r =>
    by_cases h : l0 = l
    · subst h; simp [hl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; cases B.ns !! l0 <;> simp [h]

/-- `flView_withWs` (`Model/WOps`). -/
theorem flView_withWs' (X : WX) (fl : FLPg) (bl l : Loc) (ws' : List WEntry) (hv : flView X fl)
    (hleaf : ∀ B r, X.t.bs !! bl = some B → B.ns !! l = some r → r.nv.isLeaf' = true)
    (hroot : bl ≠ X.rl) : flView (X.withWs bl l ws') fl := by
  refine flView_congr X (X.withWs bl l ws') fl rfl ?_ hv
  have hvv : (X.withWs bl l ws').v = X.v := rfl
  have hbsc : ∀ c, c ≠ bl → (X.withWs bl l ws').t.bs !! c = X.t.bs !! c := by
    intro c hc; rw [withWs_bs]; cases X.t.bs !! c <;> simp [hc]
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
  refine lCovers_congr X (X.withWs bl l ws') rfl hroots hbkt ?_ ?_
  · intro c; rw [withWs_bs]; cases X.t.bs !! c <;> simp
  · intro c _
    have hshape : ∀ pid, shp (ltree (X.withWs bl l ws') c pid) = shp (ltree X c pid) := by
      intro pid
      by_cases hc : c = bl
      · subst hc
        unfold ltree
        rw [withWs_bs, hvv]
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
    have hpos : (X.withWs bl l ws').positions c = X.positions c := by
      unfold WX.positions
      have hrp : (X.withWs bl l ws').rootPid c = X.rootPid c := by
        unfold WX.rootPid; rw [withWs_bs]
        cases X.t.bs !! c <;> simp only [Option.map_none, Option.map_some]
        split <;> rfl
      rw [hfuel, hrp]
      exact lposF_congr _ _ c hshape _ _
    unfold WX.extents
    rw [hpos]
    congr 1
    funext pid
    unfold WX.posExtent
    rw [withWs_bs, hvv]
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

end flview

end Write

end bbolt
end EtcdGrove
end Perennial
