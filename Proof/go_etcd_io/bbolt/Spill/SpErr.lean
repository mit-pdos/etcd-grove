/-
`node.spill` (U9w3, `notes/bbolt-proof-plan.md`; pure): **a spill's error facts** (`spErr`,
`Spill/NodeSpec`) compose (`spErr_trans`), follow from a frame and the database facts
(`spErr_of_frame`), and hold of `allocate`'s error after a remap (`spErr_rebase`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Spill.AllocDeref

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section err
variable [GooseExts]

theorem spErr_refl (X : WX) (w : WDb) : spErr X X w w [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, meta_with_pgid_self _⟩

/-- **Error facts compose** (a step's facts, then an error's). -/
theorem spErr_trans {X1 X2 X3 : WX} {w1 w2 w3 : WDb} {s1 s2 : List FLStep}
    (h1 : spErr X1 X2 w1 w2 s1) (h2 : spErr X2 X3 w2 w3 s2) : spErr X1 X3 w1 w3 (s1 ++ s2) := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := h2
  refine ⟨a2.trans a1, ?_, c2.trans c1, d2.trans d1, e2.trans e1, fun h => f2 (f1 h), ?_⟩
  · rw [b2, wtxid_of_C a1, b1, applySteps_append]
  · rw [g2, g1]

/-- **A frame's error facts**, with the database facts. -/
theorem spErr_of_frame {X X' : WX} {w w' : WDb} {st : List FLStep} {bl : Loc} {T : List Loc}
    (hfr : spFrame X X' bl T) (hC : w'.C = w.C) (hfl : w'.fl = w.fl.applySteps w.wtxid st)
    (hpg : X'.v.pages = X.v.pages) : spErr X X' w w' st := by
  obtain ⟨a, -, -, -, -, -, g, i, -, -, -, m, -, o, -⟩ := hfr
  refine ⟨hC, hfl, hpg, g, a, fun hs => ?_, i⟩
  rw [a]
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hs
  by_cases hb : X.rl = bl
  · obtain ⟨B', hB', -⟩ := o B (hb ▸ hB)
    rw [hb, hB']; rfl
  · obtain ⟨B', hB', -⟩ := m X.rl hb B hB
    rw [hB']; rfl

/-- **`allocate`'s error after a remap** (`dereference`'s step, then the re-base): no step. -/
theorem spErr_rebase {X Xd : WX} {w w' : WDb} (hd : derefRel X Xd) (b : Loc) (hC : w'.C = w.C)
    (hfl : w'.fl = w.fl) : spErr X (Xd.rebase b) w w' [] := by
  have hs := hd.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hv, -, -, -, hrl, htt, hmv, -, -, -, -, -, hbs⟩ := hs
  refine ⟨hC, hfl, ?_, htt, hrl, fun h => ?_, ?_⟩
  · show Xd.v.pages = X.v.pages; rw [hv]
  · show ((Xd.rebase b).t.bs !! Xd.rl).isSome = true
    rw [rebase_bs, hrl]
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨B', hB', -⟩ := optRel_some_l (hB ▸ hbs X.rl)
    rw [hB']; rfl
  · show Xd.t.mv = { X.t.mv with pgid' := Xd.t.mv.pgid' }
    exact meta_with_pgid_of_eq hmv

/-- **A node's record set**: no step, nothing of the error facts changed. -/
theorem spErr_setNode (X : WX) (w : WDb) (bl l : Loc) (r' : NRec) :
    spErr X (X.setNode bl l r') w w [] := by
  cases hB : X.t.bs !! bl with
  | none =>
    have e : X.setNode bl l r' = X := by unfold WX.setNode; rw [hB]
    rw [e]; exact spErr_refl X w
  | some B =>
    have e : X.setNode bl l r' =
        { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := B.ns.insert l r' } } } := by
      unfold WX.setNode WX.setBkt; rw [hB]
    rw [e]
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun h => ?_, meta_with_pgid_self _⟩
    show ((X.t.bs.insert bl _) !! X.rl).isSome = true
    by_cases hb : bl = X.rl
    · subst hb; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ hb]; exact h

/-- Error facts with equal step lists. -/
theorem spErr_st {X X' : WX} {w w' : WDb} {s s' : List FLStep} (h : spErr X X' w w' s)
    (e : s = s') : spErr X X' w w' s' := e ▸ h

end err

end Spill

end bbolt
end EtcdGrove
end Perennial
