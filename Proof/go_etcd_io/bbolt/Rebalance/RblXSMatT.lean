/-
Helpers for `rblX` through a materialization (U8b, `Rebalance/RblXSteps.lean`'s `rblX_mat`): a
finite tree survives a change of the logical tree by data only (`ltIs_ldat`: same positions,
height, depths); a path grows with children appended (`descIn_snoc`, `descIn_grow`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSCol
public import Proof.go_etcd_io.bbolt.Write.FlView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section matt
variable [GooseExts]

theorem map_pgid_of_wDat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    ws'.map WEntry.pgid = ws.map WEntry.pgid := by
  have := congrArg (List.map fun d => d.2.1) h
  simpa [List.map_map, Function.comp_def, wDat] using this

theorem ldat_some {x : Option (Bool × List WEntry)} {b : Bool} {ws : List WEntry}
    (h : Write.ldat x = Write.ldat (some (b, ws))) :
    ∃ ws', x = some (b, ws') ∧ ws'.map wDat = ws.map wDat := by
  cases x with
  | none => simp [Write.ldat] at h
  | some y =>
    obtain ⟨b', ws'⟩ := y
    simp only [Write.ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨ws', rfl, h2⟩

section
variable (L L' : LTree) (bl : Loc) (h : ∀ q, Write.ldat (L' bl q) = Write.ldat (L bl q))
include h

mutual
/-- **A tree survives a change by data only.** -/
theorem ltIs_ldat : ∀ (t : RTree), ltIs L bl t → ∃ t', ltIs L' bl t' ∧ t'.pid = t.pid ∧
    t'.ht = t.ht ∧ ∀ d, t'.dps d = t.dps d
  | .mk p true ws cs, ht => by
    simp only [ltIs] at ht
    obtain ⟨hL, rfl⟩ := ht
    have := h p; rw [hL] at this
    obtain ⟨ws', hL', -⟩ := ldat_some this
    exact ⟨.mk p true ws' [], ⟨hL', rfl⟩, rfl, rfl, fun d => rfl⟩
  | .mk p false ws cs, ht => by
    simp only [ltIs] at ht
    obtain ⟨hL, hcs⟩ := ht
    have := h p; rw [hL] at this
    obtain ⟨ws', hL', hw⟩ := ldat_some this
    obtain ⟨cs', hcs', hh, hd⟩ := ltIsL_ldat ws cs hcs ws' (map_pgid_of_wDat hw)
    exact ⟨.mk p false ws' cs', ⟨hL', hcs'⟩, rfl, by simp only [RTree.ht]; exact hh,
      fun d => by simp only [RTree.dps]; exact hd (d + 1)⟩
theorem ltIsL_ldat : ∀ (ws : List WEntry) (cs : List RTree), ltIsL L bl ws cs →
    ∀ ws', ws'.map WEntry.pgid = ws.map WEntry.pgid →
    ∃ cs', ltIsL L' bl ws' cs' ∧ RTree.htL cs' = RTree.htL cs ∧
      ∀ d, RTree.dpsL d cs' = RTree.dpsL d cs
  | [], [], _, ws', hw => by
    cases ws' with
    | nil => exact ⟨[], trivial, rfl, fun _ => rfl⟩
    | cons _ _ => simp at hw
  | w :: ws, t :: ts, hl, ws', hw => by
    simp only [ltIsL] at hl
    obtain ⟨hp, ht, hts⟩ := hl
    cases ws' with
    | nil => simp at hw
    | cons w' ws'' =>
      simp only [List.map_cons, List.cons.injEq] at hw
      obtain ⟨t', ht', hpid, hh, hd⟩ := ltIs_ldat t ht
      obtain ⟨ts', hts', hh', hd'⟩ := ltIsL_ldat ws ts hts ws'' hw.2
      refine ⟨t' :: ts', ⟨by rw [hpid, hp, hw.1], ht', hts'⟩, ?_, fun d => ?_⟩
      · simp only [RTree.htL]; rw [hh, hh']
      · simp only [RTree.dpsL]; rw [hd, hd']
  | [], _ :: _, hl, _, _ => by simp only [ltIsL] at hl
  | _ :: _, [], hl, _, _ => by simp only [ltIsL] at hl
end

end

/-- A path extended by a child. -/
theorem descIn_snoc (B : BRec) : ∀ a b, descIn B a b → ∀ rb c, B.ns !! b = some rb → c ∈ rb.cs →
    descIn B a c := by
  intro a b h
  induction h with
  | self x => intro rb c hb hc; exact descIn.child x c c rb hb hc (descIn.self c)
  | child a c d ra ha hc _ ih =>
    intro rb c' hb hc'
    exact descIn.child a c c' ra ha hc (ih rb c' hb hc')

/-- A path survives nodes gaining children. -/
theorem descIn_grow (B B' : BRec)
    (hk : ∀ x rx, B.ns !! x = some rx → ∃ rx', B'.ns !! x = some rx' ∧ ∀ c ∈ rx.cs, c ∈ rx'.cs) :
    ∀ a d, descIn B a d → descIn B' a d := by
  intro a d h
  exact descIn_mono B B' (fun _ => True) (fun _ _ _ _ _ _ => trivial)
    (fun x rx hx _ => hk x rx hx) a d h trivial

end matt

end bbolt
end EtcdGrove
end Perennial
