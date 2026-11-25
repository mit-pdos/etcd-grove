/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Exec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: an execution step in full (`stepExec_full`: the applied pair `vt0` is the newer of the
copy's base and `PrevValTag`, the result is the CAS of it by the copy's first command with
`rmwc + 1`), and a projection's steps (`proj_step`).
-/
module

public import Dsverify.Proof.gryff.PureLc.FrameC

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem vt0_props (base : ValTag) (pv : Option ValTag) :
    tagLe base.t.toP (match pv with
      | none => base
      | some pvt => if base.t.gt pvt.t = true then base else pvt).t.toP ∧
    ∀ p, pv = some p → tagLe p.t.toP (match pv with
      | none => base
      | some pvt => if base.t.gt pvt.t = true then base else pvt).t.toP := by
  cases pv with
  | none => exact ⟨tagLe_refl _, fun p hp => by cases hp⟩
  | some pvt =>
    simp only [Option.some.injEq, forall_eq']
    by_cases hg : base.t.gt pvt.t = true
    · rw [if_pos hg]; exact ⟨tagLe_refl _, tagLe_of_lt ((Tag.gt_iff _ _).1 hg)⟩
    · rw [if_neg hg]
      exact ⟨(not_tagLt_iff _ _).1 (fun h' => hg ((Tag.gt_iff _ _).2 h')), tagLe_refl _⟩

theorem stepExec_full {s s' : RState} {q i : w32} {o : List Out} (h : stepExec s q i = .ok (s', o))
    {vt : ValTag} (hv : execRes o = some vt) :
    ∃ c c0 rest, s.inst q i = some c ∧ c.status = St.COMMITTED ∧ c.cmds = c0 :: rest ∧
      ∃ vt0 : ValTag, (vt0 = c.base ∨ s.prevValTag = some vt0) ∧
        tagLe c.base.t.toP vt0.t.toP ∧
        (∀ p, s.prevValTag = some p → tagLe p.t.toP vt0.t.toP) ∧
        vt.t = { vt0.t with rmwc := vt0.t.rmwc + 1 } ∧
        vt.v = (if c0.oldV = vt0.v then c0.v else vt0.v) := by
  unfold stepExec at h
  peel h
  · cases h; simp [execRes] at hv
  all_goals (
    cases h
    obtain ⟨d, rfl⟩ := sendTo_some ‹sendTo _ _ = some _›
    simp only [execRes, List.findSome?_cons, Option.some.injEq] at hv
    subst hv
    rename Copy => c
    refine ⟨c, _, _, ‹s.inst q i = some _›, by simpa using ‹¬ _ ≠ St.COMMITTED›,
      ‹(_ : Copy).cmds = _ :: _›, (match s.prevValTag with
      | none => c.base
      | some pvt => if c.base.t.gt pvt.t = true then c.base else pvt), ?_, ?_, ?_, ?_, ?_⟩)
  all_goals first
    | (split <;> (try split) <;> simp_all; done)
    | skip
  all_goals first
    | exact (vt0_props _ _).1
    | exact (vt0_props _ _).2
/-- Replica `r`'s `j`-th event in a run: an `.ok` step from its state after its first `j` events
(the run's state at the event's label `n`) to its state after `j + 1`, with outputs `outsOf`. -/
theorem proj_step {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {r : Fin 3}
    {j : Nat} {e : Ev} (hj : (projR l r)[j]? = some e) :
    ∃ n s' o, l[n]? = some (r, e) ∧ cutSt l n r = stOf r ((projR l r).take j) ∧
      stepR r (stOf r ((projR l r).take j)) e = .ok (s', o) ∧
      stOf r ((projR l r).take (j + 1)) = s' ∧ outsOf r (projR l r) j = o := by
  obtain ⟨n, hn, hp⟩ := proj_index l r hj
  obtain ⟨s', o, hs, h1, -, -, -⟩ := grun_label h hn
  have hc : cutSt l n r = stOf r ((projR l r).take j) := by unfold cutSt; rw [hp]
  rw [hc] at hs
  refine ⟨n, s', o, hn, hc, hs, ?_, ?_⟩
  · rw [← h1]; unfold cutSt
    have et : l.take (n + 1) = l.take n ++ [(r, e)] := by rw [List.take_add_one, hn]; rfl
    rw [et, proj_snoc, if_pos rfl, hp, List.take_add_one, hj]; rfl
  · unfold outsOf resOf; rw [hj]; simp only; rw [hs]

end Perennial.gryff.pure
