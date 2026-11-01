/-
(raft-final phase 2, track P3b) `RNPv`/`LoanOk` across a `raft.Step` that changes the ghost state only
in `xw` (a transfer request's forward, `raft.Step`'s `"%Hxwframe"`): what `RawNode.Step` and
`RawNode.TransferLeader` rebuild `ownRawNode` with. (The same as `InvNodeRun`'s private
`RNPv.step_xw`/`LoanOk.step_xw`, which P4 wrote at the same time.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]

/-- `RNPv.step` across a step that changes the ghost state only in `xw`. -/
theorem RNPv.step_gxw [GoGlobalContext] [GoSemanticsFunctions] {rs rs' : RNState}
    {fp : List EntryM} {s s' : NState} {m : MessageM}
    (H : RNPv rs fp s)
    (hmd : rs'.mode = rs.mode) (htc : rs'.tc = rs.tc) (_hpv : s'.prevote = s.prevote)
    (hgh : s'.gh = { s.gh with xw := s'.gh.xw }) (ht : uint.Z s'.term ≤ uint.Z s.gh.tc)
    (hpc : PreCandStep m s s')
    (hhup : m.Type' = MsgHup → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) : RNPv rs' fp s' := by
  obtain ⟨H1, H2, -, H4, H5⟩ := H
  refine ⟨fun h => PreGuardF.pc hpc (H1 (hmd ▸ h)), by rw [htc, hgh]; exact H2,
    by rw [hgh]; exact ht, fun h => ?_, H5.step hpc.2⟩
  obtain ⟨Ht, Hor⟩ := hpc.1 h
  rw [hgh, Ht]
  rcases Hor with ⟨Hr, -⟩ | ⟨Hh, -⟩
  · exact H4 Hr
  · exact hhup Hh

/-- `LoanOk.step` across a step that changes the ghost state only in `xw`. -/
theorem LoanOk.step_gxw {rs : RNState} {s s' : NState} {b : Bool} (t : w64) (H : LoanOk rs s)
    (hgh : s'.gh = { s.gh with xw := s'.gh.xw })
    (hkeep : rs.slent ≠ none →
      (s'.logst.snap = s.logst.snap ∨
        ∃ s2, s'.logst.snap = some s2 ∧ uint.Z s.logst.committed < uint.Z s2.index' ∧
          b = true) ∧
      s'.logst.fl = s.logst.fl ∧
      s'.logst.stored = s.logst.stored ∧ s'.logst.unpersisted = s.logst.unpersisted ∧
      s'.logst.applying = s.logst.applying ∧
      uint.Z s.logst.committed ≤ uint.Z s'.logst.committed) :
    LoanOk { rs with term := t, psnap := rs.psnap || b } s' := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨by rw [hgh]; exact H1, fun h => ?_, fun l h => ?_⟩
  · rw [hgh]; exact H2 h
  · have hl : rs.slent = some l := h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := H3 l hl
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hkeep (by rw [hl]; simp)
    refine ⟨by rw [hgh]; exact a1, ?_, Int.le_trans a3 k6, by rw [k2]; exact a4,
      by rw [k3, k4]; exact a5, by rw [k5]; exact a6, a7, a8, a9⟩
    rcases k1 with k1 | ⟨s2, h2, hgt, hb⟩
    · rw [k1]
      rcases a2 with a2 | ⟨s2, h2, hlt, hps⟩
      · exact .inl a2
      · exact .inr ⟨s2, h2, hlt, by simp [hps]⟩
    · exact .inr ⟨s2, h2, by omega, by simp [hb]⟩

end lemmas

end EtcdGrove
end Perennial
