/-
Lean-first (no Rocq counterpart). #33 parity B2: **a synchronous run without split writes is within
`AntSim.mskB2`** (`inMask_b1_of`'s, over `AntSimD`): its features the scope's (`ModeRun`), within
`mskB2.md` by `DrainB2`'s scope bits and synchronous storage; its driver modes the mode's, the split
order `none`; every message sent under the run's mask (`NetOkD`'s `MsgMask`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A run within `mskB2`'s features, without split writes, is within `mskB2`** (`AntSimD`'s
`MsgMask`). -/
theorem inMask_b2_of {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State}
    {V : Fin R.N → AntSim.NodeView} {net : List Msg} {xnet : List XMsg}
    (hmd : AntSim.RnMode.Le R.md AntSim.mskB2.md) (hs : R.drv.split = 0)
    (hA : AntSim.AntSimD R dec S V net xnet) : AntSim.InMask AntSim.mskB2 R net xnet := by
  obtain ⟨-, -, hn, -, -⟩ := hA
  have hmm : ∀ m ∈ net, AntSim.MsgMask R m := hn.2.2.2.2.1
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hmd
  refine ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [AntSim.NodeK.Le, AntSim.BLe, AntSim.mskB2]
  · simp [AntSim.BLe, AntSim.mskB2]
  · simp [AntSim.BLe, AntSim.mskB2]
  · intro h; exact absurd hs h
  · simp [AntSim.BLe, AntSim.mskB2]
  · intro m hm
    obtain ⟨-, -, h3, -⟩ := hmm m hm
    rcases h3 with h | h
    · left
      simp only [AntSim.NetTy] at h ⊢
      rcases h with h | h | h | h | h | h | ⟨hpv, h⟩ | ⟨hrd, h⟩ | ⟨hsn, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))))))
      · exact absurd (m6 hsn) (by simp [AntSim.mskB2])
    · exact Or.inr h
  · intro h; simp [AntSim.mskB2] at h

/-- **A synchronous run of B2's off bits without split writes is within `mskB2`** (the drain's
`hinm`, from the cluster's `ModeRun` and `DrainB2`). -/
theorem inMask_b2_run {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} {dec : CCDec}
    (hmr : ModeRun s m R) (hb2 : DrainB2 s m) (has : m.Async' = false) (hsp : m.Split' = W64 0) :
    ∀ S V net xnet, AntSim.AntSimD R dec S V net xnet → AntSim.InMask AntSim.mskB2 R net xnet := by
  intro S V net xnet hA
  obtain ⟨-, -, -, -, hmd, hdrv⟩ := hmr
  obtain ⟨-, hsn, hcc, hfw, -⟩ := hb2
  refine inMask_b2_of ?_ ?_ hA
  · rw [hmd]
    simp [AntSim.RnMode.Le, AntSim.BLe, scopeMd, AntSim.mskB2, hfw, has, hsn, hcc]
  · rw [hdrv]; simp [modeDrv, hsp]

end pure

end AntHarness
end EtcdGrove
end Perennial
