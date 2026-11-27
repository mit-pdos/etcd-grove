/-
Lean-first (no Rocq counterpart).

# The drain's read numbers, with reads on (antithesis parity B1)

`AntSim.readyMsgNums`' premises other than `StateNums`, in a run with reads on (in place of
`DrainB1Bounds`' `readNums_noReads` and `causeNums_noReads`, which need reads off):

- the view's read requests, `AntSim.ReadNums (2 ^ 61) v.ps`: `AntSim.readNums_reach`
  (`Sim/ReadNums.lean`), from `NodeFacts`' `ReadOk` and the reached state's `StateNums`;
- the drain's cause, `causeNums_reach` (here): its index and log term (`ViewNormal`), not a
  proposal, and, when a `MsgReadIndex`, all its numbers (it is on the network under the mask,
  `MsgMask`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadNums

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

section pure
variable [GooseExts]

/-- **The drain's cause's numbers** (`AntSim.readyMsgNums`' cause premise), reads on or off: its
index and log term and not a proposal (`ViewNormal`); a `MsgReadIndex`'s numbers by its `MsgMask`
(`AntSim.causeReadNums`). -/
theorem causeNums_reach {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {n : Fin R.N} {v : AntSim.NodeView} (hnet : AntSim.NetOk R S net)
    (hv : AntSim.NodeOk R dec S net n v) (hN : ViewNormal v) :
    ∀ m, v.cause = some m → AntSim.InNums (2 ^ 61) m ∧ m.ty ≠ .propose ∧
      (m.ty = .readIndex → AntSim.MsgNums (2 ^ 61) m) := by
  intro m hm
  obtain ⟨-, hi, hl, hp⟩ := hN.2 m hm
  exact ⟨⟨hi, hl⟩, hp, AntSim.causeReadNums hnet hv m hm⟩

end pure

end AntHarness
end EtcdGrove
end Perennial
