/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (`node.parallel`): **a Sim fact
`node.parallel.wp_proof` takes as a law** until the Sim proves it (lead-approved, round 16), the exact
statement of the Sim theorem that will replace it (then passed as `=AntSim.leadHs_reachD` in the link):
`leadHs_reachD.law`: a leader's `Ready` keeps the disk's term and vote (synchronous storage, no
  batching, no `mem` queued and no split write: a candidate's campaign `Ready` persists the vote, a
  leader's arms keep the term and vote): what `readyExt_b1` needs of the durable ghost before the
  write.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section laws
variable [GooseExts]

/-- `AntSim.leadHs_reachD`'s statement (the Sim helper's, round 16). -/
abbrev leadHs_reachD.law : Prop :=
  ∀ {msk : AntSim.SimMask} (_hmsk : msk ≤ AntSim.mskB2) {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState} {rd : AntSim.ReadyD},
    AntSim.InMask msk R net xnet → R.md.async = false → R.drv.batch = false →
    AntSim.NetOkD R S net → AntSim.NodeOkD R dec S net n v → v.mems = [] → v.parts = [] →
    AntSim.ReachIn msk R dec Adm net xnet n v r₁ → AntSim.ReadyOutP R n v r₁ rd →
    rd.role = .leader →
    r₁.p.term = v.dur.term ∧ r₁.p.vote = v.dur.vote

end laws

end AntHarness
end EtcdGrove
end Perennial
