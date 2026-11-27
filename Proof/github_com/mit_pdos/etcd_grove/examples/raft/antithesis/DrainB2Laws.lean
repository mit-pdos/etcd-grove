/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **the Sim steps of a `-parallel`
leader's `Ready` that `StmtsB2` does not state** (round 6), as pure laws the harness proofs take
(as B1's `node.drain` took `antSim_readyA.law`); the Link passes the Sim's theorems once proved:
- `antSim_sendD_in.law`: `antSim_send`'s step (sync) over `AntSimD`, at a mask `msk ≤ mskB2`, unbatched (the
  requests `parallel` sends before its write, and every message of a sync `Ready` after it);
- `reach_fpD.law`, `dst_reachD.law`: `Sim/MsgShape`'s `reach_fp` and `dst_reach` over `NodeOkD`
  (`NetOkD`), unbatched, for the masks below `mskB2` (no snapshot is received; the outbox is empty
  between `Ready`s without batching, `NodeFactsD`); `DrainB2Report.readyOutP_d` takes them.
`mem`, `write` and `wrote` of `-parallel` are `StmtsB2`'s (`antSim_memP_in.stmt`,
`antSim_write_in.stmt`, `antSim_wrote_in.stmt`), taken as they are; its unreported `Ready` is
`Sim/QuietP`'s theorem `AntSim.antSim_quietP_in`, used directly.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShape

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section laws
variable [GooseExts]

/-- **`send` (sync) under B2** (`AntSim.antSim_send.stmt`'s step over `SimPreD`/`SimStepD`, at a
mask `msk ≤ mskB2`): the node's next pending message is reported, then it is on the network; the
announced write is over. -/
abbrev antSim_sendD_in.law : Prop :=
  ∀ (msk : AntSim.SimMask), msk ≤ AntSim.mskB2 →
  ∀ (R : AntSim.RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) (evs : List AntCheck.Event) (G : AntSim.RaftFacts)
    (n : Fin R.N) (q : Msg) (rest : List Msg),
    AntSim.InMask msk R net xnet → AntSim.SimPreD R dec S V net xnet evs G → R.md.async = false →
    R.drv.batch = false → (V n).pend = q :: rest → AntSim.Told (V n) → AntSim.MsgFacts G q →
    AntSim.SimStepD R dec evs G (AntSim.evSend (AntSim.nodeId n) (V n).byE q)
      (AntSim.setV V n { V n with pend := rest, undo := none, made := true }) (net ++ [q]) xnet

/-- **The ghost prefix is kept along `ReachIn`, B2** (`AntSim.reach_fp` over `NodeOkD`; unbatched,
below `mskB2`: no snapshot is received). -/
abbrev reach_fpD.law : Prop :=
  ∀ {msk : AntSim.SimMask}, msk ≤ AntSim.mskB2 →
  ∀ {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop} {S : AntCheck.State}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState},
    AntSim.InMask msk R net xnet → R.drv.batch = false → AntSim.NodeOkD R dec S net n v →
    AntSim.ReachIn msk R dec Adm net xnet n v r₁ → r₁.fp = v.r.fp

/-- **The destinations of the messages of the state a `Ready` is taken at, B2** (`AntSim.dst_reach`
over `NetOkD`/`NodeOkD`; unbatched, below `mskB2`: the initial configuration, the outbox empty between
`Ready`s). -/
abbrev dst_reachD.law : Prop :=
  ∀ {msk : AntSim.SimMask}, msk ≤ AntSim.mskB2 →
  ∀ {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop} {S : AntCheck.State}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState},
    AntSim.InMask msk R net xnet → R.drv.batch = false → AntSim.NetOkD R S net →
    AntSim.NodeOkD R dec S net n v → AntSim.ReachIn msk R dec Adm net xnet n v r₁ →
    AntSim.DstIn R.N (AntSim.nodeId n) r₁.p

end laws

end AntHarness
end EtcdGrove
end Perennial
