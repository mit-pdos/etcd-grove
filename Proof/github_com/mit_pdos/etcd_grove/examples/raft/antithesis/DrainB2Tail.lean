/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (the synchronous `node.drain`): **the
iteration after the write under B2** (`DrainB1Phases`' `drainSendB1.stmt`/`drainAdvanceB1.stmt` over
B2's vocabulary), statements only (round 19: nothing proves them yet):
- `drainDeadB2`: the iteration's state once the node died after its write (a fuse burnt out in the send
  loop's `reportCause`/`emit`, or in `reads`/`applyCommitted`): `drain` goes on to `Advance` and `sent`
  (its next `!n.dead` ends the loop), nothing more recorded; what `nodeOwnB2HD_dead_intro` takes, the
  `RawNode` at the `Ready`'s record, and the `Ready`'s pieces `Advance` takes;
- `drainSendB2.stmt`: the send loop (`node.drain.sendE`), from the state after the write (`drainMidB2`),
  the messages as the write left them (`drainMsgsB1`, or after `parallel`, `early`, its requests sent:
  `drainMsgsParB2`);
- `drainAdvanceB2.stmt`: the iteration's end (`node.drain.tailE`), alive or dead.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The iteration's state once the node died after its write**: the node's fields (the cause cell
with whatever it holds), the kill flag set, the view frozen at `v` (normal, the disk against it; a
death needs a fuse, so restarts are on), the storage, the `RawNode` at the `Ready`'s record `rs₂`
(`rAccepted r`), raft's ghost pieces (the durable ghost at `D`, the disk's), the bookkeeping dead;
`Advance`'s fragments of the durable maps, the committed entries' and the read states' slices. -/
def drainDeadB2 (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (I : DrainIterB1) : IProp GF :=
  iprop(∃ (v : AntSim.NodeView) (d ms hsl cl csl : Loc) (role : GoString) (applied fuse : w64)
      (dk : AntSim.DurW) (si : Loc) (x : CrashNames) (g : Nat) (D : RaftState) (hn : HardStateM)
      (o : Option AntCheck.Event),
    n.[H.node, go!"disk"] ↦□ d ∗ n.[H.node, go!"rn"] ↦ I.rn ∗ n.[H.node, go!"store"] ↦ ms ∗
    n.[H.node, go!"role"] ↦ role ∗ n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗
    pendingCause cl o ∗ n.[H.node, go!"applied"] ↦ applied ∗ n.[H.node, go!"conf"] ↦ csl ∗
    killOwn n true fuse ∗ viewFrag γ.toAntNames j v ∗ diskOwn d dk ∗
    ⌜ViewNormal v ∧ DiskRel v dk ∧ γ.mode.Restarts' = true⌝ ∗
    nodeStor si ms (votersW γ.toAntNames) hn ∗
    ⌜I.rs₂.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
    rawNode γ.raft.raftNames γ.R.md I.rn (AntSim.nodeId j) I.rs₂ (rAccepted I.r) I.qs I.ip ∗
    genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
    ownDurGhost γ.raft.raftNames (AntSim.nodeId j) D ∗ rnTermLB γ.raft I.rs₂.tc ∗ rnBudget γ.raft ∗
    ⌜StorageHolds D (diskContents dk) ∧ uint.Z D.term ≤ uint.Z I.rs₂.tc⌝ ∗
    nodeMemB2 γ j n v x g I.rs₂.phs I.rs₂.dur D true none ∗ hsRO hsl hn ∗
    durFrags γ.raft.raftNames (AntSim.nodeId j) I.W ∗
    entsRO I.rd.CommittedEntries' I.ce ∗
    readStatesPts I.rd.ReadStates' I.sts ∗
    ([∗list] st ∈ I.sts, readStateRaw γ.raft.raftNames st))

/-- **The send loop under B2** (`node.drain.sendE`, then the continuation `K`; synchronous storage, no
batching, no split write): from the state after the write (`drainMidB2`, alive) with the `Ready`'s
protocol and transfer readings pending (in the messages' order; after `parallel`, `early`, its requests
already sent), each message not yet sent reported (`reportCause`, `emit(sendEv)`) and handed over
(`sendMsg`), while the node lives; then `K` with the messages frozen and the node alive at a view with
nothing pending, the sent lists' lower bounds grown, or dead (`drainDeadB2`). -/
abbrev drainSendB2.stmt : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (np bp rdp ep c n : Loc) (γ : AntNamesB2) (j : Fin γ.R.N)
    (I : DrainIterB1) (early : Bool) (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg)
    (q : Qp) (K : Expr) (Φ : val → IProp GF),
  γ.mode.Async' = false → γ.mode.Batch' = false → γ.mode.Split' = W64 0 →
  v₁.pend = (I.ms.filter (fun m => !(early && isRequestTy m.st.msg.Type'))).filterMap
    (fun m => absMsgOf m.st) →
  v₁.xpend = I.ms.filterMap (fun m => xmsgOf m.st) →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ ⌜DrainB2 γ.scope γ.mode⌝ ∗
      np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ ep ↦ early ∗
      drainMidB2 γ j n I v₁ net₁ xnet₁ ∗
      (if early then drainMsgsParB2 γ j I else drainMsgsB1 γ.toAntNames j I) ∗
      nodeExitB2 c γ q ∗ threadTok ∗
      (∀ (v₂ : AntSim.NodeView) (net₂ : List Msg) (xnet₂ : List XMsg),
        np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ ep ↦ early ∗ drainSentB1 I ∗ nodeExitB2 c γ q ∗
          threadTok ∗
          ((drainMidB2 γ j n I v₂ net₂ xnet₂ ∗ ⌜v₂.pend = [] ∧ v₂.xpend = []⌝) ∨ drainDeadB2 γ j n I) -∗
          WP K {{ Φ }}) ⊢
    WP (App (App (Val exceptionSeq) (Lam BAnon K))
      (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.sendE np bp rdp ep))
      {{ Φ }}

/-- **The iteration's end under B2** (`node.drain.tailE`; synchronous storage, no batching, no split
write): from the state after the send loop, alive with nothing pending or dead, the read states reported
(`reads`), the committed entries reported and `n.applied` set (`applyCommitted`), `Advance`, each
message's `sent`: alive, the next loop head (`nodeOwnB2 … (.loop net' xnet' r' [])`, the `by` kept), or
dead (drained: `drain`'s next `!n.dead` ends it). -/
abbrev drainAdvanceB2.stmt : Prop :=
  ∀ (np bp rdp c n : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (I : DrainIterB1) (v₂ : AntSim.NodeView)
    (net₂ : List Msg) (xnet₂ : List XMsg) (q : Qp) (Φ : val → IProp GF),
  γ.mode.Async' = false → γ.mode.Batch' = false → γ.mode.Split' = W64 0 →
  isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ ⌜DrainB2 γ.scope γ.mode⌝ ∗
      np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ drainSentB1 I ∗ nodeExitB2 c γ q ∗
      ((drainMidB2 γ j n I v₂ net₂ xnet₂ ∗ ⌜v₂.pend = [] ∧ v₂.xpend = []⌝) ∨ drainDeadB2 γ j n I) ∗
      (∀ (v' : AntSim.NodeView) (net' : List Msg) (xnet' : List XMsg) (r' : RState),
        np ↦ n ∗ bp ↦ I.v.byE ∗ nodeExitB2 c γ q ∗
          ((nodeOwnB2 c γ j n v' (.loop net' xnet' r' []) ∗ ⌜v'.byE = I.v.byE⌝) ∨
            nodeOwnB2HD c γ j n v' .drained none true) -∗ Φ executeVal) ⊢
    WP (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.tailE np bp rdp)
      {{ Φ }}

end defs

end AntHarness
end EtcdGrove
end Perennial
