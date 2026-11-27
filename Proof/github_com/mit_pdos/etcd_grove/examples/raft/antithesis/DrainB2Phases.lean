/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **the synchronous drain's iteration
under B2** (`DrainB1Phases`' over `nodeOwnB2`), statements only (round 4: nothing proves against
them yet):
- `loopRestB2`: `nodeOwnB2HD`'s alive `.loop` arm but the `RawNode` and the raft ghost pieces a
  `Ready` moves (the generation view, the durable ghost, the slot), at the durable ghost `D`;
- `drainPreB2`: right after a synchronous `Ready`, its enter promise (`Henter`) not fired: the
  durable ghost still at the loop head's `rs.dur` (the disk not written);
- `drainMidB2`: after the report and the write (`Henter` fired at its `saveDisk`, or right after a
  report with nothing to write), at the view `vv`: `drainMidB1`'s over `loopRestB2`, its locals
  (`n by rd`) left to the caller;
- `drainMsgsParB2`: the `Ready`'s messages after `parallel` (the requests sent and frozen, the others
  owned), each with raft's certificate.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The record right after a synchronous `Ready` (`RawNode.Ready.form`'s, no snapshot loan): `rs₂`
with the `Ready`'s entries not yet appended to the storage (`rawNode_appended` moves it to `rs₂`). -/
def DrainIterB1.rs₁ (I : DrainIterB1) : RNState := { I.rs₂ with unpersisted := I.es }

/-- **An iteration's pure facts under B2** (`DrainIterB1.Ok` with the drain's `by` one of B2's,
`ByOkB2`). -/
def DrainIterB1.OkB2 (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) : Prop :=
  RsView I.rs I.v ∧ I.rs.k = γ.R.k j ∧ ByOkB2 I.v.byE ∧
  I.qs ≡ₚ I.r.p.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j)) ∧
  ReadyOut (AntSim.nodeId j) I.rs I.r.p I.h I.es I.ce I.ms I.ss none ∧
  I.ip = I.r.p.log.length ∧
  (∀ q ∈ I.ms, (absMsgOf q.st).isSome ∨ (xmsgOf q.st).isSome) ∧
  (∀ q ∈ I.ms, ∀ x, xmsgOf q.st = some x →
    XReadyOk γ.raft.raftNames γ.R.md (AntSim.nodeId j) I.r.p x ∧ XZero q.st) ∧
  (γ.R.md.transfer = false → ∀ q ∈ I.ms, (absMsgOf q.st).isSome) ∧
  I.sts = I.r.p.rd.states ∧
  uint.Z I.rs.tc < 2 ^ 61 ∧ AntSim.StateNums (2 ^ 61) I.r.p ∧
  (∀ st ∈ I.sts, uint.Z st.Index' < 2 ^ 61)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The loop head's rest under B2** (`nodeOwnB2HD … (.loop net₀ xnet₀ _ _) none false`, alive, but
`n.rn`, the `RawNode`, the generation view `genView … x 1 g`, the durable ghost `ownDurGhost … D` and
the slot): the fields (`n.hs` at `hsl`, the caller's: `drain` compares it with the `Ready`'s hard
state), the kill fields alive, the view fragment, the disk at `dk` against the view and against `D`
(`StorageHolds`), the storage, the term bounds, the bookkeeping (`nodeMemB2` at `rs`'s hard state and
durable state), `n.hs` the view's disk's (synchronous storage), the role, `applied`, the
configuration, the reads, the sent lists' lower bounds, the cause cell. -/
def loopRestB2 (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (rs : RNState) (x : CrashNames) (g : Nat) (D : RaftState) (hsl : Loc) :
    IProp GF :=
  iprop(∃ (d ms cl csl : Loc) (role : GoString) (applied fuse : w64) (dk : AntSim.DurW) (si : Loc)
      (hn : HardStateM),
    n.[H.node, go!"disk"] ↦□ d ∗ n.[H.node, go!"store"] ↦ ms ∗ n.[H.node, go!"role"] ↦ role ∗
    n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗ n.[H.node, go!"applied"] ↦ applied ∗
    n.[H.node, go!"conf"] ↦ csl ∗ killOwn n false fuse ∗
    viewFrag γ.toAntNames j v ∗ diskOwn d dk ∗
    ⌜ViewNormal v ∧ DiskRel v dk ∧ (γ.mode.Restarts' = false → fuse = W64 0)⌝ ∗
    nodeStor si ms (votersW γ.toAntNames) hn ∗
    ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
    rnTermLB γ.raft rs.tc ∗ rnBudget γ.raft ∗
    ⌜StorageHolds D (diskContents dk) ∧ uint.Z D.term ≤ uint.Z rs.tc⌝ ∗
    nodeMemB2 γ j n v x g rs.phs rs.dur D false none ∗
    hsRO hsl hn ∗
    ⌜v.alive = true ∧ role = AntSim.roleS v ∧ uint.nat applied = v.delivered.length ∧ rs.k = γ.R.k j ∧
      (γ.mode.Async' = false → hn = HardStateM.mk v.dur.term v.dur.vote v.dur.commit)⌝ ∗
    csPts csl DFrac.discard (ConfStateM.mk (votersW γ.toAntNames) [] [] [] false) false ∗
    readsOwn γ.toAntNames v ∗ ⌜v.conf = γ.R.c0⌝ ∗
    sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗ causeOwn γ.toAntNames j v cl)

/-- **A synchronous `Ready`'s enter promise** (`RawNode.Ready.form`'s `Henter` at the iteration's
record, no snapshot loan): from the loop head's durable state to the `Ready`'s, the slot back, the
durable maps' fragments, the messages certified. -/
def readyEnterB2 (γ : AntNamesB2) (j : Fin γ.R.N) (I : DrainIterB1) (x : CrashNames) (g : Nat) :
    IProp GF :=
  iprop(∀ (E : CoPset) (q' : Qp), ⌜↑(raftN γ.raft.raftNames) ⊆ E⌝ -∗ notCrashed -∗
    ownDurGhost γ.raft.raftNames (AntSim.nodeId j) I.rs.dur ∗
      genView γ.raft.raftNames (AntSim.nodeId j) x q' g ={E}=∗
      notCrashed ∗ ownDurGhost γ.raft.raftNames (AntSim.nodeId j) I.rs₂.dur ∗
      genView γ.raft.raftNames (AntSim.nodeId j) x q' g ∗
      slotFree γ.raft.raftNames (AntSim.nodeId j) g ∗ durFrags γ.raft.raftNames (AntSim.nodeId j) I.W ∗
      [∗list] q ∈ I.ms, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) q.st)

/-- **The iteration's state right after a synchronous `Ready`**, its write not entered: `n.rn` and the
`RawNode` at `rs₁` (`rAccepted r`; the entries not yet appended), the loop head's rest at the loop
head's view `I.v`, record `I.rs` and durable ghost `I.rs.dur` (`n.hs` at `hsl`), the generation view,
the durable ghost, the enter promise (`readyEnterB2`); the `Ready`'s fields read-only (hard state,
entries, committed entries, read states with raft's certificates), its append receipt to come
(`readyOut`), its messages owned (a leader's certified at once: `RawNode.Ready.form`'s `Hlead`); the
loop head's facts (`Reach` from the sent lists' lower bounds `net₀ xnet₀`, `n.hs` the view's disk's),
the iteration's (`OkB2`). -/
def drainPreB2 (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (I : DrainIterB1) (x : CrashNames) (g : Nat)
    (net₀ : List Msg) (xnet₀ : List XMsg) (hsl : Loc) : IProp GF :=
  iprop(n.[H.node, go!"rn"] ↦ I.rn ∗
    rawNode γ.raft.raftNames γ.R.md I.rn (AntSim.nodeId j) I.rs₁ (rAccepted I.r) I.qs I.ip ∗
    loopRestB2 γ j n I.v net₀ xnet₀ I.rs x g I.rs.dur hsl ∗
    genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
    ownDurGhost γ.raft.raftNames (AntSim.nodeId j) I.rs.dur ∗
    readyEnterB2 γ j I x g ∗
    hsOptC I.rd.HardState' I.h ∗ entsROz false I.rd.Entries' I.es ∗
    readyOut I.rs.storage I.rs.sn I.es none ∗
    entsRO I.rd.CommittedEntries' I.ce ∗
    readStatesPts I.rd.ReadStates' I.sts ∗
    ([∗list] st ∈ I.sts, readStateRaw γ.raft.raftNames st) ∗
    I.rd.Messages' ↦* I.ms.map QMsg.loc ∗ ownSliceCap Loc I.rd.Messages' (DFrac.own 1) ∗
    ([∗list] q ∈ I.ms, msgOwnZ false q.loc (readyDq q.st) q.st) ∗
    (⌜roleAfter I.rs.role I.ss = StateLeader⌝ -∗
      [∗list] q ∈ I.ms, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) q.st) ∗
    ⌜AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j I.v I.r ∧
      (∀ q ∈ I.ms, DrainMsgOkB1 γ.R I.rs.tc q) ∧ I.OkB2 γ.toAntNames j⌝)

/-- **The iteration's state after the report and the write** (`drainMidB1`'s, but `drain`'s locals),
at the view `vv` and the sent lists' lower bounds `net`, `xnet`: `n.rn` and the `RawNode` at `rs₂`
(`rAccepted r`, the entries appended), the loop head's rest at `vv` and `rs₂` with the durable ghost
at the `Ready`'s durable state (the write entered), the generation view, the durable ghost, the slot
free; `Advance`'s fragments of the durable maps (`durFrags`), the committed entries' and the read
states' slices with raft's certificates of the read states; the view the `Ready`'s (its state
`accepted r`, its queue, committed entries and read states to report, the loop head's `by`), the
record against it (but the steps `Advance` takes), and the iteration's facts. -/
def drainMidB2 (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (I : DrainIterB1) (vv : AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) : IProp GF :=
  iprop(∃ (x : CrashNames) (g : Nat) (hsl : Loc),
    n.[H.node, go!"rn"] ↦ I.rn ∗
    rawNode γ.raft.raftNames γ.R.md I.rn (AntSim.nodeId j) I.rs₂ (rAccepted I.r) I.qs I.ip ∗
    loopRestB2 γ j n vv net xnet I.rs₂ x g I.rs₂.dur hsl ∗
    genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
    ownDurGhost γ.raft.raftNames (AntSim.nodeId j) I.rs₂.dur ∗
    slotFree γ.raft.raftNames (AntSim.nodeId j) g ∗
    durFrags γ.raft.raftNames (AntSim.nodeId j) I.W ∗
    entsRO I.rd.CommittedEntries' I.ce ∗
    readStatesPts I.rd.ReadStates' I.sts ∗
    ([∗list] st ∈ I.sts, readStateRaw γ.raft.raftNames st) ∗
    ⌜vv.r = AntSim.accepted I.r ∧ vv.qs = I.qs ∧ vv.ce = I.ce ∧ vv.rpend = I.sts ∧
      vv.byE = I.v.byE ∧ RsViewB2 γ.mode { I.rs₂ with steps := [] } vv ∧ I.OkB2 γ.toAntNames j⌝)

/-- **The `Ready`'s messages after `parallel`**: the slice; each request (`isRequest`: an append or a
heartbeat) sent, frozen (`msgPtsC`, as `node.sendMsg` leaves it), each other one owned
(`RawNode.Ready.form`'s `msgOwnZ`); each one certified (`isRaftMsg`: a leader's, `Hlead`) and with
its facts (`DrainMsgOkB1`). -/
def drainMsgsParB2 (γ : AntNamesB2) (j : Fin γ.R.N) (I : DrainIterB1) : IProp GF :=
  iprop(I.rd.Messages' ↦* I.ms.map QMsg.loc ∗ ownSliceCap Loc I.rd.Messages' (DFrac.own 1) ∗
    ([∗list] q ∈ I.ms, if isRequestTy q.st.msg.Type' then msgPtsC q.loc DFrac.discard DFrac.discard false q.st
      else msgOwnZ false q.loc (readyDq q.st) q.st) ∗
    ([∗list] q ∈ I.ms, isRaftMsg γ.raft.raftNames (AntSim.nodeId j) q.st) ∗
    ⌜∀ q ∈ I.ms, DrainMsgOkB1 γ.R I.rs.tc q⌝)

end defs

end AntHarness
end EtcdGrove
end Perennial
