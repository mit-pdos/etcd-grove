/-
The raft node's queue of messages to the witness (2026-10-20, witness support,
`notes/raft-witness.md`): `r.witnessMsgs`, a slice of `WitnessMessage` values, each a request
`ownWMsg` holds (`InvWitness.lean`), whose protocol reading (`wAbs`) is on the node's abstract
outbox with the other queues' (`outboxRel`, `InvRaftPhys.lean`): an append to the witness is the
protocol's `wapp` (the subterm in `Commit`, the replication set's voters in `voters`), a vote
request its `wvote` (the responders in `voters`), a pre-vote request its `wprevote`, a heartbeat
an ordinary `heartbeat` (`HeartbeatOk`, to the witness). And `r.witnessVoteAsked`, the witnesses a
campaign asked: nil, or a map, which no protocol fact reads.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

/-- The protocol reading of a request to the witness (`StepC.sendWApp`, `askWitness`,
`sendWPre`, `beat`). -/
def wAbs [GooseExts] (μ : WMsg) : Msg :=
  if μ.ty = MsgApp then
    Msg.mkV .wapp μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] μ.rs0 []
  else if μ.ty = MsgVote then
    Msg.mkV .wvote μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] (elements (domSet μ.votes)) []
  else if μ.ty = MsgPreVote then
    Msg.mkV .wprevote μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] [] []
  else
    { Msg.plain .heartbeat μ.frm μ.to μ.term false with ctx := μ.ctx }

/-- A request's protocol reading is not a snapshot (2026-10-20). -/
theorem wAbs_not_snap [GooseExts] (μ : WMsg) : (wAbs μ).ty ≠ .snap := by
  unfold wAbs
  repeat (first | (split <;> try simp [Msg.mkV, Msg.plain]) | simp [Msg.mkV, Msg.plain])

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The queue `r.witnessMsgs` at `sl` holding the requests `μs` (stage W3: the slice owned, its
requests read-only). -/
def ownWQueue (sl : GoSlice) (μs : List WMsg) : IProp GF :=
  iprop(∃ (wms : List WitnessMessage), sl ↦* wms ∗ ownSliceCap WitnessMessage sl (DFrac.own 1) ∗
    [∗list] _k ↦ wm;μ ∈ wms;μs, ownWMsg wm μ)

/-- The empty queue, nil. -/
theorem ownWQueue_nil : ⊢ ownWQueue (GF := GF) slice.nil [] := by
  unfold ownWQueue
  iexists []
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ wm μ => ownWMsg (GF := GF) wm μ)).2; iempintro

/-- `r.witnessVoteAsked`: nil, or a map the node owns. -/
def ownAsked (m : Loc) : IProp GF :=
  iprop(⌜m = map.nil⌝ ∨ ∃ (a : GMap w64 Bool), m ↦$ a)

theorem ownAsked_nil : ⊢ ownAsked (GF := GF) map.nil := by
  unfold ownAsked; ileft; ipureintro; rfl

end own

end EtcdGrove
end Perennial
