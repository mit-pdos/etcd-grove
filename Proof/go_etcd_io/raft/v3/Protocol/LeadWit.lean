/-
# The leader witness (raft-final, 2026-10-29: U7, the design's §2.1)

A node that records another node as its leader at its term holds a witness that that node leads
it (`leadW`): `isLeader γ ps.lead ps.term` whenever `ps.lead` is neither `0` nor the node itself.
The self case needs no witness of its own: a node records itself only as leader (`LeadOk`), and a
leader holds its own (`leaderWit`).

What it is for: a re-forwarded `MsgTransferLeader`. A follower forwards a transfer request to its
leader stamped with its term (`stepFollower`, `raft.go:1757-1763`, `send` stamps `r.Term`); if the
receiver forwarded it again `send` would `Panicf` on the stamped message (`raft.go:534-536`). The
receiver R at the request's term T, a follower with a leader L, has `isLeader L T` (`leadW`); the
request carries `isLeader R T` (`isRaftMsg`, from the forwarder's `xfW`); `isLeader_unique` gives
`L = R`, which `LeadOk` refutes. So the receiver has no leader there and drops it (`raft.go:1758`).

Why it holds (`leadW_stepC`): the only rules that set `lead` to a node other than `0` or the node
are `higherTerm` for a `fromLeader` type and the adoptions at the current term (`appAccept`,
`appStale`, `appReject`, `heartbeat`, the snapshot rules), each on a received message of a type
whose `isMessage` holds `isLeader src term` (an `app`, a `heartbeat`, a `snap`). Every other rule
sets `0` or `id`, or keeps `lead` and `term`; no rule changes the term and keeps `lead`.

Statements only in raft-final's phase 1 (`notes/raft-unified-plan.md`, "Phase 1 sorries"): proved by
phase 2's track P1.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.StepC
public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF]

/-- **The leader witness** of node `id` at its protocol state `ps` (persistent): if it records a
leader other than itself, that node leads its term. -/
def leadW (γ : RaftNames) (id : w64) (ps : PState) : IProp GF :=
  iprop(□ (⌜ps.lead ≠ W64 0 ∧ ps.lead ≠ id⌝ -∗ isLeader γ ps.lead ps.term))

instance leadW_persistent (γ : RaftNames) (id : w64) (ps : PState) :
    Persistent (leadW (GF := GF) γ id ps) := by
  unfold leadW; infer_instance

/-- A state with no leader recorded (a new node's: `newRaft`, `Bootstrap`, `RestartNode`) has the
witness. -/
theorem leadW_none (γ : RaftNames) (id : w64) (ps : PState) (h : ps.lead = W64 0) :
    ⊢ leadW (GF := GF) γ id ps := by
  unfold leadW
  iintro !> %H
  exact absurd h H.1

/-- The witness reads only `lead` and `term`. -/
theorem leadW_eq (γ : RaftNames) (id : w64) (ps ps' : PState) (hl : ps'.lead = ps.lead)
    (ht : ps'.term = ps.term) : leadW (GF := GF) γ id ps ⊢ leadW γ id ps' := by
  unfold leadW
  rw [hl, ht]

/-- **A step keeps the witness** (`StepC`, which every branch of `raft.Step` delivers: `StepCD`,
`StepCDS`), given the received messages' facts. -/
theorem leadW_stepC (γ : RaftNames) (c : CfgM) (id : w64) (B : Int) (ps : PState) (recv : List Msg)
    (ps' : PState) (Hstep : StepC c id B ps recv ps') :
    ⊢ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗ leadW γ id ps -∗ leadW γ id ps' := by
  sorry

end ghost

end EtcdGrove
end Perennial
