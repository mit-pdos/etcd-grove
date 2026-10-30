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

/-- The sender of a leader's message leads its term. -/
private theorem isMessage_fromLeader (γ : RaftNames) (m : Msg) (h : fromLeader m.ty = true) :
    isMessage (GF := GF) γ m ⊢ isLeader γ m.src m.term := by
  have Hty : m.ty = .app ∨ m.ty = .heartbeat ∨ m.ty = .snap := by
    revert h; cases m.ty <;> simp [fromLeader]
  rcases Hty with Hty | Hty | Hty
  · unfold isMessage; rw [Hty]
    iintro ⟨-, #Hl, -⟩; iexact Hl
  · unfold isMessage; rw [Hty]
    iintro ⟨#Hl, -⟩; iexact Hl
  · unfold isMessage; rw [Hty]
    iintro ⟨#Hl, -⟩; iexact Hl

private theorem leadW_keep (γ : RaftNames) (id : w64) (R : IProp GF) (ps ps' : PState)
    (hl : ps'.lead = ps.lead) (ht : ps'.term = ps.term) :
    ⊢ R -∗ leadW γ id ps -∗ leadW γ id ps' := by
  iintro - H
  iapply leadW_eq γ id ps ps' hl ht $$ H

private theorem leadW_zero (γ : RaftNames) (id : w64) (R : IProp GF) (ps ps' : PState)
    (hl : ps'.lead = W64 0 ∨ ps'.lead = id) :
    ⊢ R -∗ leadW γ id ps -∗ leadW γ id ps' := by
  iintro - -
  unfold leadW
  iintro !> %H
  rcases hl with h | h
  · exact absurd h H.1
  · exact absurd h H.2

private theorem leadW_adopt (γ : RaftNames) (id : w64) (m : Msg) (ps ps' : PState)
    (hl : ps'.lead = m.src) (ht : ps'.term = m.term) (hfl : fromLeader m.ty = true) :
    ⊢ ([∗list] x ∈ [m], isMessage (GF := GF) γ x) -∗ leadW γ id ps -∗ leadW γ id ps' := by
  iintro Hr -
  icases (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).1 $$ Hr with #Hm
  unfold leadW
  iintro !> -
  rw [hl, ht]
  iapply isMessage_fromLeader γ m hfl $$ Hm

private theorem preadRespondAll_lead_term (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).lead = s.lead ∧ (preadRespondAll id s qs).term = s.term := by
  obtain ⟨o, rd, h⟩ := preadRespondAll_eq id s qs
  rw [h]; exact ⟨rfl, rfl⟩

/-- **A step keeps the witness** (`StepC`, which every branch of `raft.Step` delivers: `StepCD`,
`StepCDS`), given the received messages' facts. -/
theorem leadW_stepC (γ : RaftNames) (c : CfgM) (id : w64) (B : Int) (ps : PState) (recv : List Msg)
    (ps' : PState) (Hstep : StepC c id B ps recv ps') :
    ⊢ ([∗list] m ∈ recv, isMessage (GF := GF) γ m) -∗ leadW γ id ps -∗ leadW γ id ps' := by
  induction Hstep with
  | refl => iintro - H; iexact H
  | trans s₀ r₁ s₁ r₂ s₂ _ _ ih1 ih2 =>
    iintro Hr H
    icases (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ Hr with
      ⟨Hr1, Hr2⟩
    iapply ih2 $$ Hr2
    iapply ih1 $$ Hr1 H
  | higherTerm m s =>
    by_cases h : fromLeader m.ty = true
    · exact leadW_adopt γ id m _ _ (by simp [pbecomeFollower, h]) rfl h
    · exact leadW_zero γ id _ _ _ (Or.inl (by simp [pbecomeFollower, h]))
  | campaign => exact leadW_zero γ id _ _ _ (Or.inl rfl)
  | grantVote => exact leadW_keep γ id _ _ _ rfl rfl
  | rejectVote => exact leadW_keep γ id _ _ _ rfl rfl
  | recordVote => exact leadW_keep γ id _ _ _ rfl rfl
  | win => exact leadW_zero γ id _ _ _ (Or.inr rfl)
  | lose => exact leadW_zero γ id _ _ _ (Or.inl rfl)
  | drain => exact leadW_keep γ id _ _ _ rfl rfl
  | appAccept m s _ _ Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | appStale m s Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | appReject m s _ _ Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | heartbeat m s Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | beat => exact leadW_keep γ id _ _ _ rfl rfl
  | appResp => exact leadW_keep γ id _ _ _ rfl rfl
  | commit => exact leadW_keep γ id _ _ _ rfl rfl
  | sendApps => exact leadW_keep γ id _ _ _ rfl rfl
  | propose => exact leadW_keep γ id _ _ _ rfl rfl
  | propForward => exact leadW_keep γ id _ _ _ rfl rfl
  | snapRestore m s Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | snapFastfwd m s Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | snapStale m s Hty _ _ Hterm =>
    exact leadW_adopt γ id m _ _ rfl Hterm.symm (by rw [Hty]; rfl)
  | takeReads => exact leadW_keep γ id _ _ _ rfl rfl
  | readFwd => exact leadW_keep γ id _ _ _ rfl rfl
  | readPend => exact leadW_keep γ id _ _ _ rfl rfl
  | readArrive => exact leadW_keep γ id _ _ _ rfl rfl
  | readRelease => exact leadW_keep γ id _ _ _ rfl rfl
  | readSingle m s =>
    exact leadW_keep γ id _ _ _ (preadRespondAll_lead_term id _ _).1
      (preadRespondAll_lead_term id _ _).2
  | readReleaseSingle s =>
    exact leadW_keep γ id _ _ _ (preadRespondAll_lead_term id _ _).1
      (preadRespondAll_lead_term id _ _).2
  | readAck m s =>
    exact leadW_keep γ id _ _ _ (preadRespondAll_lead_term id _ _).1
      (preadRespondAll_lead_term id _ _).2
  | readState => exact leadW_keep γ id _ _ _ rfl rfl
  | sendFree => exact leadW_keep γ id _ _ _ rfl rfl
  | abandon => exact leadW_zero γ id _ _ _ (Or.inl rfl)
  | zeroAck => exact leadW_keep γ id _ _ _ rfl rfl
  | reMatch => exact leadW_keep γ id _ _ _ rfl rfl
  | stepDown => exact leadW_zero γ id _ _ _ (Or.inl rfl)

end ghost

end EtcdGrove
end Perennial
