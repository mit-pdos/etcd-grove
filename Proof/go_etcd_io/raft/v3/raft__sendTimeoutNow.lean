/- Port of election_proof/proof_raft__sendTimeoutNow.v.

raft v3.7 (stage R4): the message `&pb.Message{To: new(to), Type: pb.MsgTimeoutNow.Enum()}` is
built owned (`msgOwn_lit0`, `LemmasSendR.lean`) and handed to `send`. -/
module

public import Spec.go_etcd_io.raft.v3.raft__sendTimeoutNow
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Proof.go_etcd_io.raft.v3.TracedUntraced

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.sendTimeoutNow.wp_proof
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.sendTimeoutNow.spec (GF := GF) (hG := hG) := by
  intro c r id s to Q Hto Htz Htr
  wp_start as ⟨Hphys, Hgate⟩
  wp_auto
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 14)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v0» with #cTo
  wp_auto
  imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 14, to, 0, 0, 0, 0, 0, 0, false, 0⟩ ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy cTo
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    msg_nulls
  have Hok : SendOk id s ⟨W32 14, to, 0, 0, 0, 0, 0, 0, false, 0⟩ [] [] [] :=
    Or.inr (Or.inr (Or.inl (Or.inr ⟨Or.inl rfl, fun _ => Htz, rfl, rfl, rfl, Hto, rfl,
      fun h => absurd h (by simp [MsgTransferLeader])⟩)))
  -- (Q8 stage 1, slice 5) `send` at the caller's gate: `MsgTimeoutNow` is not traced
  wp_apply wp_raft_send c r id s «$a0_ptr» _ [] none [] [] [] Q (Or.inl rfl) Hok
    (fun h => absurd h (by simp [MsgSnap]))
      (fun h => absurd h (by simp [MsgApp])) rfl (fun h => absurd Htr h)
      $$ [$Hphys $Hm Hgate] as ⟨Hphys, HQ⟩
  · isplitr
    · iapply tsSrc_ne; exact (fun h => absurd h (by simp [MsgSnap]))
    simp only
    rw [show sendOutGate id s c (W32 14) [] = none from rfl]
    iexact Hgate
  ihave Hphys := ownRaftPhysC_unsend c r id s $$ Hphys
  iapply HΦ
  iframe Hphys HQ

end proof

end EtcdGrove
end Perennial
