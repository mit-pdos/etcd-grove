/-
Proof of `Spec/go_etcd_io/raft/v3/witness__handleHeartbeat.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__handleHeartbeat
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasSendR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The message's cells fresh, its context the request's (shared, read-only). -/
theorem witness.handleHeartbeat.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    witness.handleHeartbeat.spec (GF := GF) (hG := hG) := by
  intro w id mv μ term
  wp_start as ⟨#Hid, #Hm⟩
  iunfold ownWMsg at Hm
  icases Hm with ⟨%s0, %s1, %Hmv, #Hs0, #Hs1, #Hvot, #Hctx⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  wp_auto
  rw [show raftpb.MsgHeartbeatResp = #((W32 9 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 9) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cTe
  imod cellRO_alloc $$ «$v2» with #cFr
  imod cellRO_alloc $$ «$v3» with #cTo
  wp_alloc ml as Hml
  imod msgOwn_lit ml _ (wHeartbeat id term μ).1 μ.ctx ⊤ $$ [Hml] with Hmsg
  · simp only [wHeartbeat, respM, show MsgHeartbeatResp = W32 9 from rfl, ← Hfr]
    iframe Hml Hctx cTy cTo cFr cTe
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    msg_nulls
  wp_auto
  rw [show (wHeartbeat id term μ).2 = μ.ctx from rfl]
  iapply HΦ
  iframe Hmsg

end proof

end EtcdGrove
end Perennial
