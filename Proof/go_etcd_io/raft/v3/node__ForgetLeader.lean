/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
public import Spec.go_etcd_io.raft.v3.node__step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `step` of the literal message, a local one (`netP_local`). (Raft v3.7, stage R5: the message
is `&pb.Message{Type: pb.MsgForgetLeader.Enum()}`, built into `msgIn` by
`msgIn_of_scalar_struct`; `MsgForgetLeader.Enum()` is a new callee.) -/
theorem node.ForgetLeader.wp_proof
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ForgetLeader.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as #Hnode
  wp_auto
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod rdCred_zero_upd (GF := GF) γ.raft with Hcr
  imod tickCred_zero (GF := GF) γ.bud with Htc
  rw [show raftpb.MsgForgetLeader = #((W32 23 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 23)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_auto
  imod msgIn_of_scalar_struct «$a1_ptr» pty null null null null null null null null null
      { (zero_val MessageM) with Type' := W32 23 } ⊤ $$ [«$a1»] with Hmsg
  · iframe «$a1» cTy
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_node_step γ id n _ $$ [Hmsg Hcr Htc]
  · iframe Hnode
    unfold stepP
    ileft
    iapply netP_local γ id _ _ (.inr (.inl rfl)) rfl rfl rfl $$ Hmsg Hlb Hcr Htc
  iintro %err -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
