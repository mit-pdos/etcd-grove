/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__step
public import Spec.go_etcd_io.raft.v3.node__stepWithWaitOption

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

/-- `stepWithWaitOption(ctx, m, false)`: `m` is not a proposal (`NetMsgOk`). (Raft v3.7, stage
R5: `stepP` passed on whole, `stepArg`'s network branch being `netP` alone.) -/
theorem node.step.wp_proof
    (wp_node_stepWithWaitOption : node.stepWithWaitOption.spec (GF := GF) (hG := hG)) :
    node.step.spec (GF := GF) (hG := hG) := by
  intro γ id n m
  wp_start as ⟨#Hnode, Hstep⟩
  unfold stepP
  icases Hstep with (Hnet | Hfwd)
  rotate_left
  · -- a forwarded proposal (2026-10-10)
    wp_auto
    wp_apply wp_node_stepWithWaitOption γ id n m false $$ [Hfwd]
    · iframe Hnode
      unfold stepArg
      iright; iright
      iframe Hfwd
      ipureintro; rfl
    iintro %err -
    wp_auto
    iapply HΦ
    itrivial
  wp_auto
  wp_apply wp_node_stepWithWaitOption γ id n m false $$ [Hnet]
  · iframe Hnode
    unfold stepArg
    ileft
    iexact Hnet
  iintro %err -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
