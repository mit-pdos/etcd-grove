/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__stepWait
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
variable [AllG GF]

/-- `stepWithWaitOption(ctx, m, true)`, for `Propose`'s message. -/
theorem node.stepWait.wp_proof
    (wp_node_stepWithWaitOption : node.stepWithWaitOption.spec (GF := GF) (hG := hG)) :
    node.stepWait.spec (GF := GF) (hG := hG) := by
  intro γ id n data_sl esl data
  wp_start as ⟨#Hnode, Hes, Hcap, #Hdata, #Hent⟩
  wp_auto
  wp_apply wp_node_stepWithWaitOption γ id n (propMsg esl) true $$ [Hes Hcap]
  · iframe Hnode
    unfold stepArg
    iright
    ileft
    isplitr
    · ipureintro; rfl
    iexists data_sl, esl, data
    iframe Hes Hcap Hdata Hent
    ipureintro; rfl
  iintro %err -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
