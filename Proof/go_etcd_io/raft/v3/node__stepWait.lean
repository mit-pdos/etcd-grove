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

/-- `stepWithWaitOption(ctx, m, true)`, for `Propose`'s message. (Raft v3.7, stage R5: the
message `msgIn ml 1` with its entry `propEntryM data`. Stage R7a: any `nodeCtx`, the error
`propErr`.) -/
theorem node.stepWait.wp_proof
    (wp_node_stepWithWaitOption : node.stepWithWaitOption.spec (GF := GF) (hG := hG)) :
    node.stepWait.spec (GF := GF) (hG := hG) := by
  intro γ id n ml data ctx cd
  wp_start as ⟨#Hnode, #Hctx, Harg⟩
  wp_auto
  wp_apply wp_node_stepWithWaitOption γ id n ml true ctx cd $$ [Harg]
  · iframe Hnode Hctx
    unfold stepArg
    icases Harg with (⟨Hm, #Hent⟩ | Hfwd)
    · iright
      ileft
      isplitr
      · ipureintro; rfl
      iexists data
      iframe Hm Hent
    · -- (etcd-io/raft#44) `ProposeConfChange`'s
      iright; iright; iright
      isplitr
      · ipureintro; rfl
      iexact Hfwd
  iintro %err #Herr
  wp_auto
  iapply HΦ
  simp only [↓reduceIte]
  iexact Herr

end proof

end EtcdGrove
end Perennial
