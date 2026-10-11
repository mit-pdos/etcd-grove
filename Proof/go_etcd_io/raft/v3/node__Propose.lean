/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.node__stepWait

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

/-- The one-entry batch `[]pb.Entry{{Data: data}}`, then `stepWait`. -/
theorem node.Propose.wp_proof
    (wp_node_stepWait : node.stepWait.spec (GF := GF) (hG := hG)) :
    node.Propose.spec (GF := GF) (hG := hG) := by
  intro γ id n data_sl data Q fresh
  wp_start as ⟨#Hnode, #Hdata, Harg⟩
  wp_auto_lc 1
  -- the proposal's ghost work (2026-10-10): the slice recorded, the update deposited
  imod node_propose_ghost γ id n data_sl data Q fresh ⊤ CoPset.subseteq_top
    CoPset.subseteq_top $$ Hnode Hdata Hlc1 Harg with ⟨#Hent, Hres⟩
  wp_apply wp_slice_literal (l := [propEntry data_sl])
  isplitr
  · ipureintro; rfl
  iintro %esl ⟨Hes, Hcap⟩
  wp_auto
  have Hm : ∀ s : GoSlice, raftpb.Message.mk (W32 2) 0 0 0 0 0 s 0 0 Loc.null false 0
      slice.nil slice.nil = propMsg s := fun _ => rfl
  rw [Hm]
  wp_apply wp_node_stepWait γ id n data_sl _ data $$ [$Hnode $Hes $Hcap $Hdata $Hent]
  iintro %err -
  wp_auto
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
