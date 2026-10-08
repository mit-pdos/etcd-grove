/-
Port of election_proof/proof_Entry__Size.v (an `Axiom` there; proved here since
2026-10-08 from the translated body).
-/
import EtcdGrove.Raft.Spec.Entry__Size
import EtcdGrove.Raft.Spec.raftpb_sovRaft

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.Entry.Size.wp_proof
    (wp_sovRaft : raftpb.sovRaft.spec (GF := GF) (hG := hG)) :
    raftpb.Entry.Size.spec (GF := GF) (hG := hG) := by
  intro e dq ev
  wp_start as He
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ He
  wp_auto
  wp_if_destruct
  · wp_end
  iStructNamed He
  wp_auto
  wp_apply wp_sovRaft with %n1 _
  wp_apply wp_sovRaft with %n2 _
  wp_apply wp_sovRaft with %n3 _
  -- `Data` nil or not; either way the four fields go back into `e ↦{dq} ev`
  wp_if_destruct
  · ihave He : e ↦{dq} ev $$ [Term Index Type' Data]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    wp_end
  wp_apply wp_sovRaft with %n4 _
  ihave He : e ↦{dq} ev $$ [Term Index Type' Data]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  wp_end

end proof

end EtcdGrove
end Perennial
