/- Port of election_proof/proof_assertConfStatesEquivalent.v. -/
import EtcdGrove.Raft.Spec.assertConfStatesEquivalent
import EtcdGrove.Raft.Spec.ConfState__Equivalent

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

theorem assertConfStatesEquivalent.wp_proof
    (wp_ConfState_Equivalent : raftpb.ConfState.Equivalent.spec (GF := GF) (hG := hG)) :
    assertConfStatesEquivalent.spec (GF := GF) (hG := hG) := by
  intro l cs1 cs2 v1 v2 dq1 dq2 Hperm H1 H2 H3 H4 H5 H6 Hal
  wp_start as ⟨H1, H2⟩
  wp_auto
  wp_apply wp_ConfState_Equivalent _ _ _ _ _ _ _ Hperm H1 H2 H3 H4 H5 H6 Hal
    $$ [$cs1 $H1 $H2] as ⟨-, H1, H2⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
