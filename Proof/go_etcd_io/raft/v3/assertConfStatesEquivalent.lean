/- Port of election_proof/proof_assertConfStatesEquivalent.v. -/
module

public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__Equivalent

@[expose] public section

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
  intro l cs1 cs2 v1 v2 l1 l2 dq1 dq2 dl1 dl2 Hperm Hlen Hlperm Hllen H1 H3 H4 H6 Hal
  wp_start as ⟨H1, H2, Hl1, Hl2⟩
  wp_auto
  wp_apply wp_ConfState_Equivalent _ _ _ _ _ _ _ _ _ _ _ Hperm Hlen Hlperm Hllen H1 H3 H4 H6 Hal
    $$ [$cs1 $H1 $H2 $Hl1 $Hl2] as ⟨-, H1, H2, Hl1, Hl2⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
