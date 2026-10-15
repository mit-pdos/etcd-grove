/- Port of election_proof/proof_payloadSize.v. -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.payloadSize
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData

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

theorem payloadSize.wp_proof
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG)) :
    payloadSize.spec (GF := GF) (hG := hG) := by
  intro p dq e
  wp_start as He
  wp_auto
  wp_apply wp_Entry_GetData.1 p dq e $$ [$He] as He
  iapply HΦ $$ He

end proof

end EtcdGrove
end Perennial
