/- Port of election_proof/proof_payloadSize.v. -/
module

public import Spec.go_etcd_io.raft.v3.payloadSize

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

theorem payloadSize.wp_proof : payloadSize.spec (GF := GF) (hG := hG) := by
  intro e
  wp_start as _
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
