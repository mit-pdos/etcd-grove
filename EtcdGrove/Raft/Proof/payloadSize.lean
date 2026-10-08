/- Port of election_proof/proof_payloadSize.v. -/
import EtcdGrove.Raft.Spec.payloadSize

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem payloadSize.wp_proof : payloadSize.spec (GF := GF) (hG := hG) := by
  intro e
  wp_start as _
  wp_alloc e_ptr as e; wp_pures; wp_load; wp_pures; iclear e
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
