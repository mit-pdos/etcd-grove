/-
Port of election_proof/proof_traceBecomeLeader.v.
-/
import EtcdGrove.Raft.Spec.traceBecomeLeader

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

theorem traceBecomeLeader.wp_proof : traceBecomeLeader.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
