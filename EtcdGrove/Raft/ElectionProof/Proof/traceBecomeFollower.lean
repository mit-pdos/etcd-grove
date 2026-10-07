/-
Port of `election_proof/proof_traceBecomeFollower.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.traceBecomeFollower

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

theorem traceBecomeFollower.wp_proof : traceBecomeFollower.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start
  wp_end

end proof

end EtcdGrove
end Perennial
