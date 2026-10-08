/-
Port of election_proof/proof_traceCommit.v.
-/
import EtcdGrove.Raft.Spec.traceCommit

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

theorem traceCommit.wp_proof : traceCommit.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start
  wp_end

end proof

end EtcdGrove
end Perennial
