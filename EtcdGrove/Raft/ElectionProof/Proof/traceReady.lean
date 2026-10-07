/-
Port of `election_proof/proof_traceReady.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.Spec.traceReady

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

theorem traceReady.wp_proof : traceReady.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as -
  iapply HΦ
  ipureintro
  trivial

end proof

end EtcdGrove
end Perennial
