/-
Port of election_proof/proof_IsEmptySnap.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.IsEmptySnap

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

theorem IsEmptySnap.wp_proof : IsEmptySnap.spec (GF := GF) (hG := hG) := by
  intro sp
  wp_start as -
  wp_auto
  iapply HΦ
  ipureintro
  rfl

end proof

end EtcdGrove
end Perennial
