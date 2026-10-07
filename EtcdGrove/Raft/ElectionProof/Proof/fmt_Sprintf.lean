/-
Port of election_proof/proof_fmt_Sprintf.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.fmt_Sprintf

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

/-- Not translated; see the comment at the spec. -/
axiom fmt.Sprintf.wp_proof : fmt.Sprintf.spec (GF := GF) (hG := hG)

#check @fmt.Sprintf.wp_proof

end proof

end EtcdGrove
end Perennial
