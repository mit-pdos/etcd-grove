/-
Port of election_proof/proof_confchange_Restore.v.
-/
import EtcdGrove.Raft.Spec.confchange_Restore

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
axiom confchange.Restore.wp_proof : confchange.Restore.spec (GF := GF) (hG := hG)


end proof

end EtcdGrove
end Perennial
