/-
Port of `election_proof/proof_strings_Join.v`.
-/
import EtcdGrove.Raft.Spec.strings_Join

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

/-- Not translated; see the comment at the spec. -/
axiom strings.Join.wp_proof : strings.Join.spec (GF := GF) (hG := hG)


end proof

end EtcdGrove
end Perennial
