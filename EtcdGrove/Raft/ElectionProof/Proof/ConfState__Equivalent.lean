/-
Port of election_proof/proof_ConfState__Equivalent.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.ConfState__Equivalent

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
axiom raftpb.ConfState.Equivalent.wp_proof :
  raftpb.ConfState.Equivalent.spec (GF := GF) (hG := hG)


end proof

end EtcdGrove
end Perennial
