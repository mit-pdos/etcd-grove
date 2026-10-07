/-
Port of election_proof/proof_Entry__Size.v.
-/
import EtcdGrove.Raft.Spec.Entry__Size

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

/-- Trust boundary: an `axiom` rather than a `sorry`, so that it still counts as an
assumption under `#print axioms`. See the spec file for why it may be assumed. -/
axiom raftpb.Entry.Size.wp_proof : raftpb.Entry.Size.spec (GF := GF) (hG := hG)


end proof

end EtcdGrove
end Perennial
