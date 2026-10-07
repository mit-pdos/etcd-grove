/-
Port of `election_proof/proof_slices_Sort.v`.
-/
import EtcdGrove.Raft.Spec.slices_Sort

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

/-- Trust boundary: an `axiom` rather than a `sorry`d theorem, so that it still counts
as an assumption under `#print axioms` and under the greps in notes/STATUS.md. See
that file for why it may be assumed. -/
axiom slices.«Sort».wp_proof : slices.«Sort».spec (GF := GF) (hG := hG)


end proof

end EtcdGrove
end Perennial
