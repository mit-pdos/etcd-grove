/-
Port of election_proof/proof_big_Int__Int64.v.
-/
import EtcdGrove.Raft.Spec.big_Int__Int64

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

/-- **Trust boundary**: an `axiom` rather than a `sorry` (Rocq: an `Axiom` inside the
functor rather than an `Admitted` `Lemma`), so that it still counts as an assumption
under `#print axioms`. `math/big` is not translated and is not raft; see
`Spec/big_Int__Int64.lean` and notes/STATUS.md ("Trust base") for why it may be
assumed. -/
axiom big.Int.Int64.wp_proof : big.Int.Int64.spec (GF := GF) (hG := hG)


end proof

end EtcdGrove
end Perennial
