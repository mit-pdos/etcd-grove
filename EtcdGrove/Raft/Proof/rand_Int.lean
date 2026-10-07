/-
Port of `election_proof/proof_rand_Int.v`.
-/
import EtcdGrove.Raft.Spec.rand_Int

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Trust boundary**: an `axiom` rather than a `sorry` (Rocq: an `Axiom` inside the
functor rather than an `Admitted` `Lemma`), so that it still counts as an assumption
under `#print axioms` (Rocq `Print Assumptions`) and in `etc/tcb-report.py`. This is
the RNG, which notes/STATUS.md ("Trust base") lists as assumable; see
`Spec/rand_Int.lean` for what exactly is claimed and why. -/
axiom rand.Int.wp_proof : rand.Int.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
