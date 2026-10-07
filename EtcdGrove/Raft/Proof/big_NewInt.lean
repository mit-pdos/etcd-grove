/-
Port of `election_proof/proof_big_NewInt.v`.
-/
import EtcdGrove.Raft.Spec.big_NewInt

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

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an
assumption, not unfinished work. `math/big` is not translated and is not raft; see the spec. -/
axiom big.NewInt.wp_proof : big.NewInt.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
