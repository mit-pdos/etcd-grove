/-
Port of `election_proof/proof_big_NewInt.v`.
-/
import EtcdGrove.Raft.Spec.big_NewInt

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

/-- Proved in Perennial (`Perennial.Proof.math.big`). -/
theorem big.NewInt.wp_proof : big.NewInt.spec (GF := GF) (hG := hG) := by
  intro x
  iintro %Φ _ HΦ
  iapply _root_.Perennial.math.big.wp_NewInt x $$ [] HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
