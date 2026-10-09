/-
Port of election_proof/proof_big_Int__Int64.v.
-/
module

public import Spec.math.big.Int__Int64

@[expose] public section

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
theorem big.Int.Int64.wp_proof : big.Int.Int64.spec (GF := GF) (hG := hG) := by
  intro p z Hz
  iintro %Φ ⟨_, Hp⟩ HΦ
  iapply _root_.Perennial.math.big.wp_Int64 p z Hz $$ Hp HΦ

end proof

end EtcdGrove
end Perennial
