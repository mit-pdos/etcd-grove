/-
Port of `election_proof/proof_rand_Int.v`.
-/
module

public import Spec.crypto.rand.Int

@[expose] public section

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

/-- Perennial's `crypto.rand.wp_Int`, proved from its model of `Int`
(`Perennial/TrustedCode/crypto/rand.lean`). -/
theorem rand.Int.wp_proof : rand.Int.spec (GF := GF) (hG := hG) :=
  fun rdr max mz Hmz => crypto.rand.wp_Int rdr max mz Hmz

end proof

end EtcdGrove
end Perennial
