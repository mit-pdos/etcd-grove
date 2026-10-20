/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__witnessDeliver.lean`. Lean-first
(2026-10-20, witness support).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__witnessDeliver

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- `r.witness == nil`: the early return. -/
theorem KV.witnessDeliver.wp_proof : KV.witnessDeliver.spec (GF := GF) (hG := hG) := by
  intro r ms
  wp_start as #Hw
  wp_auto
  iapply HΦ; itrivial

end proof

end kv
end EtcdGrove
end Perennial
