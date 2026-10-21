/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/witnessRead__GetState.lean`. Lean-first (2026-10-20,
witness support).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.witnessRead__GetState

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

theorem witnessRead.GetState.wp_proof : witnessRead.GetState.spec (GF := GF) (hG := hG) := by
  intro r s P p σ
  wp_start as #Hr
  iunfold isWRead at Hr
  icases Hr with ⟨#Hrs, #Hrst, -, -⟩
  wp_auto
  iapply HΦ; itrivial

end proof

end kv
end EtcdGrove
end Perennial
