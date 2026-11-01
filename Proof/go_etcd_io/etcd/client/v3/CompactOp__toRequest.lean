/-
Proof of `Spec/CompactOp__toRequest.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.CompactOp__toRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem CompactOp.toRequest.wp_proof : CompactOp.toRequest.spec (GF := GF) (hG := hG) := by
  intro op
  wp_start as ⟨⟩
  wp_auto
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
