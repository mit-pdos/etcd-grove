/-
Proof of `Spec/CompactOp__applyCompactOpts.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.CompactOp__applyCompactOpts

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

theorem CompactOp.applyCompactOpts.wp_proof :
    CompactOp.applyCompactOpts.spec (GF := GF) (hG := hG) := by
  intro p op
  wp_start as Hp
  wp_auto
  wp_for
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
