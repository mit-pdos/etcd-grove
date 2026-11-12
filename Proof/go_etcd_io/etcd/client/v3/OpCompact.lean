/-
Proof of `Spec/OpCompact.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.OpCompact
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

theorem OpCompact.wp_proof
    (wp_applyCompactOpts : CompactOp.applyCompactOpts.spec (GF := GF) (hG := hG)) :
    OpCompact.spec (GF := GF) (hG := hG) := by
  intro rev
  wp_start as ⟨⟩
  wp_auto
  wp_apply wp_applyCompactOpts ret_ptr _ $$ [$ret] as Hret
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
