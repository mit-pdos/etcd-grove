/- Lean-first (no Rocq counterpart).

`(*client).unlift(top, serialized)` (dag.go, PR #46): the panic test (never taken: the ids are
equal), `head--`, then `serialized.clear(top.opId)`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.client__unlift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.bitset__clear

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem client.unlift.wp_proof (wp_clear : bitset.clear.spec (GF := GF) (hG := hG)) :
    client.unlift.spec (GF := GF) (hG := hG) := fun cp cv top lin_ptr lsl ws hid hop hlen => by
  wp_start as ⟨Hc, Hlin, Hws⟩
  wp_auto
  rw [hid]
  simp only [_root_.decide_true, Bool.not_true]
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"clear")]
  wp_call
  wp_auto
  wp_apply wp_clear lsl ws _ (by simpa using hlen) $$ [Hws] as Hws
  · iframe
  iapply HΦ
  iframe

end proof

end porcupine
end EtcdGrove
end Perennial
