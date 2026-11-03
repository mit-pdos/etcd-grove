/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/CheckOperationsTimeout.lean`: `checkOperations(model, history, false, timeout)`.
-/
module

public import Spec.github_com.anishathalye.porcupine.CheckOperationsTimeout
public import Spec.github_com.anishathalye.porcupine.checkOperations

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem CheckOperationsTimeout.wp_proof
    (wp_checkOperations : checkOperations.spec (GF := GF) (hG := hG)) :
    CheckOperationsTimeout.spec (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq dur
  wp_start as ⟨#Hcci, #Hm, Hsl, #Hio, %Hops⟩
  wp_auto
  wp_apply wp_checkOperations σ S m sl ops dq false dur $$ [$Hsl] as %r %info %Hr
  · iframe #; ipureintro; exact Hops
  iapply HΦ
  ipureintro
  exact Hr

end proof

end porcupine
end EtcdGrove
end Perennial
