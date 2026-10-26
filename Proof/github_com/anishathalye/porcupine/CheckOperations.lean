/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/CheckOperations.lean`: `checkOperations(model, history, false, 0)`.
-/
module

public import Spec.github_com.anishathalye.porcupine.CheckOperations
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

theorem CheckOperations.wp_proof
    (wp_checkOperations : checkOperations.spec (GF := GF) (hG := hG)) :
    CheckOperations.spec (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq Hops
  wp_start as ⟨#Hcci, #Hm, Hsl, #Hio⟩
  wp_auto
  wp_apply wp_checkOperations σ S m sl ops dq false (W64 0) Hops $$ [$Hsl] as %r %info %Hr
  · iframe #
  iapply HΦ
  ipureintro
  intro Hlin
  have := (Hr Hlin).2 (by decide)
  subst this
  simp

end proof

end porcupine
end EtcdGrove
end Perennial
