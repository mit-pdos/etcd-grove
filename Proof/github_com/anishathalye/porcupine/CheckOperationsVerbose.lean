/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/CheckOperationsVerbose.lean`: `checkOperations(model, history, true, timeout)`.
-/
module

public import Spec.github_com.anishathalye.porcupine.CheckOperationsVerbose
public import Spec.github_com.anishathalye.porcupine.checkOperations

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem CheckOperationsVerbose.wp_proof
    (wp_checkOperations : checkOperations.spec (GF := GF) (hG := hG)) :
    CheckOperationsVerbose.spec (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq dur Hops
  wp_start as ⟨#Hcci, #Hm, Hsl, #Hio⟩
  wp_auto
  wp_apply wp_checkOperations σ S m sl ops dq true dur Hops $$ [$Hsl] as %r %info %Hr
  · iframe #
  iapply HΦ
  ipureintro
  exact Hr

end proof

end porcupine
end EtcdGrove
end Perennial
