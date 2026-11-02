/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/CheckOperationsTimeout.lean`:
`checkOperations(model, Linearizability, history, false, timeout)`, with `Linearizability` read from the
package fact (`linInit`).
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.CheckOperationsTimeout
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.checkOperations

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
  intro σ S m sl ops dq dur Hops Hcl
  wp_start as ⟨#Hcci, #Hm, Hsl, #Hio⟩
  have Hacc : isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ⊢
      linInit (GF := GF) :=
    isPkgInit_access (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine
  ihave #HI := Hacc $$ Hpkg
  iunfold linInit at HI
  icases HI with ⟨%c, #Hlin, #Hc⟩
  wp_auto
  wp_apply wp_checkOperations σ S m c sl ops dq false dur Hops Hcl $$ [$Hsl]
    as %r %info ⟨%Hr, Hsl⟩
  · iframe #
  iapply HΦ
  iframe Hsl
  ipureintro
  exact Hr

end proof

end porcupine
end EtcdGrove
end Perennial
