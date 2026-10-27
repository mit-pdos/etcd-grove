/- Lean-first (no Rocq counterpart).

`insertBefore(n, mark)`: two stores when `mark` is not `nil` (its `prev` is `nil`, so the
third is skipped).
-/
module

public import Spec.github_com.anishathalye.porcupine.insertBefore

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

theorem insertBefore.wp_proof : insertBefore.spec (GF := GF) (hG := hG) :=
    fun n vn mark vm => by
  wp_start as ⟨Hn, (%Hnil | ⟨Hm, %Hprev⟩)⟩
  · subst Hnil
    wp_auto
    iapply HΦ
    ileft
    iframe
    ipureintro; rfl
  · ihave %Hmnn := typedPointsto_not_null $$ Hm
    wp_func_call
    wp_call
    wp_auto
    simp only [Hmnn, _root_.decide_false, Bool.not_false]
    wp_auto
    rw [Hprev]
    wp_auto
    iapply HΦ
    iright
    iframe

end proof

end porcupine
end EtcdGrove
end Perennial
