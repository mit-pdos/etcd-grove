/- Lean-first (no Rocq counterpart).

`newclientOperation(op, numClients, id)`: a composite literal.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newclientOperation

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

theorem newclientOperation.wp_proof : newclientOperation.spec (GF := GF) (hG := hG) :=
    fun op nc id => by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end porcupine
end EtcdGrove
end Perennial
