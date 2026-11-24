/-
The proof of `NewChunkedWriter` (`Net/Spec/net/http/internal/NewChunkedWriter.lean`): the
`*chunkedWriter` allocated with its `Wire`, returned with its points-to.
-/
module

public import Net.Spec.net.http.internal.NewChunkedWriter

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http.internal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.internal.Assumptions]

theorem NewChunkedWriter.wp_proof : NewChunkedWriter.spec (GF := GF) (hG := hG) := by
  intro wi
  wp_start as -
  wp_auto
  wp_apply (IntoValTyped.wp_alloc (V := net.http.internal.chunkedWriter)
    (t := net.http.internal.chunkedWriter.ty)) as %l Hl
  iapply HΦ
  iunfold chunkedW
  iexact Hl

end proof

end net.http.internal
end Perennial

