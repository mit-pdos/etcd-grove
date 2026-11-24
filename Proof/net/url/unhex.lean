/-
The proof of `unhex.spec` (`Spec/net/url/unhex.lean`).
-/
module

public import Spec.net.url.unhex

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.url

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]

theorem unhex.wp_proof : unhex.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  wp_auto
  unfold unhexF
  iapply HΦ
  itrivial

end proof

end net.url
end Perennial
