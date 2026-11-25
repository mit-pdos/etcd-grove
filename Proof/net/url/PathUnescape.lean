/-
The proof of `PathUnescape.spec` (`Spec/net/url/PathUnescape.lean`).
-/
module

public import Spec.net.url.PathUnescape
public import Spec.net.url.unescape

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

theorem PathUnescape.wp_proof (wp_unescape : unescape.spec (GF := GF) (hG := hG)) :
    PathUnescape.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_unescape s mPathSegment (by decide)
  iapply HΦ
  itrivial

end proof

end net.url
end Perennial
