/-
The proof of `fixTrailer` (`Net/Spec/net/http/fixTrailer.lean`): no `Trailer`.
-/
module

public import Net.Spec.net.http.fixTrailer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem fixTrailer.wp_proof : fixTrailer.spec (GF := GF) (hG := hG) := by
  intro h chunked maxH
  wp_start as Hm
  wp_auto
  wp_apply (wp_map_lookup2 (V := GoSlice) go.string (go.SliceType go.string) h _ go!"Trailer" _) $$ Hm
    as Hm
  iapply HΦ
  iexact Hm

end proof

end net.http
end Perennial
