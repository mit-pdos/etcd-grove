/-
The proof of `fixPragmaCacheControl` (`Net/Spec/net/http/fixPragmaCacheControl.lean`): no `Pragma`.
-/
module

public import Net.Spec.net.http.fixPragmaCacheControl

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

theorem fixPragmaCacheControl.wp_proof : fixPragmaCacheControl.spec (GF := GF) (hG := hG) := by
  intro h ms
  wp_start as ⟨Hm, %Hk⟩
  wp_auto
  wp_apply (wp_map_lookup2 (V := GoSlice) go.string (go.SliceType go.string) h _ go!"Pragma" _) $$ Hm
    as Hm
  rw [Hk]
  try wp_auto
  iapply HΦ
  iexact Hm

end proof

end net.http
end Perennial
