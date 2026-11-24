/-
The proof of `Marshal` (`Spec/encoding/json/Codec/Marshal.lean`): `marshalAny`'s result.
-/
module

public import Spec.encoding.json.Codec.Marshal
public import Spec.encoding.json.Codec.marshalAny

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

theorem Marshal.wp_proof (wp_marshalAny : marshalAny.spec (GF := GF) (hG := hG)) :
    Marshal.spec (GF := GF) (hG := hG) := by
  intro J F v Ψ
  wp_start as ⟨Hvia, Henc⟩
  wp_auto
  wp_apply wp_marshalAny $$ [$Hpkg $Hvia $Henc] as %s %err Hret
  iapply HΦ $$ Hret

end proof

end encoding.json
end Perennial
