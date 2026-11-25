/-
The proof of `http.NewServeMux` (`Net/Spec/net/http/NewServeMux.lean`): `&ServeMux{}`.
-/
module

public import Net.Spec.net.http.NewServeMux

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

theorem NewServeMux.wp_proof : NewServeMux.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  iassumption

end proof

end net.http
end Perennial
