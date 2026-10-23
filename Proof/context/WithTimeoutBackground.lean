/-
`context.WithTimeout(context.Background(), d)`: proved from Perennial's `wp_WithTimeout_Background`
(`Perennial/Proof/context/WithDeadlineBackground.lean`, the pin since 2026-10-23;
`notes/client-timeouts-plan.md` T3). Until then the trust boundary: an axiom, Perennial specifying
`WithDeadlineCause` for an `isContext` parent only, and `Background()` being none.
-/
module

public import Spec.context.WithTimeoutBackground
public import Perennial.Proof.context.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The spec's descriptor is Perennial's `bgDeadlineDesc` (no values, the deadline, Done
proposition `True`); its `isClosedchanInit` premise is unused (Perennial derives it from
`isPkgInit`). -/
theorem context.WithTimeoutBackground.wp_proof :
    context.WithTimeoutBackground.spec (GF := GF) (hG := hG) := by
  intro d
  iintro %Φ ⟨#Hpkg, -⟩ HΦ
  wp_apply (_root_.Perennial.context.wp_WithTimeout_Background d) $$ []
    as %ctx' %γ' %cancel %dl ⟨#Hcancel, #Hctx⟩
  iapply HΦ
  iframe #

end proof

end EtcdGrove
end Perennial
