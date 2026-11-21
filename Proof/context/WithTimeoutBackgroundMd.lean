/-
`context.WithTimeout(context.Background(), d)` with its outgoing metadata
(`Spec/context/WithTimeoutBackgroundMd.lean`; the auth-mode merge's 5b, 2026-10-29): proved (errdesc
stage 2b, 2026-11-21) from Perennial's `wp_WithTimeout_Background`, whose context's values are
`Background()`'s (`ctxValueFrom`), and the chain laws `metadata.outMD_bgFrom` (stage 1) and
`context.libCtxOk_bgFrom`. Until then a trust-boundary axiom.
-/
module

public import Spec.context.WithTimeoutBackgroundMd
public import Perennial.Proof.context.Results
public import Proof.context.LibKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.WithTimeoutBackgroundMd.wp_proof :
    context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG) := by
  intro d
  iintro %Φ ⟨#Hpkg, -⟩ HΦ
  wp_apply (_root_.Perennial.context.wp_WithTimeout_Background d) $$ []
    as %ctx' %γ' %cancel %dl ⟨#Hcancel, #Hctx, #Hfrom⟩
  ihave #Hmd := metadata.outMD_bgFrom ctx' $$ Hfrom
  ihave #Hlib := context.libCtxOk_bgFrom ctx' $$ [Hpkg Hfrom]
  · iframe #
  ihave #Hoc := metadata.outgoingCtxOkC_of_outMD ctx' none $$ Hmd
  iapply HΦ
  iframe #

end proof

end EtcdGrove
end Perennial
