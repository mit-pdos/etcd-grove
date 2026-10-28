/-
Proof of `Spec/k8s_io/client_go/tools/cache/handleWatch.lean`, over `handleAnyWatch`'s named
hypothesis (gap D4). Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.handleWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem handleWatch.wp_proof (wp_handleAnyWatch : handleAnyWatch.spec (GF := GF) (hG := hG)) :
    handleWatch.spec (GF := GF) (hG := hG) := by
  intro ctx dch γd start w γa γw r bm inits f γ OK et name tname cb clk errCh n p L C
  wp_start as ⟨#Hctx, #Hw, Hcons, HL, #Hf, #Hty, #Herr, #Hstep, #Hcb⟩
  wp_auto
  wp_apply (wp_handleAnyWatch ctx dch γd start w γa γw r bm inits f γ OK et name tname cb clk
    errCh n p L C) $$ [$Hctx $Hw $Hcons $HL $Hf $Hty $Herr $Hstep $Hcb] as %b %err Hpost
  (try wp_auto)
  iapply HΦ
  iexact Hpost

end proof

end cache
end EtcdGrove
end Perennial
