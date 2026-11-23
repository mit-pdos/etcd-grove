/-
The proof of `connReader.releaseConn` (`Net/Spec/net/http/connReader__releaseConn.lean`): under the
mutex the phase is the main one (the main thread's half of `γ.ph`), so the main thread owns the
reader's `conn`, which it sets to `nil`.
-/
module

public import Net.Spec.net.http.connReader__releaseConn
public import Net.Proof.net.http.ConnReaderLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

theorem connReader.releaseConn.wp_proof : connReader.releaseConn.spec (GF := GF) (hG := hG) := by
  intro cr γ cn P hs Z
  wp_start as ⟨#Hcr, Hleft⟩
  iunfold crLeft at Hleft
  icases Hleft with ⟨Hph, Hr, %c, %hb, %ab, %fl, Hc, Hhb, Hir, Hab, Hfl, Hbuf⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv, #Hcond⟩, Hinv⟩
  iunfold crPh at Hinv
  icases Hinv with ⟨%ph, Hph2, Hinv⟩
  ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
  subst Hag
  wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Hinv]
  · iunfold crPh
    iexists false
    iframe Hph2 Hinv
  iapply HΦ
  iunfold crLeft
  iframe Hph Hr
  iexists null, hb, ab, fl
  iframe Hc Hhb Hir Hab Hfl Hbuf

end proof

end net.http
end Perennial
