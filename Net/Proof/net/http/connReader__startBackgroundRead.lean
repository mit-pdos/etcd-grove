/-
The proof of `connReader.startBackgroundRead` (`Net/Spec/net/http/connReader__startBackgroundRead.lean`):
under the mutex the phase is the main one (the main thread's half of `γ.ph`), so the invariant holds
the background reader's token; `inRead` set, the deadline cleared (`deadline_au`), `backgroundRead`
forked with the token, the buffer and the reader's token, and the fields put in the invariant in the
background phase.
-/
module

public import Net.Spec.net.http.connReader__startBackgroundRead
public import Net.Spec.net.http.connReader__backgroundRead
public import Net.Spec.net.Conn__SetReadDeadline
public import Net.Proof.net.http.ConnReaderLemmas
public import GooseLang.Ext.Net.Proto

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
variable [π : NetProtoGS] [net.Assumptions] [field_sem : net.FieldAssumptions]

theorem connReader.startBackgroundRead.wp_proof
    (wp_SetReadDeadline : net.Conn.SetReadDeadline.spec (GF := GF) (hG := hG))
    (wp_backgroundRead : connReader.backgroundRead.spec (GF := GF) (hG := hG)) :
    connReader.startBackgroundRead.spec (GF := GF) (hG := hG) := by
  intro cr γ t cn a la ra P hs Z c ab fl arr
  wp_start as ⟨#Hcr, #Hlaw, #Henv, #Hrwc, #Hca, #Hcis, Hph, Hr, Hc, Hhb, Hir, Hab, Hfl, #Hcok,
    Hbuf, Hrecv⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv, #Hcond⟩, Hinv⟩
  iunfold crPh at Hinv
  icases Hinv with ⟨%ph, Hph2, Hinv⟩
  ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
  subst Hag
  simp only [Bool.false_eq_true, ite_false]
  wp_apply wp_SetReadDeadline t cn true a la ra _ (fun _ => iprop(True)) $$ [$Hca]
    as %err0 -
  · imod deadline_au (Gg := hG.goose_globalGS) cn true (W64 1) _ $$ Hcis with ⟨%st, Hend, Hcl⟩
    imodintro
    iexists st
    iframe Hend
    iintro %res %st' %Hd Hend
    imod Hcl $$ %res %st' %Hd Hend with -
    imodintro; itrivial
  wp_apply wp_fork $$ [Hinv Hbuf Hrecv]
  · wp_apply wp_backgroundRead cr γ t cn a la ra P hs Z arr $$ [Hinv Hbuf Hrecv]
    · iframe Hcr Hlaw Henv Hrwc Hca Hinv Hbuf Hrecv
    itrivial
  imod ghostVar_update_halves true γ.ph _ _ $$ Hph Hph2 with ⟨Hph, Hph2⟩
  icases (ghostVar_split_half γ.r 1 hs).1 $$ Hr with ⟨Hr, Hr2⟩
  wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Hc Hhb Hir Hab Hfl Hr2]
  · iunfold crPh
    iexists true
    simp only [ite_true]
    iframe Hph2
    iunfold crBg
    iexists c, false, true, ab, fl
    iframe Hc Hhb Hir Hab Hfl Hr2 Hcok
    simp only [ite_true]
    ipureintro; trivial
  iapply HΦ
  iframe Hph Hr

end proof

end net.http
end Perennial
