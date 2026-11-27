/-
The proof of `connReader.abortPendingRead` (`Net/Spec/net/http/connReader__abortPendingRead.lean`):
under the mutex the phase is the background one (the main thread's half of `γ.ph`); while the read
runs the invariant is put back for `Cond.Wait`; once it is done (`inRead` false) the invariant holds
the background reader's token and its resources, which the main thread takes, putting the token
back in the main phase.
-/
module

public import Net.Spec.net.http.connReader__abortPendingRead
public import Net.Spec.net.Conn__SetReadDeadline
public import Net.Proof.net.http.ConnReaderLemmas
public import Perennial.Proof.sync.Results
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
variable [π : NetProtoGS] [net.Assumptions]

theorem val_false_ne_true : (#false : val) ≠ #true :=
  fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)

theorem connReader.abortPendingRead.wp_proof
    (wp_SetReadDeadline : net.Conn.SetReadDeadline.spec (GF := GF) (hG := hG)) :
    connReader.abortPendingRead.spec (GF := GF) (hG := hG) := by
  intro cr γ t cn a la ra P hs Z tm b
  wp_start as ⟨#Hcr, #Htm, #Hrwc, #Hca, Hrdl, Hph, Hr⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv, #Hcond⟩, Hinv⟩
  iunfold crPh at Hinv
  icases Hinv with ⟨%ph, Hph2, Hinv⟩
  ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
  subst Hag
  simp only [ite_true]
  iunfold crBg at Hinv
  icases Hinv with ⟨%c, %hb, %ir, %ab, Hc, Hhb, Hir, Hab, Hr2, #Hcok, Hrest⟩
  wp_auto
  cases ir
  · -- no read runs: return at once, the main phase back
    simp only [Bool.false_eq_true, ite_false]
    icases Hrest with ⟨Htok, Hrd⟩
    wp_auto
    imod ghostVar_update_halves false γ.ph _ _ $$ Hph Hph2 with ⟨Hph, Hph2⟩
    wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Htok]
    · iunfold crPh
      iexists false
      simp only [Bool.false_eq_true, ite_false]
      iframe Hph2 Htok
    iapply HΦ
    iframe Hph
    isplitl [Hr Hr2]
    · iapply (ghostVar_split_half γ.r 1 hs).2; iframe Hr Hr2
    iunfold crOwn
    iframe Hrdl
    iexists c, hb, ab
    iframe Hc Hhb Hir Hab Hcok Hrd
  -- the read runs: abort it
  simp only [ite_true]
  icases Hrest with %Hhb0
  wp_auto
  wp_apply wp_SetReadDeadline t cn true a la ra tm
      (fun _ => iprop(∃ b' : Bool, rdlTok (Gg := hG.goose_globalGS) cn true b')) $$ [$Hca Hrdl]
    as %err0 ⟨%res0, ⟨%b2, Hrdl⟩, -⟩
  · imod deadline_au (Gg := hG.goose_globalGS) cn true (W64 1) _ b $$ Hrdl with ⟨%st, Hend, Hcl⟩
    imodintro
    iexists st
    iframe Hend
    iintro %res %st' %Hd Hend
    imod Hcl $$ %res %st' %Hd Hend with ⟨-, Hrdl⟩
    imodintro; iexists _; iexact Hrdl
  ihave #Hcr' := Hcr
  iunfold crIs at Hcr'
  icases Hcr' with ⟨#Hsync, #Hmu⟩
  ihave #Hlocker := sync.Mutex_is_Locker (structFieldRef net.http.connReader go!"mu" cr)
    (crInv cr γ cn P hs Z) $$ Hsync Hmu
  ihave HI : (sync.ownMutex (structFieldRef net.http.connReader go!"mu" cr) ∗
      ghostVar γ.ph (1 : Qp).half true ∗ crBg cr γ cn P hs Z ∗
      ∃ b' : Bool, rdlTok (Gg := hG.goose_globalGS) cn true b' : IProp GF)
    $$ [Hown Hph2 Hc Hhb Hir Hab Hr2 Hrdl]
  · iframe Hown Hph2 Hrdl
    iunfold crBg
    iexists c, hb, true, true
    iframe Hc Hhb Hir Hab Hr2 Hcok
    simp only [ite_true]
    ipureintro; exact Hhb0
  wp_for HI
  icases HI with ⟨Hown, Hph2, HI, %b1, Hrdl⟩
  iunfold crBg at HI
  icases HI with ⟨%c', %hb', %ir', %ab', Hc, Hhb, Hir, Hab, Hr2, #Hcok', Hrest⟩
  wp_auto
  cases ir'
  · -- done: leave the loop
    simp only [Bool.false_eq_true, ite_false, val_false_ne_true, decide_false]
    icases Hrest with ⟨Htok, Hrd⟩
    simp only [_root_.decide_true, ite_true]
    wp_auto
    wp_apply wp_SetReadDeadline t cn true a la ra _
        (fun _ => iprop(∃ b' : Bool, rdlTok (Gg := hG.goose_globalGS) cn true b')) $$ [$Hca Hrdl]
      as %err1 ⟨%res1, ⟨%b3, Hrdl⟩, -⟩
    · imod deadline_au (Gg := hG.goose_globalGS) cn true (W64 1) _ b1 $$ Hrdl with ⟨%st, Hend, Hcl⟩
      imodintro
      iexists st
      iframe Hend
      iintro %res %st' %Hd Hend
      imod Hcl $$ %res %st' %Hd Hend with ⟨-, Hrdl⟩
      imodintro; iexists _; iexact Hrdl
    imod ghostVar_update_halves false γ.ph _ _ $$ Hph Hph2 with ⟨Hph, Hph2⟩
    wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Htok]
    · iunfold crPh
      iexists false
      simp only [Bool.false_eq_true, ite_false]
      iframe Hph2 Htok
    iapply HΦ
    iframe Hph
    isplitl [Hr Hr2]
    · iapply (ghostVar_split_half γ.r 1 hs).2; iframe Hr Hr2
    iunfold crOwn
    iframe Hrdl
    iexists c', hb', ab'
    iframe Hc Hhb Hir Hab Hcok' Hrd
  · simp only [ite_true, _root_.decide_true]
    ihave #Hcond' := Hcond
    iunfold crCond at Hcond'
    icases Hcond' with ⟨-, #Hcf, #Hcv⟩
    wp_auto
    wp_apply sync.Cond.wp_Wait cv (interface.mk (go.GoType.PointerType sync.Mutex.ty)
        #(structFieldRef net.http.connReader go!"mu" cr))
        (iprop(sync.ownMutex (structFieldRef net.http.connReader go!"mu" cr) ∗ crInv cr γ cn P hs Z))
      $$ [Hown Hph2 Hc Hhb Hir Hab Hr2 Hrest] as ⟨Hown, Hinv⟩
    · isplitr
      · iexact Hcv
      isplitr
      · iexact Hlocker
      iframe Hown
      iunfold crInv
      isplitr
      · iright; iexists cv; iexact Hcond
      iunfold crPh
      iexists true
      iframe Hph2
      simp only [ite_true]
      iunfold crBg
      iexists c', hb', true, ab'
      iframe Hc Hhb Hir Hab Hr2 Hcok'
      simp only [ite_true]
      iexact Hrest
    iunfold crInv at Hinv
    icases Hinv with ⟨-, Hinv⟩
    iunfold crPh at Hinv
    icases Hinv with ⟨%ph, Hph2, Hinv⟩
    ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
    subst Hag
    simp only [ite_true]
    wp_for_post
    iframe
    unfold named
    iframe

end proof

end net.http
end Perennial
