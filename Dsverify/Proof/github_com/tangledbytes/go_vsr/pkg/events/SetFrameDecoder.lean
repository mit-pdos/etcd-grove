/-
`events.SetFrameDecoder(kitFrameDecoder)` (the lab's `Proof/events/SetFrameDecoder.lean`, D11;
notes/dsv-vr.md): under the hook's lock (`hookKnownFull`, events' package fact) it stores
`decodeFrame` if the hook is unset; either way the hook is set for good (`frameDecoderSet`). What
`vsrwire`'s `init` calls (its generated `Init.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Init
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.tangledbytes.go_vsr.pkg.events

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tangledbytes.go_vsr.pkg.events.Assumptions]

set_option goose.wp.extras true

/-- `decodeFrame` is a function, not `nil`. -/
theorem kitFrameDecoder_ne_nil [examples.vsrwire.Assumptions] : kitFrameDecoder ≠ func.nil := by
  intro h
  have e := (FuncUnfold.func_unfold (f := examples.vsrwire.decodeFrame) (type_args := []))
  unfold kitFrameDecoder at h
  rw [h, go.intoVal_unfold GoFunc] at e
  simp [func.nil, examples.vsrwire.decodeFrame.impl] at e

theorem wp_SetFrameDecoder [examples.vsrwire.Assumptions] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events }}
      (App (Val (@! SetFrameDecoder)) (Val #kitFrameDecoder))
    {{ RET #(); frameDecoderSet }} := by
  wp_start
  ihave #Hk : (hookKnownFull : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold hookKnownFull at Hk
  icases Hk with ⟨%γh, #Hk⟩
  iunfold hookState at Hk
  icases Hk with ⟨%mu, #Hmu, #Hlock⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock mu (hookLockInvFull (GF := GF) γh) $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold hookLockInvFull at Hinv
  icases Hinv with ⟨%g, Hg, (⟨%Hnil, Ha⟩ | ⟨%Hgn, Ha⟩)⟩
  · subst Hnil
    wp_auto
    iapply wp_fupd
    imod monoListAuthOwn_update [()] List.nil_prefix $$ Ha with ⟨Ha, #Hlb⟩
    wp_apply sync.Mutex.wp_Unlock mu (hookLockInvFull (GF := GF) γh) $$ [$Hlock $Hown Hg Ha]
    · inext
      iunfold hookLockInvFull
      iexists kitFrameDecoder
      iframe
      iright
      iframe
      ipureintro; rfl
    imodintro
    iapply HΦ
    unfold frameDecoderSet hookState
    iexists γh
    iframe Hlb
    iexists mu
    iframe Hmu Hlock
  · subst Hgn
    wp_auto
    rw [decide_eq_false kitFrameDecoder_ne_nil]
    wp_auto
    ihave #Hlb := monoListLbOwn_get γh 1 _ $$ Ha
    wp_apply sync.Mutex.wp_Unlock mu (hookLockInvFull (GF := GF) γh) $$ [$Hlock $Hown Hg Ha]
    · inext
      iunfold hookLockInvFull
      iexists kitFrameDecoder
      iframe
      iright
      iframe
      ipureintro; rfl
    iapply HΦ
    unfold frameDecoderSet hookState
    iexists γh
    iframe Hlb
    iexists mu
    iframe Hmu Hlock

end proof

end github_com.tangledbytes.go_vsr.pkg.events
end Perennial
