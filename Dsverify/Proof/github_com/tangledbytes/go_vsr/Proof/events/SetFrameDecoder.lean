/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/events/SetFrameDecoder.lean (lab master
915f964; notes/dsv-vr.md): over any `GF`, on the net extension; the hook's lock is the hub's
`hookLockInvFull` (`hookKnownFull`, `Spec/events.lean`).
-/
/-
`events.SetFrameDecoder(f)` (D11): under the hook's lock, store `f` if the hook is unset; either
way the hook is set for good (`frameDecoderSet`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

theorem events.SetFrameDecoder.wp' : events.SetFrameDecoder.spec (GF := GF) (hG := hG) := by
  intro f Hnn
  wp_start as ⟨#Hk, #Hf⟩
  unfold events.hookKnownFull events.hookState
  icases Hk with ⟨%γh, %mu, #Hmu, #Hlock⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock mu (events.hookLockInvFull γh) $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold events.hookLockInvFull at Hinv
  icases Hinv with ⟨%g, Hg, (⟨%Hnil, Ha⟩ | ⟨%Hgn, #Hdec, Ha⟩)⟩
  · subst Hnil
    wp_auto
    iapply wp_fupd
    imod monoListAuthOwn_update [()] List.nil_prefix $$ Ha with ⟨Ha, #Hlb⟩
    wp_apply sync.Mutex.wp_Unlock mu (events.hookLockInvFull γh) $$ [$Hlock $Hown Hg Ha]
    · inext
      iunfold events.hookLockInvFull
      iexists f
      iframe
      iright
      iframe
      isplitr
      · ipureintro; exact Hnn
      · iexact Hf
    imodintro
    iapply HΦ
    unfold events.frameDecoderSet events.hookState
    iexists γh
    iframe Hlb
    iexists mu
    iframe Hmu Hlock
  · wp_auto
    rw [decide_eq_false Hgn]
    wp_auto
    ihave #Hlb := monoListLbOwn_get γh 1 _ $$ Ha
    wp_apply sync.Mutex.wp_Unlock mu (events.hookLockInvFull γh) $$ [$Hlock $Hown Hg Ha]
    · inext
      iunfold events.hookLockInvFull
      iexists g
      iframe
      iright
      iframe
      isplitr
      · ipureintro; exact Hgn
      · iexact Hdec
    iapply HΦ
    unfold events.frameDecoderSet events.hookState
    iexists γh
    iframe Hlb
    iexists mu
    iframe Hmu Hlock

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
