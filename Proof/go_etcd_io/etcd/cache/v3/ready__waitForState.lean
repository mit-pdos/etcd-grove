/-
Proof of `Spec/ready__waitForState.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ready__waitForState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem ready.waitForState.wp_proof : ready.waitForState.spec (GF := GF) (hG := hG) := by
  intro r γ e0 ctx s pred P
  wp_start as ⟨#Hr, #Hlb, #Hctx, #Hpred⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave HI : (∃ e1 : Nat, readyEpochLb γ e1 ∗ ⌜e0 ≤ e1⌝ : IProp GF) $$ []
  · iexists e0; iframe #; ipureintro; exact Nat.le_refl _
  unfold context.isContext context.isContextDef
  iNamed Hctx
  wp_for HI
  icases HI with ⟨#Hlb1, %Hle1⟩
  unfold isReady
  wp_apply sync.Mutex.wp_Lock $$ [$Hr] as ⟨Hlocked, Hinv⟩
  unfold readyLockInv
  iNamed Hinv
  unfold readyEpochLb
  ihave %Hle := monoNatLbOwn_valid $$ Hauth Hlb1
  ihave #Hlbe := monoNatLbOwn_get $$ Hauth
  unfold readyPredSpec
  wp_apply Hpred $$ %b [$HisReady] as HisReady
  cases hP : P b
  · -- not yet: wait for the next change or for the context
    wp_auto
    ihave #Hunk := ownBroadcastChan_Unknown $$ Hch
    wp_apply sync.Mutex.wp_Unlock $$ [$Hr $Hlocked HisReady HstateCh Hch Hauth]
    · inext; iexists b, ch, γch, e; simp only [named]; iframe; ipureintro; exact Hb
    wp_apply HDone as %ch1 %γ1 #Hdone
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-stateChCopy`: the epoch moved on; loop
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hunk
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hunk
      iintro ⟨#HQ, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists e + 1
      iframe HQ
      ipureintro; omega
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-ctx.Done()`: return `ctx.Err()`, non-nil
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone
      iintro ⟨#HP, #Hc⟩
      wp_auto
      ihave #HErrD := HErr $$ %Broadcast.Done
      wp_apply HErrD $$ [] as %err %herr
      · iexact Hc
      wp_for_post
      iapply HΦ
      unfold readyWaitResult
      iright
      iframe #
      ipureintro; exact herr
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- seen: return `ctx.Err()`
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hr $Hlocked HisReady HstateCh Hch Hauth]
    · inext; iexists b, ch, γch, e; simp only [named]; iframe; ipureintro; exact Hb
    ihave #HErrU := HErr $$ %Broadcast.Unknown
    wp_apply HErrU as %err Herr
    wp_for_post
    iapply HΦ
    unfold readyWaitResult
    by_cases herr : err = GoInterface.nil
    · ileft
      isplitr
      · ipureintro; exact herr
      iexists b
      unfold readySeen readyEpochLb
      isplitr
      · iexists e; iframe Hlbe; ipureintro; exact ⟨Nat.le_trans Hle1 Hle.2, Hb.symm⟩
      · ipureintro; exact hP
    · iright
      simp only [herr, ↓reduceIte]
      icases Herr with ⟨#HP, #Hc⟩
      iframe #
      ipureintro; exact herr

end proof

end EtcdGrove
end Perennial
