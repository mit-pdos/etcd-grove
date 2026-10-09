/-
Proof of `Spec/notifier__wait.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.notifier__wait

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem notifier.wait.wp_proof : notifier.wait.spec (GF := GF) (hG := hG) := by
  intro n γ k0 ctx s
  wp_start as ⟨Hh, #Hlb, #Hctx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold context.isContext context.isContextDef
  iNamed Hctx
  unfold notifierHandle
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hh] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  unfold notifierLockInv
  iNamed HP
  unfold notifierLb
  ihave %Hle := monoNatLbOwn_valid $$ Hauth Hlb
  ihave #Hlbk := monoNatLbOwn_get $$ Hauth
  ihave #Hunk := ownBroadcastChan_close c.ch c.γch _ Broadcast.Unknown c.γi $$ [Hbc]
  · iframe #
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hcur Hch Hauth Hpend] as Hh
  · inext
    iexists c
    simp only [named]
    iframe
    iframe #
  wp_apply HDone as %ch1 %γ1 #Hdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-ch`: a `notify` closed it; return `nil`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, c.ch, c.γch
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hunk
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hunk
    iintro ⟨#HQ, -⟩
    wp_auto
    iapply HΦ
    iframe
    unfold notifierWaitResult notifierLb
    ileft
    isplitr
    · ipureintro; rfl
    iapply monoNatLbOwn_le (k0 + 1) (by omega) $$ HQ
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
    iapply HΦ
    iframe
    unfold notifierWaitResult
    iright
    iframe #
    ipureintro; exact herr
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
