/-
Proof of `Spec/watcher__Compact.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.watcher__Compact

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

theorem watcher.Compact.wp_proof : watcher.Compact.spec (GF := GF) (hG := hG) := by
  intro w γ pred Pb sent ph compactRev
  wp_start as ⟨#Hw, Hph, #HcP⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, ⟨%eCP, #HeCP, #HeCPs⟩⟩
  unfold isWatcher
  iNamed Hw
  wp_auto
  ihave %Hhnn := typedPointsto_not_null $$ «$v0»
  iStructNamed «$v0»
  ipersist Revision
  unfold errorStringSpec
  wp_apply HeCPs as %reason
  iclear HeCPs
  ipersist «$r0»
  ipersist resp
  ipersist w
  -- the cancel response is what `cancelAt _ (some compactRev)` says
  ihave #Hcancel : cancelAt «$r0_ptr» (some compactRev) $$ []
  · unfold cancelAt respSent respAt eventsAt hdrAt
    iexists _
    iframe «$r0»
    isplitl
    · isplitl
      · iexists []
        isplitl
        · iapply ownSlice_nil
        isplitl
        · ipureintro; rfl
        imodintro
        iintro %i %ev %e %Hev
        simp at Hev
      isplitl
      · iright
        isplitl
        · ipureintro; exact Hhnn
        dsimp only [cancelModel]
        rw [show (zero_val go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader).Revision' = W64 0 from rfl]
        iexact Revision
      ipureintro
      exact ⟨rfl, rfl, rfl⟩
    ipureintro; exact Hhnn
  wp_func_lits
  cases ph with
  | opened =>
    simp only [watcherAt, WatcherPhase.cancelAfter]
    unfold watcherClosePub
    wp_apply Once.wp_Do_frame (watcherStopOnceAddr w) (watcherOnceP (hG := hG) w γ)
      iprop(∃ sc c, watcherClosed γ sc c) (watcherOpen γ sent)
      (watcherClosed γ sent (some compactRev)) _ $$ [$Honce $Hph] as ⟨#HQ, HR⟩
    · unfold onceFrameSpec
      wp_start as ⟨HP, Hopen⟩
      unfold watcherOnceP
      icases HP with ⟨Hcr, Htok⟩
      wp_auto
      ipersist Hcr
      wp_apply_core chan.wp_close (V := go_etcd_io.etcd.client.v3.WatchResponse) ch γ.ch $$ HisCh
      iintro -
      iapply watcher_close_au w γ Pb sent (some compactRev) «$r0_ptr» _ $$ Hinv Hopen Htok Hcr
        Hcancel HcP [HΦ]
      iintro #Hcl
      wp_auto
      iapply HΦ
      iframe #
    icases HR with (HR | HR)
    · iapply HΦ; iexact HR
    · iexfalso
      icases HQ with ⟨%sc, %c, #HQ⟩
      iapply watcherOpen_closed_false $$ [$HR $HQ]
  | closed c =>
    simp only [watcherAt, WatcherPhase.cancelAfter]
    ihave #Hcl := Hph
    wp_apply Once.wp_Do_frame (watcherStopOnceAddr w) (watcherOnceP (hG := hG) w γ)
      iprop(∃ sc c, watcherClosed γ sc c) emp emp _ $$ [$Honce] as -
    · -- the closure cannot run: the right to close is gone
      isplitr
      · iempintro
      unfold onceFrameSpec
      wp_start as ⟨HP, -⟩
      unfold watcherOnceP
      icases HP with ⟨-, Htok⟩
      wp_auto_lc 1
      imod watcher_tok_closed_false w γ Pb sent c $$ [$Hinv $Hcl $Htok $Hlc1] with HF
      iexfalso; iexact HF
    iapply HΦ
    iexact Hcl

end proof

end EtcdGrove
end Perennial
