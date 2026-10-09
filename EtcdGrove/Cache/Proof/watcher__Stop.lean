/-
Proof of `Spec/watcher__Stop.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.watcher__Stop

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

theorem watcher.Stop.wp_proof : watcher.Stop.spec (GF := GF) (hG := hG) := by
  intro w γ pred sent ph
  wp_start as ⟨#Hw, Hph⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isWatcher
  iNamed Hw
  wp_auto
  ipersist w
  wp_func_lits
  cases ph with
  | opened =>
    simp only [watcherAt, WatcherPhase.cancelAfter]
    wp_apply Once.wp_Do_frame (watcherStopOnceAddr w) (watcherOnceP (hG := hG) w γ)
      iprop(∃ sc c, watcherClosed γ sc c) (watcherOpen γ sent) (watcherClosed γ sent none) _
      $$ [$Honce $Hph] as ⟨#HQ, HR⟩
    · unfold onceFrameSpec
      wp_start as ⟨HP, Hopen⟩
      unfold watcherOnceP
      icases HP with ⟨Hcr, Htok⟩
      ipersist Hcr
      wp_auto
      wp_apply_core chan.wp_close (V := go_etcd_io.etcd.client.v3.WatchResponse) ch γ.ch $$ HisCh
      iintro -
      iapply watcher_close_au w γ sent none null _ $$ Hinv Hopen Htok Hcr [] [HΦ]
      · unfold cancelAt; ipureintro; rfl
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
      imod watcher_tok_closed_false w γ sent c $$ [$Hinv $Hcl $Htok $Hlc1] with HF
      iexfalso; iexact HF
    iapply HΦ
    iexact Hcl

end proof

end EtcdGrove
end Perennial
