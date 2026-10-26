/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__ShutDown.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__ShutDown

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem Typed.ShutDown.wp_proof : Typed.ShutDown.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as ⟨#Hq, Hst⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  ipersist q
  wp_apply sync.Once.wp_Do $$ [$Honce]
  · iintro !> %Φ' HP HΦ'
    wp_apply wp_with_defer as %defer2 defer2
    (try wp_auto)
    wp_apply wp_broadcast_chan_close $$ [$HP] as -
    · imodintro; itrivial
    iapply HΦ'; itrivial
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  (try wp_auto)
  -- the flag's ghost state becomes `true` (persistently)
  ihave Hsdg : |==> shutdownLb γ $$ [Hsdg_i]
  · unfold sdGhost
    cases σ.shuttingDown
    · simp only [Bool.false_eq_true, ↓reduceIte]
      imod dghostVar_update true γ.sd false $$ Hsdg_i with H
      iunfold shutdownLb
      iapply dghostVar_persist $$ H
    · simp only [↓reduceIte]; imodintro; iexact Hsdg_i
  imod Hsdg with #Hsdlb
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i]
  · inext; iunfold qLockInv
    iexists ({ σ with shuttingDown := true } : QState K), false
    simp only [sdGhost, ↓reduceIte]
    iframe; iframe #; ipureintro; exact Hwf_i
  wp_apply wp_wgWait $$ [$Hst] as Hst
  · iframe #
  iapply HΦ
  iframe; iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
