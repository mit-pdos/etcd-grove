/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__ShutDownWithDrain.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__ShutDownWithDrain
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem Typed.ShutDownWithDrain.wp_proof
    (wp_Len : sets.Set.Len.spec (GF := GF) (hG := hG)) :
    Typed.ShutDownWithDrain.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as ⟨#Hq, Hst⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  ihave #Hlocker := sync.Mutex_is_Locker L.mu (qLockInv (K := K) q L γ) $$ Hsync Hmu
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
  imod sdGhost_shut $$ Hsdg_i with #Hsdlb
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
  ihave HI : (sync.ownMutex L.mu ∗ qLockInv (K := K) q L γ : IProp GF)
    $$ [Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i]
  · iframe; iunfold qLockInv
    iexists ({ σ with shuttingDown := true } : QState K), true
    iframe
    isplitr
    · iapply sdGhost_true $$ Hsdlb
    ipureintro; exact Hwf_i
  wp_for HI
  icases HI with ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  wp_apply (sets.Set.wp_ptr_Len_of (T := T) wp_Len) $$ [$Hproc $Hproc_i] as ⟨-, Hproc_i⟩
  wp_if_destruct
  · -- nothing is being processed: done
    try simp only [val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
    · inext; iunfold qLockInv; iexists σ, drain; iframe; ipureintro; exact Hwf_i
    wp_apply wp_wgWait $$ [$Hst] as Hst
    · iframe #
    iapply HΦ
    iframe; iframe #
  · cases drain
    · -- `drain` cleared by a `ShutDown`: done
      simp only [val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
      · inext; iunfold qLockInv; iexists σ, false; iframe; ipureintro; exact Hwf_i
      wp_apply wp_wgWait $$ [$Hst] as Hst
      · iframe #
      iapply HΦ
      iframe; iframe #
    · -- wait
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      wp_apply sync.Cond.wp_Wait L.cond (interface.mk (go.GoType.PointerType sync.Mutex.ty) #L.mu)
          (iprop(sync.ownMutex L.mu ∗ qLockInv (K := K) q L γ))
        $$ [Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i] as HI
      · isplitr
        · iexact Hcv
        isplitr
        · iexact Hlocker
        iframe; iunfold qLockInv; iexists σ, true; iframe; ipureintro; exact Hwf_i
      wp_for_post
      iframe

end proof

end workqueue
end EtcdGrove
end Perennial
