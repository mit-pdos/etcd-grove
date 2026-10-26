/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__Add.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__Add
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.client_go.util.workqueue.queue__Push
public import Spec.k8s_io.client_go.util.workqueue.queue__Touch
public import Spec.k8s_io.client_go.util.workqueue.noMetrics__add
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.client_go.util.workqueue.Lemmas

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

theorem Typed.Add.wp_proof
    (wp_Has : sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Insert : sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_Push : queue.Push.spec (GF := GF) (hG := hG))
    (wp_Touch : queue.Touch.spec (GF := GF) (hG := hG))
    (wp_add : noMetrics.add.spec (GF := GF) (hG := hG)) :
    Typed.Add.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ k
  wp_start as #Hq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  wp_auto
  cases hsd : σ.shuttingDown
  · wp_auto
    wp_apply (sets.Set.wp_ptr_Has_of wp_Has) $$ [$Hdirty $Hdirty_i] as ⟨-, Hdirty_i⟩
    cases hd : (σ.dirty !! k).isSome
    · -- not dirty: dirty, then queued unless being processed
      wp_auto
      wp_apply wp_add
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply (sets.Set.wp_ptr_Insert_of wp_Insert) $$ [$Hdirty $Hdirty_i $Hl1] as ⟨-, Hdirty_i, -⟩
      wp_apply (sets.Set.wp_ptr_Has_of wp_Has) $$ [$Hproc $Hproc_i] as ⟨-, Hproc_i⟩
      simp only [sets.insertAll_cons, sets.insertAll_nil]
      cases hp : (σ.processing !! k).isSome
      · -- queued
        wp_auto
        wp_apply wp_Push $$ [$Hfifo_i] as Hfifo_i
        wp_apply sync.Cond.wp_Signal $$ [$Hcv]
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
        · inext; iunfold qLockInv
          iexists ({ σ with dirty := <[k := sets.present]> σ.dirty, queue := σ.queue ++ [k] } : QState K), drain
          simp only [hsd]; iframe; ipureintro; exact σ.wf_add_queue k Hwf_i hd hp
        iapply HΦ; itrivial
      · -- being processed: `Done` queues it
        wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
        · inext; iunfold qLockInv
          iexists ({ σ with dirty := <[k := sets.present]> σ.dirty } : QState K), drain
          simp only [hsd]; iframe; ipureintro; exact σ.wf_add_dirty k Hwf_i hp
        iapply HΦ; itrivial
    · -- already dirty: nothing changes (`Touch` if not being processed)
      wp_auto
      wp_apply (sets.Set.wp_ptr_Has_of wp_Has) $$ [$Hproc $Hproc_i] as ⟨-, Hproc_i⟩
      cases hp : (σ.processing !! k).isSome
      · wp_auto
        wp_apply wp_Touch
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
        · inext; iunfold qLockInv; iexists σ, drain; rw [hsd]; iframe; ipureintro; exact Hwf_i
        iapply HΦ; itrivial
      · wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
        · inext; iunfold qLockInv; iexists σ, drain; rw [hsd]; iframe; ipureintro; exact Hwf_i
        iapply HΦ; itrivial
  · -- shutting down: nothing changes
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
    · inext; iunfold qLockInv; iexists σ, drain; rw [hsd]; iframe; ipureintro; exact Hwf_i
    iapply HΦ; itrivial

end proof

end workqueue
end EtcdGrove
end Perennial
