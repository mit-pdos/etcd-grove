/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__Done.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__Done
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len
public import Spec.k8s_io.client_go.util.workqueue.queue__Push
public import Spec.k8s_io.client_go.util.workqueue.noMetrics__done
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

theorem Typed.Done.wp_proof
    (wp_Has : sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Delete : sets.Set.Delete.spec (GF := GF) (hG := hG))
    (wp_Len : sets.Set.Len.spec (GF := GF) (hG := hG))
    (wp_Push : queue.Push.spec (GF := GF) (hG := hG))
    (wp_done : noMetrics.done.spec (GF := GF) (hG := hG)) :
    Typed.Done.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ k
  wp_start as ⟨#Hq, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  iunfold keyTok at Htok
  ihave %Hpk := ghost_map_lookup $$ Hauth_i Htok
  imod ghost_map_delete $$ Hauth_i Htok with Hauth_i
  have Hp : (σ.processing !! k).isSome = true := by
    show (σ.processing.lookup k).isSome = true; rw [Hpk]; rfl
  (try wp_auto)
  wp_apply wp_done
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply (sets.Set.wp_ptr_Delete_of wp_Delete) $$ [$Hproc $Hproc_i $Hl1] as ⟨-, Hproc_i, -⟩
  simp only [sets.deleteAll_cons, sets.deleteAll_nil]
  wp_apply (sets.Set.wp_ptr_Has_of wp_Has) $$ [$Hdirty $Hdirty_i] as ⟨-, Hdirty_i⟩
  cases hd : (σ.dirty !! k).isSome
  · -- not added meanwhile
    wp_auto
    wp_apply (sets.Set.wp_ptr_Len_of (T := T) wp_Len) $$ [$Hproc $Hproc_i] as ⟨-, Hproc_i⟩
    have Hwf' := σ.done_wf k Hwf_i Hp
    rw [QState.done_eq, if_neg (by simp [hd])] at Hwf'
    wp_if_destruct
    · wp_apply sync.Cond.wp_Signal $$ [$Hcv]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
      · inext; iunfold qLockInv
        iexists ({ σ with processing := GMap.delete k σ.processing } : QState K), drain
        iframe; ipureintro; exact Hwf'
      iapply HΦ; itrivial
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
      · inext; iunfold qLockInv
        iexists ({ σ with processing := GMap.delete k σ.processing } : QState K), drain
        iframe; ipureintro; exact Hwf'
      iapply HΦ; itrivial
  · -- added meanwhile: queued again
    wp_auto
    wp_apply wp_Push $$ [$Hfifo_i] as Hfifo_i
    wp_apply sync.Cond.wp_Signal $$ [$Hcv]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
    · have Hwf' := σ.done_wf k Hwf_i Hp
      rw [QState.done_eq, if_pos hd] at Hwf'
      inext; iunfold qLockInv
      iexists ({ σ with processing := GMap.delete k σ.processing, queue := σ.queue ++ [k] } : QState K), drain
      iframe; ipureintro; exact Hwf'
    iapply HΦ; itrivial

end proof

end workqueue
end EtcdGrove
end Perennial
