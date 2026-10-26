/-
Proof of `Spec/k8s_io/client_go/util/workqueue/Typed__Get.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.Typed__Get
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete
public import Spec.k8s_io.client_go.util.workqueue.queue__Len
public import Spec.k8s_io.client_go.util.workqueue.queue__Pop
public import Spec.k8s_io.client_go.util.workqueue.noMetrics__get
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

theorem Typed.Get.wp_proof
    (wp_Insert : sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_Delete : sets.Set.Delete.spec (GF := GF) (hG := hG))
    (wp_Len : queue.Len.spec (GF := GF) (hG := hG))
    (wp_Pop : queue.Pop.spec (GF := GF) (hG := hG))
    (wp_get : noMetrics.get.spec (GF := GF) (hG := hG)) :
    Typed.Get.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as #Hq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iNamed Hq
  ihave #HL := isCond_L _ _ $$ Hcv
  ihave #Hlocker := sync.Mutex_is_Locker L.mu (qLockInv (K := K) q L γ) $$ Hsync Hmu
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  (try wp_auto)
  ihave HI : (sync.ownMutex L.mu ∗ qLockInv (K := K) q L γ : IProp GF) $$ [Hlocked HI]
  · iframe
  wp_for HI
  icases HI with ⟨Hlocked, HI⟩
  iNamedSuffix HI "_i"
  ihave %Hql := ownFifo_length_lt _ _ $$ Hfifo_i
  wp_apply wp_Len $$ [$Hfifo_i] as Hfifo_i
  rcases hq : σ.queue with _ | ⟨k, rest⟩
  · -- the FIFO is empty
    rw [hq] at Hql
    simp only [List.length_nil]
    wp_auto
    cases hsd : σ.shuttingDown
    · -- not shutting down: wait
      simp only [Bool.not_false, decide_true, ↓reduceIte]
      wp_auto
      wp_apply sync.Cond.wp_Wait L.cond (interface.mk (go.GoType.PointerType sync.Mutex.ty) #L.mu)
          (iprop(sync.ownMutex L.mu ∗ qLockInv (K := K) q L γ))
        $$ [Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i] as HI
      · isplitr
        · iexact Hcv
        isplitr
        · iexact Hlocker
        iframe; iunfold qLockInv; iexists σ, drain; rw [hq, hsd]; iframe; ipureintro; exact Hwf_i
      wp_for_post
      iframe
    · -- shutting down and drained
      simp only [Bool.not_true, ↓reduceIte, val_false_ne_true, decide_false, _root_.decide_true,
        Bool.false_eq_true]
      wp_auto
      wp_apply wp_Len $$ [$Hfifo_i] as Hfifo_i
      simp only [List.length_nil]
      wp_auto
      wp_alloc_anon
      wp_auto
      simp only [sdGhost, ↓reduceIte]
      icases Hsdg_i with #Hsdlb
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i]
      · inext; iunfold qLockInv; iexists σ, drain; rw [hq, hsd]
        simp only [sdGhost, ↓reduceIte]
        iframe; iframe #; ipureintro; exact Hwf_i
      iapply HΦ
      simp only [↓reduceIte]
      iframe #
  · -- the FIFO is not empty: the loop ends
    rw [hq] at Hql
    have Hql' : rest.length + 1 < 2 ^ 63 := by simpa using Hql
    wp_if_destruct
    · exfalso; simp only [List.length_cons] at Hif
      have : ((rest.length + 1 : Nat) : Int) < 2 ^ 63 := by omega
      have h0 : (0 : Int) ≤ ((rest.length + 1 : Nat) : Int) := by omega
      have := congrArg (fun w : w64 => sint.Z w) Hif
      rw [show sint.Z (W64 ((rest.length + 1 : Nat) : Int)) = ((rest.length + 1 : Nat) : Int) by word] at this
      simp at this; omega
    try simp only [val_false_ne_true, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    wp_apply wp_Len $$ [$Hfifo_i] as Hfifo_i
    wp_if_destruct
    · contradiction
    wp_apply wp_Pop $$ [$Hfifo_i] as Hfifo_i
    wp_apply wp_get
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Insert_of wp_Insert) $$ [$Hproc $Hproc_i $Hl1] as ⟨-, Hproc_i, -⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l2 ⟨Hl2, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Delete_of wp_Delete) $$ [$Hdirty $Hdirty_i $Hl2] as ⟨-, Hdirty_i, -⟩
    simp only [sets.insertAll_cons, sets.insertAll_nil, sets.deleteAll_cons, sets.deleteAll_nil]
    have Hnp := σ.front_not_processing k rest Hwf_i hq
    imod ghost_map_insert (γ := γ.proc) k sets.present Hnp $$ Hauth_i with ⟨Hauth_i, Htok⟩
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfifo_i Hdirty_i Hproc_i Hsd_i Hdrain_i Hauth_i Hsdg_i]
    · inext; iunfold qLockInv; iexists σ.get k rest, drain
      simp only [QState.get]; iframe; ipureintro; exact σ.get_wf k rest Hwf_i hq
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold keyTok; iexact Htok

end proof

end workqueue
end EtcdGrove
end Perennial
