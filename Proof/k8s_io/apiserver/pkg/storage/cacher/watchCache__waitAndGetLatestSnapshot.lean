/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/watchCache__waitAndGetLatestSnapshot.lean`. Lean-first (no Rocq counterpart).
The read lock (the reader's token), the wait (`waitUntilFreshLocked`), and, without an error,
the latest snapshot (`getLatestSnapshotLocked`) and the cache's version, which is its state's; the
deferred `RUnlock` gives the token back.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__waitAndGetLatestSnapshot
public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__waitUntilFreshLocked
public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__getLatestSnapshotLocked
public import Spec.k8s_io.component_base.tracing.SpanFromContext
public import Spec.k8s_io.component_base.tracing.Span__AddEvent

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable [store_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]

theorem watchCache.waitAndGetLatestSnapshot.wp_proof
    (wp_wait : watchCache.waitUntilFreshLocked.spec (GF := GF) (hG := hG))
    (wp_latest : watchCache.getLatestSnapshotLocked.spec (GF := GF) (hG := hG))
    (wp_SpanFromContext : tracing.SpanFromContext.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG)) :
    watchCache.waitAndGetLatestSnapshot.spec (GF := GF) (hG := hG) := by
  intro wc γ Ψ ctx minRV mv
  wp_start as ⟨#Hwc, Htok⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_SpanFromContext ctx) $$ [] as %sp %Hsp
  (try wp_auto)
  rw [watchCache.TypeAssumptions.ptr_RLock_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_RLock (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ)) $$ [Htok] as ⟨Hrl, HP⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply (wp_AddEvent sp _ _) $$ []
  · iframe #; ipureintro; exact Hsp
  (try wp_auto)
  wp_apply (wp_wait wc γ Ψ ctx minRV) $$ [Hrl HP] as %err ⟨Hrl, %st, Hl, %Hfresh⟩
  · iframe #; iframe
  (try wp_auto)
  cases err with
  | ok ei =>
    -- the wait's error
    (try wp_auto)
    rw [watchCache.TypeAssumptions.ptr_RUnlock_unfold.method_unfold]
    wp_pures
    (try wp_auto)
    wp_apply (sync.RWMutex.wp_RUnlock (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ)) $$ [Hrl Hl] as Htok
    · iframe #; iframe Hrl; inext; iunfold wcLockP; iexists st; iframe
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iintro %h
    exfalso; simp_all
  | nil =>
  (try wp_auto)
  wp_apply (wp_AddEvent sp _ _) $$ []
  · iframe #; ipureintro; exact Hsp
  (try wp_auto)
  wp_apply (wp_latest wc γ Ψ ctx mv sync.rfrac st) $$ [Hl] as %p ⟨Hl, #Hsn, #HΨ⟩
  · iframe #; iframe
  iunfold wcLockPSt at Hl
  icases Hl with ⟨Hrv, Hown⟩
  (try wp_auto)
  rw [watchCache.TypeAssumptions.ptr_RUnlock_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_RUnlock (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ)) $$ [Hrl Hrv Hown] as Htok
  · iframe #; iframe Hrl; inext; iunfold wcLockP; iexists st; unfold wcLockPSt; iframe
  (try wp_auto)
  iapply HΦ
  iframe Htok
  iintro -
  iexists p, st
  iframe Hsn HΨ
  ipureintro
  refine ⟨rfl, rfl, ?_⟩
  simp_all

end proof

end cacher
end EtcdGrove
end Perennial
