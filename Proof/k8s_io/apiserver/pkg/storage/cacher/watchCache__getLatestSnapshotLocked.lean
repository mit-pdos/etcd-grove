/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/watchCache__getLatestSnapshotLocked.lean`. Lean-first (no Rocq counterpart).
Non-recursive: the store's latest snapshot, loaded with the reader's part of the writer's
token as the view shift's resource (`wcsOwn γ q st`, which agrees with the published state,
`ghostVar_agree_keep`), so it is of `st`; then its version checked against the cache's.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__getLatestSnapshotLocked
public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__checkSnapshotResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.WatchCacheStorage__LatestSnapshot
public import Spec.k8s_io.component_base.tracing.SpanFromContext
public import Spec.k8s_io.component_base.tracing.Span__AddEvent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable [store_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]

theorem watchCache.getLatestSnapshotLocked.wp_proof
    (wp_check : watchCache.checkSnapshotResourceVersion.spec (GF := GF) (hG := hG))
    (wp_LatestSnapshot : WatchCacheStorage.LatestSnapshot.spec (GF := GF) (hG := hG))
    (wp_SpanFromContext : tracing.SpanFromContext.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG)) :
    watchCache.getLatestSnapshotLocked.spec (GF := GF) (hG := hG) := by
  intro wc γ Ψ ctx mv q st
  wp_start as ⟨#Hwc, Hl⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store $$ []
  · iPkgInit
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  unfold isWC
  icases Hwc with ⟨%s, %c, %cfg, #Hs, #Hwcs, #Hc, #Hcond, #Hcfg, #Hcfgok, #Hguard⟩
  unfold wcLockPSt
  icases Hl with ⟨Hrv, Hown⟩
  (try wp_auto)
  wp_apply (wp_SpanFromContext ctx) $$ [] as %sp %Hsp
  (try wp_auto)
  wp_apply (wp_LatestSnapshot s γ Ψ (wcsOwn γ q st)
    (fun st' => iprop(⌜st' = st⌝ ∗ wcsOwn γ q st))) $$ [Hown] as %p %st' ⟨#Hsn, #HΨ, %Heq, Hown⟩
  · iframe #
    iframe Hown
    iintro %st' Hpub Hown
    iunfold wcsPub at Hpub
    iunfold wcsOwn at Hown
    ihave ⟨%Heq, Hpub, Hown⟩ := ghostVar_agree_keep γ.st st' st _ _ $$ [Hpub Hown]
    · iframe
    imodintro
    isplitl [Hpub]
    · iunfold wcsPub; iexact Hpub
    isplitr
    · ipureintro; exact Heq
    iunfold wcsOwn; iexact Hown
  subst Heq
  (try wp_auto)
  wp_apply (wp_AddEvent sp _ _) $$ []
  · iframe #; ipureintro; exact Hsp
  (try wp_auto)
  wp_apply (wp_check wc p st'.1 st'.2) $$ []
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hrv Hown Hsn HΨ

end proof

end cacher
end EtcdGrove
end Perennial
