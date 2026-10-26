/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/watchCache__WaitUntilFreshAndGet.lean`. Lean-first (no Rocq counterpart).
The version (`getCurrentRV`'s or the versioner's, which both give the caller's fact of it
without an error); at `0`, the store's latest snapshot with a trivial view shift; otherwise
`waitAndGetLatestSnapshot`; then the snapshot's `GetByKey` (the `btreeStore`'s, which never fails).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__WaitUntilFreshAndGet
public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__waitAndGetLatestSnapshot
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.WatchCacheStorage__LatestSnapshot
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__ResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__GetByKey
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

theorem watchCache.WaitUntilFreshAndGet.wp_proof
    (wp_waitGet : watchCache.waitAndGetLatestSnapshot.spec (GF := GF) (hG := hG))
    (wp_LatestSnapshot : WatchCacheStorage.LatestSnapshot.spec (GF := GF) (hG := hG))
    (wp_ResourceVersion : btreeStore.ResourceVersion.spec (GF := GF) (hG := hG))
    (wp_GetByKey : btreeStore.GetByKey.spec (GF := GF) (hG := hG))
    (wp_SpanFromContext : tracing.SpanFromContext.spec (GF := GF) (hG := hG))
    (wp_AddEvent : tracing.Span.AddEvent.spec (GF := GF) (hG := hG)) :
    watchCache.WaitUntilFreshAndGet.spec (GF := GF) (hG := hG) := by
  intro wc γ Ψ parseRV ctxPre curRV ctx rvs key
  wp_start as ⟨#Hwc, #Hget, Hcp, Htok⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store $$ []
  · iPkgInit
  ihave #Ptr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing $$ []
  · iPkgInit
  iunfold wcGetOk at Hget
  icases Hget with ⟨%cfg, %vi, %f, #Hcfg, #Hvi, #Hf, #Hparse, #Hcur⟩
  (try wp_auto)
  wp_apply (wp_SpanFromContext ctx) $$ [] as %sp %Hsp
  (try wp_auto)
  wp_if_destruct
  -- `""`: the current revision
  (try wp_auto)
  wp_apply Hcur $$ [$Hcp] as %n %err Hm0
  (try wp_auto)
  ihave Hm : (⌜err = GoInterface.nil⌝ -∗
      (⌜(go!"" : GoString) = go!""⌝ ∗ curRV n ∨
        ⌜(go!"" : GoString) ≠ go!"" ∧ parseRV go!"" = some n⌝)) $$ [Hm0]
  · iintro %he
    ileft
    ispecialize Hm0 $$ %he
    iframe Hm0
    ipureintro
    rfl
  rotate_left
  -- a version to parse
  (try wp_auto)
  wp_apply Hparse as %n %err %Hp
  (try wp_auto)
  ihave Hm : (⌜err = GoInterface.nil⌝ -∗
      (⌜rvs = go!""⌝ ∗ curRV n ∨ ⌜rvs ≠ go!"" ∧ parseRV rvs = some n⌝)) $$ []
  · iintro %he
    iright
    ipureintro
    refine ⟨by assumption, ?_⟩
    revert Hp
    cases parseRV rvs <;> simp_all
  rotate_left
  -- both: `Hm`
  all_goals (
    (try wp_auto)
    cases err with
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      iframe Htok
      iintro %h
      exfalso; simp_all
    | nil =>
      ispecialize Hm $$ %rfl
      (try wp_auto)
      wp_if_destruct
      · -- `0`: the latest snapshot, without the lock
        iunfold isWC at Hwc
        icases Hwc with ⟨%s, %c, %cfg', #Hs, #Hwcs, -, -, -, -, -⟩
        (try wp_auto)
        wp_apply (wp_LatestSnapshot s γ Ψ emp (fun _ => emp)) $$ [] as %p %st ⟨#Hsn, #HΨ, -⟩
        · iframe #
          isplitl
          · itrivial
          iintro %st' Hpub -
          imodintro
          iframe
        (try wp_auto)
        wp_apply (wp_ResourceVersion p DFrac.discard st.1 st.2) $$ [] as -
        · iframe #
          iunfold isSnap at Hsn
          iexact Hsn
        (try wp_auto)
        wp_apply (wp_GetByKey p DFrac.discard st.1 st.2 key) $$ [] as -
        · iframe #
          iunfold isSnap at Hsn
          iexact Hsn
        (try wp_auto)
        wp_apply (wp_AddEvent sp _ _) $$ []
        · iframe #; ipureintro; exact Hsp
        (try wp_auto)
        iapply HΦ
        iframe Htok
        iintro -
        iexists p, st, (W64 0)
        iframe Hsn HΨ Hm
        ipureintro
        refine ⟨rfl, rfl, rfl, ?_⟩
        word
      · -- otherwise: wait under the read lock
        (try wp_auto)
        wp_apply (wp_waitGet wc γ Ψ ctx n _) $$ [Htok] as %snap %rv %idx %err2 ⟨Htok, Hres⟩
        · iframe #; iframe
        (try wp_auto)
        cases err2 with
        | ok ei =>
          (try wp_auto)
          iapply HΦ
          iframe Htok
          iintro %h
          exfalso; simp_all
        | nil =>
          ispecialize Hres $$ %rfl
          icases Hres with ⟨%p, %st, %Hsnap, #Hsn, #HΨ⟩
          obtain ⟨rfl, rfl, Hge⟩ := Hsnap
          (try wp_auto)
          wp_apply (wp_GetByKey p DFrac.discard st.1 st.2 key) $$ [] as -
          · iframe #
            iunfold isSnap at Hsn
            iexact Hsn
          (try wp_auto)
          wp_apply (wp_AddEvent sp _ _) $$ []
          · iframe #; ipureintro; exact Hsp
          (try wp_auto)
          iapply HΦ
          iframe Htok
          iintro -
          iexists p, st, n
          iframe Hsn HΨ Hm
          ipureintro
          refine ⟨rfl, rfl, rfl, ?_⟩
          rcases Hge with h | h
          · simp_all
          · exact h)

end proof

end cacher
end EtcdGrove
end Perennial
