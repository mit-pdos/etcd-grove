/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.validateReliable` on the accepting run: the events' range
(`watchRevisionRange`) is none (nothing to check) or `[mn, mx)`, and the changes' events over it
(`Replay.EventsForRVs`) compare equal to the events without bookmarks and errors
(`filterOutBookmarksAndErrors`, `compareEvents`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__validateReliable
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.watchRevisionRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__EventsForRVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.filterOutBookmarksAndErrors
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__compareEvents

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem WatchValidator.validateReliable.wp_proof
    (wp_WRR : watchRevisionRange.spec (GF := GF) (hG := hG))
    (wp_EFR : Replay.EventsForRVs.spec (GF := GF) (hG := hG))
    (wp_filter : filterOutBookmarksAndErrors.spec (GF := GF) (hG := hG))
    (wp_CE : WatchValidator.compareEvents.spec (GF := GF) (hG := hG)) :
    WatchValidator.validateReliable.spec (GF := GF) (hG := hG) := by
  intro rp R x req sl rs hok
  unfold reliableOkR at hok
  cases hwr : watchRangeL x rs with
  | none => rw [hwr] at hok; cases hok
  | some o =>
  rw [hwr] at hok
  wp_start as ⟨#HR, #Hreq, #Hs⟩
  ihave #HR0 := HR
  iunfold replayAt at HR0
  icases HR0 with ⟨#Hd, -⟩
  wp_auto
  wp_apply (wp_WRR req x sl rs o hwr) $$ [] as %p %err ⟨%herr, Hr⟩
  · iframe #
  subst herr
  wp_auto
  cases o with
  | none =>
    iunfold rangeRep at Hr
    icases Hr with %hp
    subst hp
    wp_auto
    iapply HΦ; ipureintro; rfl
  | some mm =>
  obtain ⟨mn, mx⟩ := mm
  simp only at hok
  iunfold rangeRep at Hr
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hr
  ihave Hr2 : rangeRep (GF := GF) p (some (mn, mx)) $$ [Hr]
  · iunfold rangeRep; iexact Hr
  simp only [decide_eq_false hnn]
  wp_auto
  wp_apply (wp_EFR rp R x req p mn mx) $$ [Hr2] as %esl %eerr ⟨%heerr, #Hesl, Hr2⟩
  · iframe #
    iexact Hr2
  subst heerr
  wp_auto
  wp_apply (wp_filter sl rs) $$ [] as %fsl #Hf
  · iframe #
  rw [method_unfold (t := go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"compareEvents")]
  wp_call
  (try wp_auto)
  wp_apply (wp_CE rp R esl fsl _ _ hok) $$ [] as %cerr %hcerr
  · iframe #
  subst hcerr
  wp_auto
  iapply HΦ; ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
