/-
Lean-first (no Rocq counterpart).

The proof of `Replay.EventsForRVs`: the loop over the replay's changes keeps the events of the changes
visited (`eventsForRVsL` of a prefix, `evStepL`): a change outside the range or the watch's scope is
skipped, any other gives its `toWatchEvent` (each change has an object or the one before it, `chgOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__EventsForRVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change__toWatchEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.keyInScope

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

/-- One change's contribution to `eventsForRVsL`. -/
def evStepL (x : Input) (mn mx : w64) (c : RChange) : Option REv :=
  if uint.nat mn ≤ uint.nat c.rv ∧ uint.nat c.rv < uint.nat mx ∧
      keyInScopeL x.WKey' x.Recursive' c.key = true then toWatchEventL x c
  else none

theorem evStep_take (R : RReplay) (x : Input) (mn mx : w64) (j : Nat) (c : RChange)
    (hc : R.changes[j]? = some c) :
    (R.changes.take (j + 1)).filterMap (evStepL x mn mx) =
      (R.changes.take j).filterMap (evStepL x mn mx) ++ (evStepL x mn mx c).toList := by
  rw [List.take_add_one, hc, List.filterMap_append]
  cases h : evStepL x mn mx c <;> simp [h]

set_option hygiene false in
/-- A change that gives no event: the loop goes on with the same events. -/
local macro "efr_skip" : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists j + W64 1, cv, esl, gs
  rw [hj1, hstep, hev]
  simp only [Option.toList_none, List.append_nil]
  iframe
  isplitl []
  · iexact Hg
  ipureintro; refine ⟨by word, by word⟩))

theorem Replay.EventsForRVs.wp_proof
    (wp_TWE : Change.toWatchEvent.spec (GF := GF) (hG := hG))
    (wp_KIS : keyInScope.spec (GF := GF) (hG := hG)) :
    Replay.EventsForRVs.spec (GF := GF) (hG := hG) := by
  intro rp R x req p mn mx
  wp_start as ⟨#HR, #Hreq, Hr⟩
  unfold replayAt
  icases HR with ⟨#Hdrv, %sm, %M, %csl, %cvs, #Hrp, #Hsm, %HMs, %HMrv, %HMch, #HMm, #Hcsl, #Hcvs⟩
  unfold wreqRep
  icases Hreq with ⟨%p', %hreq, #Hsie⟩
  subst hreq
  iunfold rangeRep at Hr
  iStructNamed Hrp
  ihave %Hlen := ownSlice_len $$ Hcsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hcvs
  wp_auto
  wp_apply (wp_slice_make3 (V := k8s_io.apimachinery.pkg.watch.Event) (W64 0) csl.len (by word))
    as %fsl ⟨Hf, Hfc, -⟩
  ihave HL : (∃ (j : w64) (ch : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change)
      (esl : GoSlice) (gs : List k8s_io.apimachinery.pkg.watch.Event),
      "i" ∷ i_ptr ↦ j ∗ "change" ∷ change_ptr ↦ ch ∗ "filtered" ∷ filtered_ptr ↦ esl ∗
      "He" ∷ esl ↦* gs ∗ "Hc" ∷ ownSliceCap k8s_io.apimachinery.pkg.watch.Event esl (DFrac.own 1) ∗
      "#Hg" ∷ ([∗list] g;r ∈ gs;(R.changes.take (sint.nat j)).filterMap (evStepL x mn mx), evRep g r) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z csl.len⌝ : IProp GF) $$ [i change filtered Hf Hfc]
  · iexists W64 0, _, fsl, []
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl
    · simp only [named, List.filterMap_nil]
      iapply BigSepL2.bigSepL2_nil.2
      itrivial
    ipureintro; refine ⟨by word, by word⟩
  iapply wp_fupd
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z csl.len := by simpa using Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z csl.len := ⟨Hj.1, Hif'⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem cvs (sint.nat j) as cv
    wp_apply (wp_load_slice_index csl (sint.Z j) cvs DFrac.discard cv Hj.1) $$ [Hcsl] as -
    · isplit
      · iexact Hcsl
      · ipureintro; exact Hcv_lookup
    obtain ⟨c, hc⟩ : ∃ c, R.changes[sint.nat j]? = some c := by
      have : sint.nat j < R.changes.length := by rw [← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave #Hcv := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => changeVRep (GF := GF) v r)
      Hcv_lookup hc $$ Hcvs
    ihave #Hcv' := Hcv
    iunfold changeVRep at Hcv'
    icases Hcv' with ⟨%hkr, -, -⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hstep := evStep_take R x mn mx (sint.nat j) c hc
    (try wp_auto)
    rw [hkr.2]
    by_cases hlo : uint.Z c.rv < uint.Z mn
    · have hev : evStepL x mn mx c = none := by
        unfold evStepL; rw [ite_eq_right_iff.2]; intro h; exfalso; word
      simp only [hlo, decide_true]
      wp_auto
      efr_skip
    simp only [hlo, decide_false]
    wp_auto
    rw [hkr.2]
    by_cases hhi : uint.Z mx ≤ uint.Z c.rv
    · have hev : evStepL x mn mx c = none := by
        unfold evStepL; rw [ite_eq_right_iff.2]; intro h; exfalso; word
      simp only [hhi, decide_true]
      wp_auto
      efr_skip
    simp only [hhi, decide_false]
    wp_auto
    rw [hkr.1]
    wp_apply (wp_KIS x.WKey' x.Recursive' c.key)
    cases hk : keyInScopeL x.WKey' x.Recursive' c.key
    · have hev : evStepL x mn mx c = none := by
        unfold evStepL; rw [ite_eq_right_iff.2]; intro h; rw [hk] at h; exact absurd h.2.2 (by simp)
      wp_auto
      efr_skip
    have hev : evStepL x mn mx c = toWatchEventL x c := by
      unfold evStepL; rw [ite_eq_left_iff.2]; intro h; exfalso; apply h; exact ⟨by word, by word, hk⟩
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change.ty) (m := go!"toWatchEvent")]
    wp_call
    (try wp_auto)
    have hco : chgOk c := HMch c (List.mem_of_getElem? hc)
    wp_apply (wp_TWE cv c x hco) $$ [] as %ep %eerr ⟨%heerr, Hep⟩
    · iframe #
    subst heerr
    wp_auto
    cases htw : toWatchEventL x c with
    | none =>
      rw [htw] at hev
      icases Hep with %hep
      subst hep
      simp only [decide_true, Bool.not_true]
      wp_auto
      efr_skip
    | some r =>
      rw [htw] at hev
      icases Hep with ⟨%v, Hv, #Hvr⟩
      ihave %hnn := typedPointsto_not_null _ _ _ $$ Hv
      simp only [decide_eq_false hnn, Bool.not_false]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %nsl ⟨Hn, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$He $Hc $Hn] as %esl' ⟨He, Hc, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, cv, esl', _
      rw [hj1, hstep, hev]
      iframe
      isplitl []
      · simp only [named, Option.toList_some]
        iapply (BigSepL2.bigSepL2_snoc).2
        iframe Hg
        iexact Hvr
      ipureintro; refine ⟨by word, by word⟩
  · have hjl : sint.nat j = R.changes.length := by rw [← Hl2]; word
    isimp only [hjl, List.take_length] at Hg
    have hev : R.changes.filterMap (evStepL x mn mx) = eventsForRVsL R x mn mx := rfl
    isimp only [hev] at Hg
    (try wp_auto)
    ipersist He
    imodintro
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    isplitl []
    · iunfold evsRO
      iexists gs
      isplitl []
      · iexact He
      · iexact Hg
    · iunfold rangeRep
      iexact Hr

end proof

end k8s_correctness
end EtcdGrove
end Perennial
