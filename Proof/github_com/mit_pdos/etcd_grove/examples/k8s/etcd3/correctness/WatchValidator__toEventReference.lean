/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.toEventReference` when every event has a reference: the loop appends
each event's reference (`keyFunc`, `objectRV` with the replay's versioner) to a slice
`make([]eventReference, 0, len(events))` (not `nil`, `wp_slice_make3_nn`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__toEventReference
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.objectRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyFunc
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchLemmas

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

theorem mapM_evRefL_cons {r : REv} {rs : List REv} {refs : List (GoString × GoString × w64)}
    (h : (r :: rs).mapM evRefL = some refs) :
    ∃ e es, evRefL r = some e ∧ rs.mapM evRefL = some es ∧ refs = e :: es := by
  rw [List.mapM_cons] at h
  cases hr : evRefL r with
  | none => rw [hr] at h; cases h
  | some e =>
    cases hrs : rs.mapM evRefL with
    | none => rw [hr, hrs] at h; cases h
    | some es =>
      rw [hr, hrs] at h
      simp at h
      exact ⟨e, es, rfl, rfl, h.symm⟩

theorem mapM_evRefL_take {rs : List REv} {refs : List (GoString × GoString × w64)}
    (h : rs.mapM evRefL = some refs) (j : Nat) :
    (rs.take j).mapM evRefL = some (refs.take j) ∧ refs.length = rs.length := by
  induction rs generalizing refs j with
  | nil => simp at h; subst h; simp
  | cons r rs ih =>
    obtain ⟨e, es, hr, hrs, rfl⟩ := mapM_evRefL_cons h
    refine ⟨?_, by simp [(ih hrs 0).2]⟩
    cases j with
    | zero => simp
    | succ j => simp [List.mapM_cons, hr, (ih hrs j).1]

theorem evRefL_some {r : REv} {e : GoString × GoString × w64} (h : evRefL r = some e) :
    ∃ o, r.o = .obj o ∧ e = (storeKeyL (o.Namespace' ++ go!"/" ++ o.Name'), r.ty, o.ResourceVersion') := by
  unfold evRefL at h
  cases ho : r.o with
  | obj o =>
    rw [ho] at h; simp [keyOfL, objRVL] at h
    refine ⟨o, rfl, ?_⟩
    rw [← h]; simp
  | status s => rw [ho] at h; simp [keyOfL] at h
  | other => rw [ho] at h; simp [keyOfL] at h

theorem WatchValidator.toEventReference.wp_proof
    (wp_keyFunc : k8s_etcd3.keyFunc.spec (GF := GF) (hG := hG))
    (wp_objectRV : objectRV.spec (GF := GF) (hG := hG)) :
    WatchValidator.toEventReference.spec (GF := GF) (hG := hG) := by
  intro rp R sl rs refs hok
  wp_start as ⟨#HR, #Hs⟩
  ihave #HR0 := HR
  unfold replayAt
  icases HR with ⟨#Hdrv, %sm, %M, %csl, %cvs, #Hrp, #Hsm, %HMs, %HMrv, %HMch, #HMm, #Hcsl, #Hcvs⟩
  iStructNamed Hrp
  iunfold evsRO at Hs
  icases Hs with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  have hlr : refs.length = rs.length := (mapM_evRefL_take hok 0).2
  wp_auto
  wp_apply (wp_slice_make3_nn (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventReference)
    (W64 0) sl.len (by word)) as %fsl ⟨Hf, Hfc, -, %hfnn⟩
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (esl : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "event" ∷ event_ptr ↦ ev ∗ "refs" ∷ refs_ptr ↦ esl ∗
      "He" ∷ esl ↦* (refs.take (sint.nat j)).map erefV ∗
      "Hc" ∷ ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventReference esl
        (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ esl ≠ slice.nil⌝ : IProp GF) $$ [i event refs Hf Hfc]
  · iexists W64 0, _, fsl
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
    iframe
    ipureintro; exact ⟨by word, by word, hfnn⟩
  wp_for HL
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem vs (sint.nat j) as v
    wp_apply (wp_load_slice_index sl (sint.Z j) vs DFrac.discard v Hj.1) $$ [Hsl] as -
    · isplit
      · iexact Hsl
      · ipureintro; exact Hv_lookup
    obtain ⟨r, hr⟩ : ∃ r, rs[sint.nat j]? = some r := by
      have : sint.nat j < rs.length := by rw [← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨e, he⟩ : ∃ e, refs[sint.nat j]? = some e := by
      have : sint.nat j < refs.length := by rw [hlr, ← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have hre : evRefL r = some e := by
      have h1 := (mapM_evRefL_take hok (sint.nat j + 1)).1
      rw [List.take_add_one, List.take_add_one, hr, he] at h1
      have h0 := (mapM_evRefL_take hok (sint.nat j)).1
      simp only [Option.toList_some, List.mapM_append, h0, List.mapM_cons, List.mapM_nil] at h1
      cases hh : evRefL r with
      | none => rw [hh] at h1; simp at h1
      | some e' => rw [hh] at h1; simp at h1; rw [h1]
    obtain ⟨o, hro, rfl⟩ := evRefL_some hre
    ihave #Hv := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      Hv_lookup hr $$ Hvs
    ihave #Hv' := Hv
    iunfold evRep at Hv'
    icases Hv' with ⟨%hty, #Ho⟩
    isimp only [hro] at Ho
    iunfold evObjRep at Ho
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : refs.take (sint.nat j + 1) = refs.take (sint.nat j) ++
        [(storeKeyL (o.Namespace' ++ go!"/" ++ o.Name'), r.ty, o.ResourceVersion')] := by
      rw [List.take_add_one, he]; rfl
    (try wp_auto)
    wp_apply (wp_keyFunc v.Object' o) $$ [Ho]
    · iframe #
    (try wp_auto)
    wp_apply (wp_objectRV v.Object' o) $$ [Ho]
    · iframe #
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hn, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$He $Hc $Hn] as %esl' ⟨He, Hc, -⟩
    ihave %Hl' := ownSlice_len $$ He
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, v, esl'
    rw [hj1, htake, List.map_append]
    simp only [List.map_cons, List.map_nil, erefV, hty]
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro hnil
    subst hnil
    have h0 : (slice.nil : GoSlice).len = W64 0 := rfl
    rw [h0] at Hl'
    have h1 : sint.nat (W64 0) = 0 := rfl
    rw [h1] at Hl'
    simp at Hl'
  · have hfull : refs.take (sint.nat j) = refs := List.take_of_length_le (by rw [hlr, ← Hl2, Hlen.1]; word)
    rw [hfull]
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; exact ⟨rfl, Hj.2.2⟩

end proof

end k8s_correctness
end EtcdGrove
end Perennial
