/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).initialEvents`: `listItems`' fresh copies, made read-only, each appended as
an Added event.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__initialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__listItems
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

theorem Model.initialEvents.wp_proof
    (wp_listItems : Model.listItems.spec (GF := GF) (hG := hG)) :
    Model.initialEvents.spec (GF := GF) (hG := hG) := by
  intro mp m x key opts b hP hR
  wp_start as #Hm
  wp_auto
  wp_apply (wp_listItems mp m x key opts b hP hR) $$ [Hm] as %isl %err ⟨%herr, Hsl⟩
  · iexact Hm
  subst herr
  unfold objsOwn
  icases Hsl with ⟨%xs, Hisl, -, Hxs⟩
  imod objsDeep_persist xs _ $$ Hxs with #Hxs
  ihave %Hlen := ownSlice_len $$ Hisl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hxs
  wp_auto
  ihave HL : (∃ (j : w64) (ov : GoInterface) (esl : GoSlice)
      (gs : List k8s_io.apimachinery.pkg.watch.Event),
      "i" ∷ i_ptr ↦ j ∗ "obj" ∷ obj_ptr ↦ ov ∗ "events" ∷ events_ptr ↦ esl ∗
      "He" ∷ esl ↦* gs ∗ "Hc" ∷ ownSliceCap k8s_io.apimachinery.pkg.watch.Event esl (DFrac.own 1) ∗
      "#Hg" ∷ ([∗list] g;r ∈ gs;((listItemsL x key m).take (sint.nat j)).map
        (fun o => ({ ty := evAdded, o := .obj o } : REv)), evRep g r) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z isl.len⌝ : IProp GF) $$ [i obj events]
  · iexists W64 0, _, slice.nil, []
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · simp only [List.map_nil]
      iapply BigSepL2.bigSepL2_nil.2
      itrivial
    ipureintro; refine ⟨by word, by word⟩
  iapply wp_fupd
  wp_for HL
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z isl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem xs (sint.nat j) as y
    wp_apply (wp_load_slice_index isl (sint.Z j) xs (DFrac.own 1) y Hj.1) $$ [Hisl] as Hisl
    · isplit
      · iexact Hisl
      · ipureintro; exact Hy_lookup
    obtain ⟨o, ho⟩ : ∃ o, (listItemsL x key m)[sint.nat j]? = some o := by
      have : sint.nat j < (listItemsL x key m).length := by rw [← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave #Hy := BigSepL2.bigSepL2_lookup (Φ := fun _ y o => deepRO (GF := GF) y (DeepV.obj o))
      Hy_lookup ho $$ Hxs
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : (listItemsL x key m).take (sint.nat j + 1) =
        (listItemsL x key m).take (sint.nat j) ++ [o] := by
      rw [List.take_add_one, ho]; rfl
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hn, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$He $Hc $Hn] as %esl' ⟨He, Hc, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, y, esl', _
    rw [hj1, htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitl
    · simp only [named]
      iapply (BigSepL2.bigSepL2_snoc).2
      iframe Hg
      unfold evRep evObjRep
      isplitr
      · ipureintro; rfl
      · iexact Hy
    ipureintro; refine ⟨by word, by word⟩
  · have hjl : sint.nat j = (listItemsL x key m).length := by rw [← Hl2]; word
    isimp only [hjl, List.take_length] at Hg
    (try wp_auto)
    ipersist He
    imodintro
    iapply HΦ
    isplitr
    · ipureintro; rfl
    unfold evsRO
    iexists gs
    isplitl []
    · iexact He
    · iexact Hg

end proof

end k8s_correctness
end EtcdGrove
end Perennial
