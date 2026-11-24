module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__listItems
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.keyInScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.maps.Keys
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input labelSel fieldSel)


section pure

variable [GooseExts]

/-- `listItems`' result over the keys `ks` visited (in order). -/
def itemsOfKeys (x : Input) (key : GoString) (m : RM) (ks : List GoString) : List Obj :=
  (((ks.filterMap fun k => (m.items !! k).map (k, ·)).filter fun ko =>
    keyInScopeL key x.Recursive' ko.1).filter fun ko => selOkL x ko.2).map Prod.snd

theorem listItemsL_keys (x : Input) (key : GoString) (m : RM) :
    listItemsL x key m = itemsOfKeys x key m (sortedKeysL m.items) := rfl

theorem itemsOfKeys_snoc (x : Input) (key : GoString) (m : RM) (ks : List GoString) (k : GoString)
    (o : Obj) (ho : m.items !! k = some o) :
    itemsOfKeys x key m (ks ++ [k]) = itemsOfKeys x key m ks ++
      (if keyInScopeL key x.Recursive' k && selOkL x o then [o] else []) := by
  have h1 : ([k].filterMap fun k => (m.items !! k).map (k, ·)) = [(k, o)] := by simp [ho]
  unfold itemsOfKeys
  simp only [List.filterMap_append, List.filter_append, List.map_append, h1]
  congr 1
  cases h1 : keyInScopeL key x.Recursive' k <;> cases h2 : selOkL x o <;> simp [h1, h2]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.listItems.wp_proof
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_Keys : maps.Keys.spec_objMap (GF := GF) (hG := hG))
    (wp_SM : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    Model.listItems.spec (GF := GF) (hG := hG) := by
  have wp_Matches := mlistMatchesW.wp_ok wp_SM wp_LM wp_LE wp_FM wp_FE wp_GA
  intro mp m x key opts b hP hR
  wp_start as Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, #HI, #Hit, #HR⟩
  iStructNamed Hp
  wp_auto
  ihave %HszM := itemsRO_size_map M m.items $$ Hit
  wp_apply (wp_Keys il) as %f #Hf
  wp_apply Hf $$ %M %DFrac.discard [] [HI] %HszM as %s %ks - Hs %Hks
  · iexact HI
  iStructNamed opts
  irename : ("_" ∷ True : IProp GF) => Htriv
  iclear Htriv
  ihave %Hsl := ownSlice_len $$ Hs
  ihave %hdom := itemsRO_dom_all M m.items $$ Hit
  have hks : ks = sortedKeysL m.items :=
    sortedKeysL_unique m.items ks (fun k => by rw [Hks.1, hdom]) Hks.2
  ihave HL : (∃ (j : w64) (isl : GoSlice) (xs : List GoInterface) (kv : GoString),
      "i" ∷ i_ptr ↦ j ∗ "items" ∷ items_ptr ↦ isl ∗ "k" ∷ k_ptr ↦ kv ∗
      "Hisl" ∷ isl ↦* xs ∗ "Hcap" ∷ ownSliceCap GoInterface isl (DFrac.own 1) ∗
      "Hxs" ∷ ([∗list] y;o ∈ xs;itemsOfKeys x key m (ks.take (sint.nat j)),
        deepRep (DFrac.own 1) y (.obj o)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i items k]
  · iexists W64 0, slice.nil, [], (zero_val GoString)
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · simp only [itemsOfKeys, List.filterMap_nil, List.filter_nil, List.map_nil, named]
      iapply BigSepL2.bigSepL2_nil.2
      itrivial
    ipureintro; refine ⟨by word, by word⟩
  wp_for HL
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ks (sint.nat j) as kj
    wp_apply (wp_load_slice_index s (sint.Z j) ks (DFrac.own 1) kj Hj.1) $$ [Hs] as Hs
    · isplit
      · iexact Hs
      · ipureintro; exact Hkj_lookup
    wp_apply wp_keyInScope
    rw [hR]
    have hkjM : (M !! kj).isSome := (Hks.1 kj).1 (List.mem_of_getElem? Hkj_lookup)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hkjM
    icases itemsRO_lookup M m.items kj v hv $$ Hit with ⟨%p, %o, ⟨%ho, %hvp⟩, #Hpo⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : ks.take (sint.nat j + 1) = ks.take (sint.nat j) ++ [kj] := by
      rw [List.take_add_one, Hkj_lookup]; rfl
    have hstep := itemsOfKeys_snoc x key m (ks.take (sint.nat j)) kj o ho
    rw [← htake] at hstep
    cases hsc : keyInScopeL key x.Recursive' kj
    · simp only [hsc, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, isl, xs, kj
      rw [hj1, hstep]
      iframe
      ipureintro; refine ⟨by word, by word⟩
    · simp only [hsc, Bool.true_and] at hstep
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M kj
        DFrac.discard) $$ HI as -
      rw [hv, Option.getD_some, hvp]
      (try wp_auto)
      isimp only [hP] at Predicate
      wp_apply (wp_Matches _ x b p o DFrac.discard) $$ [$Hinit $Predicate $Hpo] as ⟨Predicate, -⟩
      rw [hP]
      cases hsel : selOkL x o
      · simp only [hsel, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, isl, xs, kj
        rw [hj1, hstep]
        iframe
        ipureintro; refine ⟨by word, by word⟩
      · simp only [hsel, ↓reduceIte] at hstep
        (try wp_auto)
        wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
        · iexact Hpo
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hisl $Hcap $Hosl] as %isl' ⟨Hisl, Hcap, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, isl', _, kj
        rw [hj1, hstep]
        iframe
        isplitl
        · iapply BigSepL2.bigSepL2_singleton.2
          unfold deepRep
          iexists c
          iframe Hc
          ipureintro; rfl
        ipureintro; refine ⟨by word, by word⟩
  · have hjl : sint.nat j = ks.length := by word
    have hfin : itemsOfKeys x key m (ks.take (sint.nat j)) = listItemsL x key m := by
      rw [hjl, List.take_length, hks, listItemsL_keys]
    (try wp_auto)
    iapply HΦ
    isplitr
    · ipureintro; rfl
    unfold objsOwn
    rw [← hfin]
    iexists xs
    iframe

end proof

end k8s_correctness
end EtcdGrove
end Perennial
