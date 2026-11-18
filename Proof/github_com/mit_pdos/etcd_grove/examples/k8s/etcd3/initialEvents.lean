module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyInScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.predicate
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `initialEventsL` over a list of items. -/
def initEvsOf (x : Input) (its : List item) : List WEv :=
  (its.filter fun it =>
    keyInScopeL x.WKey' x.Recursive' (storeKeyL it.key') && selOkL x it.obj').map
    fun it => ⟨0, it.obj'⟩

theorem initEvsOf_snoc (x : Input) (l : List item) (e : item) :
    initEvsOf x (l ++ [e]) = initEvsOf x l ++
      (if keyInScopeL x.WKey' x.Recursive' (storeKeyL e.key') && selOkL x e.obj'
       then [⟨0, e.obj'⟩] else []) := by
  unfold initEvsOf
  rw [List.filter_append, List.map_append]
  split <;> simp_all

theorem initialEvents.wp_proof
    (wp_predicate : predicate.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG))
    (wp_SM : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    initialEvents.spec (GF := GF) (hG := hG) := by
  have wp_Matches := mlistMatches.wp_proof wp_SM wp_LM wp_LE wp_FM wp_FE wp_GA
  intro x st g
  wp_start as #Hst
  unfold storeOwn
  icases Hst with ⟨#Hs, %Hrv⟩
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  wp_apply wp_predicate
  irename : (in_ptr ↦ x : IProp GF) => Hin
  ihave HI : (∃ (j : w64) (itm : item) (sl : GoSlice) (ws : List WEvent),
      "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itm ∗ "evs" ∷ evs_ptr ↦ sl ∗
      "Hw" ∷ sl ↦* ws ∗ "Hc" ∷ ownSliceCap WEvent sl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z st.items'.len ∧
        ws.map wevOf = initEvsOf x (g.items.take (sint.nat j))⌝ : IProp GF) $$ [i it evs]
  · iexists W64 0, _, slice.nil, []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    · ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z st.items'.len := ⟨Hj.1, Hif⟩
    list_elem g.items (sint.nat j) as e
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index st.items' (sint.Z j) g.items _ e Hj.1 $$ [Hs] as -
    · isplit
      · iexact Hs
      · ipureintro; exact He_lookup
    (try wp_auto)
    wp_apply wp_storeKey
    (try wp_auto)
    wp_apply wp_keyInScope
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : g.items.take (sint.nat j + 1) = g.items.take (sint.nat j) ++ [e] := by
      rw [List.take_add_one, He_lookup]; rfl
    cases hsc : keyInScopeL x.WKey' x.Recursive' (storeKeyL e.key')
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, e, sl, ws
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hj1, htake, initEvsOf_snoc, hsc, Hj.2.2]
      simp
    · (try wp_auto)
      wp_apply wp_Matches $$ [$pred $o] as ⟨pred, o⟩
      (try wp_auto)
      cases hsel : selOkL x e.obj'
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, e, sl, ws
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, htake, initEvsOf_snoc, hsc, hsel, Hj.2.2]
        simp
      · (try wp_auto)
        wp_apply wp_slice_literal (V := WEvent) (l := [⟨W64 0, e.obj'⟩])
        isplitr
        · ipureintro; rfl
        iintro %nsl ⟨Hn, -⟩
        wp_apply wp_slice_append $$ [$Hw $Hc $Hn] as %sl' ⟨Hw', Hc', -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, e, sl', ws ++ [⟨W64 0, e.obj'⟩]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, htake, initEvsOf_snoc, hsc, hsel, ← Hj.2.2]
        simp [wevOf]
  · (try wp_auto)
    iapply HΦ
    unfold wevsOwnM
    iexists ws
    iframe
    ipureintro
    have : g.items.take (sint.nat j) = g.items := List.take_of_length_le (by word)
    rw [Hj.2.2, this]
    rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
