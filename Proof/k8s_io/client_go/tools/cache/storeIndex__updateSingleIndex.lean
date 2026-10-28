/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__updateSingleIndex.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateSingleIndex
public import Spec.k8s_io.client_go.tools.cache.storeIndex__addKeyToIndex
public import Spec.k8s_io.client_go.tools.cache.storeIndex__deleteKeyFromIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

omit [GooseSemantics] in
theorem delVals_step (V Vj : GoString → KSet) (vs : List GoString) (j : Nat) (x key : GoString)
    (hx : vs[j]? = some x) (hVj : Vj = delVals V (vs.take j) key) :
    (fun w => if w = x then GMap.delete key (Vj w) else Vj w) =
      delVals V (vs.take (j + 1)) key := by
  rw [List.take_add_one, hx, Option.toList_some, delVals_snoc, hVj]

omit [GooseSemantics] in
theorem addVals_step (V Vj : GoString → KSet) (vs : List GoString) (j : Nat) (x key : GoString)
    (hx : vs[j]? = some x) (hVj : Vj = addVals V (vs.take j) key) :
    (fun w => if w = x then <[key := sets.present]> (Vj w) else Vj w) =
      addVals V (vs.take (j + 1)) key := by
  rw [List.take_add_one, hx, Option.toList_some, addVals_snoc, hVj]

theorem storeIndex.updateSingleIndex.wp_proof
    (wp_add : storeIndex.addKeyToIndex.spec (GF := GF) (hG := hG))
    (wp_del : storeIndex.deleteKeyFromIndex.spec (GF := GF) (hG := hG)) :
    storeIndex.updateSingleIndex.spec (GF := GF) (hG := hG) := by
  intro i im ip dqi dqm fv ix OK F f name key old new ovs
  wp_start as ⟨Hixr, Him, %hf, #Hfn, #Hold, #Hnew, #Hovs, Hipr, Hix⟩
  iunfold ownIx at Hix
  icases Hix with ⟨Hip, HIX⟩
  wp_auto
  wp_apply (wp_map_lookup2 go.string IndexFunc.ty im fv name dqm) $$ [$Him] as Him
  simp only [hf, Option.getD_some, Option.isSome_some, _root_.decide_true]
  wp_auto
  iunfold fnOk at Hfn
  icases Hfn with ⟨%hfnn, #Hfun, #Hcall⟩
  -- the old object's values
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ oldObj_ptr ↦ old ∗
      indexFunc_ptr ↦ f ∗ key_ptr ↦ key ∗ name_ptr ↦ name ∗
      ∃ (sl : GoSlice) (dq : DFrac), oldIndexValues_ptr ↦ sl ∗ sl ↦*{dq} ovs)))
    $$ [oldIndexValues oldObj indexFunc key name]
  · cases old with
    | nil =>
      (try wp_auto)
      have hnil : slice.slice (zero_val GoSlice) GoString (W64 0) (W64 0) = slice.nil :=
        (slice_slice_trivial (V := GoString) slice.nil).symm
      rw [hnil]
      isplitr
      · ipureintro; rfl
      iframe
      iunfold objVals at Hovs
      icases Hovs with (%h | ⟨%h, -⟩)
      · rw [h.2]
        iexists (DFrac.own 1)
        iapply ownSlice_nil
      · exact absurd rfl h
    | ok o =>
      iunfold okNil at Hold
      icases Hold with (%h | #HOK)
      · cases h
      (try wp_auto)
      wp_apply Hcall $$ [$HOK] as %sl %err ⟨%herr, %dq, %vs, Hsl, #HF⟩
      subst herr
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iframe
      iunfold objVals at Hovs
      icases Hovs with (%h | ⟨-, #HF'⟩)
      · cases h.1
      iunfold fnFun at Hfun
      ihave %heq := Hfun $$ %(GoInterface.ok o) %vs %ovs HF HF'
      subst heq
      iexists dq
      iexact Hsl
  iintro %v ⟨%hv, oldObj, indexFunc, key, name, %osl, %odq, oldIndexValues, Hosl⟩
  subst hv
  -- the new object's values
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ newObj_ptr ↦ new ∗
      indexFunc_ptr ↦ f ∗ key_ptr ↦ key ∗ name_ptr ↦ name ∗
      ∃ (sl : GoSlice) (dq : DFrac) (nvs : List GoString), indexValues_ptr ↦ sl ∗
        sl ↦*{dq} nvs ∗ objVals F new nvs)))
    $$ [indexValues newObj indexFunc key name]
  · cases new with
    | nil =>
      (try wp_auto)
      have hnil : slice.slice (zero_val GoSlice) GoString (W64 0) (W64 0) = slice.nil :=
        (slice_slice_trivial (V := GoString) slice.nil).symm
      rw [hnil]
      isplitr
      · ipureintro; rfl
      iframe
      iexists (DFrac.own 1), []
      isplitl
      · iapply ownSlice_nil
      · iunfold objVals; ileft; ipureintro; exact ⟨rfl, rfl⟩
    | ok o =>
      iunfold okNil at Hnew
      icases Hnew with (%h | #HOK)
      · cases h
      (try wp_auto)
      wp_apply Hcall $$ [$HOK] as %sl %err ⟨%herr, %dq, %vs, Hsl, #HF⟩
      subst herr
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iframe
      iunfold objVals; iright; iframe #; ipureintro; intro h; cases h
  iintro %v ⟨%hv, newObj, indexFunc, key, name, %nsl, %ndq, %nvs, indexValues, Hnsl, #Hnvs⟩
  subst hv
  (try wp_auto)
  -- the indexer's index, made if none
  wp_apply (wp_map_lookup1 go.string index.ty ip _ name) $$ [$Hip] as Hip
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ i_ptr ↦ i ∗ name_ptr ↦ name ∗
      ∃ (lx : Loc) (X : IxN), idx_ptr ↦ lx ∗ ownIxN lx (DFrac.own 1) X ∗
        ip ↦$ GMap.fmap Prod.fst (<[name := (lx, X)]> ix) ∗
        ([∗map] _n ↦ e ∈ GMap.delete name ix, ownIxN e.1 (DFrac.own 1) e.2) ∗
        ⌜viewN X = viewN (ixAt ix name)⌝)))
    $$ [Hipr i name idx Hip HIX]
  · skip
    cases hn : ix !! name with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      (try wp_auto)
      wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
        (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string)) as %m Hm
      (try wp_auto)
      wp_apply (wp_mapInsert go.string ip _ name m) $$ [$Hip] as Hip
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iframe
      iexists (∅ : IxN)
      iframe
      have hd : GMap.delete name ix = ix := by
        ext n; simp only [GMap.lookup_delete_iff]; split <;> simp_all
      rw [GMap.fmap_insert, hd]
      iframe
      isplitl [Hm]
      · iunfold ownIxN
        rw [GMap.fmap_empty]
        iframe
        iapply BigSepM.bigSepM_empty.2
        itrivial
      · ipureintro
        unfold ixAt viewN
        simp [hn]
    | some e =>
      obtain ⟨lx, X⟩ := e
      simp only [Option.map_some, Option.getD_some]
      icases (BigSepM.bigSepM_delete hn) $$ HIX with ⟨HX, HIX⟩
      iunfold ownIxN at HX
      icases HX with ⟨Hlx, HXs⟩
      ihave %hnn := ownMap_not_nil $$ Hlx
      simp only [decide_eq_false hnn]
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iframe
      iexists X
      have hf : GMap.fmap Prod.fst (<[name := (lx, X)]> ix) = GMap.fmap Prod.fst ix := by
        ext n
        simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
        split
        · subst_vars; simp [hn]
        · rfl
      rw [hf]
      iframe
      iunfold ownIxN
      iframe
      ipureintro
      unfold ixAt
      simp [hn]
  iintro %v ⟨%hv, Hipr, Hrecv, name, %lx, %X, idx, HX, Hip, HIX, %hX⟩
  subst hv
  (try wp_auto)
  ihave %Hol := ownSlice_len $$ Hosl
  ihave %Hnl := ownSlice_len $$ Hnsl
  -- the result when the index is left as is or updated to `X'`
  have hpost : ∀ X' : IxN, updNPost ovs nvs key (viewN (ixAt ix name)) (viewN X') →
      (∀ n, n ≠ name → (<[name := (lx, X')]> ix) !! n = ix !! n) ∧
      updNPost ovs nvs key (viewN (ixAt ix name)) (viewN (ixAt (<[name := (lx, X')]> ix) name)) := by
    intro X' h
    refine ⟨fun n hn => GMap.lookup_insert_ne _ _ (Ne.symm hn), ?_⟩
    unfold ixAt; rw [GMap.lookup_insert]; exact h
  have hfst : ∀ X' : IxN, GMap.fmap Prod.fst (<[name := (lx, X')]> ix) =
      GMap.fmap Prod.fst (<[name := (lx, X)]> ix) := by
    intro X'; rw [GMap.fmap_insert, GMap.fmap_insert]
  by_cases hsame : ∃ a, nvs = [a] ∧ ovs = [a]
  · obtain ⟨a, hna, hoa⟩ := hsame
    rw [hna] at Hnl ⊢
    rw [hoa] at Hol ⊢
    have h1 : nsl.len = W64 1 := by simp at Hnl; word
    have h2 : osl.len = W64 1 := by simp at Hol; word
    simp only [h1, _root_.decide_true]
    (try wp_auto)
    simp only [h2, _root_.decide_true]
    (try wp_auto)
    have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z nsl.len := by rw [h1]; decide
    have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z osl.len := by rw [h2]; decide
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index nsl (sint.Z (W64 0)) [a] _ a (by decide) $$ [Hnsl] as Hnsl
    · isplit
      · iexact Hnsl
      · ipureintro; rfl
    (try wp_auto)
    simp only [hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index osl (sint.Z (W64 0)) [a] _ a (by decide) $$ [Hosl] as Hosl
    · isplit
      · iexact Hosl
      · ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iexists <[name := (lx, X)]> ix, [a]
    iframe
    iframe #
    isplitl [Hip HX HIX]
    · iunfold ownIx
      iframe
      iapply BigSepM.bigSepM_insert_delete.2
      iframe
    · ipureintro
      have := hpost X (Or.inr ⟨a, hoa, hna, hX⟩)
      rw [hoa, hna] at this
      exact this
  · wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        oldIndexValues_ptr ↦ osl ∗ osl ↦*{odq} ovs ∗
        indexValues_ptr ↦ nsl ∗ nsl ↦*{ndq} nvs)))
      $$ [oldIndexValues Hosl indexValues Hnsl]
    · by_cases h1 : nsl.len = W64 1
      · simp only [h1, _root_.decide_true]
        (try wp_auto)
        by_cases h2 : osl.len = W64 1
        · simp only [h2, _root_.decide_true]
          (try wp_auto)
          obtain ⟨b, hb⟩ : ∃ b, nvs = [b] := by
            apply List.length_eq_one_iff.1; rw [Hnl.1, h1]; rfl
          obtain ⟨a, ha⟩ : ∃ a, ovs = [a] := by
            apply List.length_eq_one_iff.1; rw [Hol.1, h2]; rfl
          have hab : b ≠ a := by
            rintro rfl; exact hsame ⟨b, hb, ha⟩
          rw [hb, ha]
          have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z nsl.len := by rw [h1]; decide
          have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z osl.len := by rw [h2]; decide
          simp only [hb1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index nsl (sint.Z (W64 0)) [b] _ b (by decide) $$ [Hnsl] as Hnsl
          · isplit
            · iexact Hnsl
            · ipureintro; rfl
          (try wp_auto)
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index osl (sint.Z (W64 0)) [a] _ a (by decide) $$ [Hosl] as Hosl
          · isplit
            · iexact Hosl
            · ipureintro; rfl
          (try wp_auto)
          simp only [hab, decide_false]
          (try wp_auto)
          iframe
          ipureintro; rfl
        · simp only [h2, decide_false]
          (try wp_auto)
          iframe
          ipureintro; rfl
      · simp only [h1, decide_false]
        (try wp_auto)
        iframe
        ipureintro; rfl
    iintro %v ⟨%hv, oldIndexValues, Hosl, indexValues, Hnsl⟩
    subst hv
    (try wp_auto)
    -- delete the key from the old values' sets
    ihave HI : (∃ (j : w64) (s0 : GoString) (Xj : IxN),
        "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ s0 ∗ "HX" ∷ ownIxN lx (DFrac.own 1) Xj ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ ∗
        "%HXj" ∷ ⌜viewN Xj = delVals (viewN X) ((ovs).take (sint.nat j)) key⌝ : IProp GF)
      $$ [i value HX]
    · iexists W64 0, _, X
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (W64 0) = 0 by word, List.take_zero, delVals_nil]
    wp_for HI
    wp_if_destruct
    · have Hlt : sint.Z j < sint.Z osl.len :=
        Classical.byContradiction fun h => by simp [h] at Hif
      have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨Hj.1, Hlt⟩
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem (ovs) (sint.nat j) as x
      wp_apply wp_load_slice_index osl (sint.Z j) (ovs) odq x Hj.1 $$ [Hosl] as Hosl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      wp_apply wp_del $$ [$HX] as ⟨%Xj', HX, %HXj'⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, x, Xj'
      iframe
      ipureintro
      have Hs : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [Hs, HXj', delVals_step (viewN X) (viewN Xj) _ _ x key Hx_lookup HXj]
    · (try wp_auto)
      have Hjl : sint.nat j = (ovs).length := by rw [Hol.1]; word
      rw [Hjl, List.take_length] at HXj
      -- add the key to the new values' sets
      ihave HI : (∃ (j : w64) (s0 : GoString) (Xj : IxN),
          "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ s0 ∗ "HX" ∷ ownIxN lx (DFrac.own 1) Xj ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nsl.len⌝ ∗
          "%HXj" ∷ ⌜viewN Xj = addVals (delVals (viewN X) (ovs) key)
            ((nvs).take (sint.nat j)) key⌝ : IProp GF)
        $$ [i value HX]
      · iexists W64 0, _, Xj
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, ?_⟩
        rw [show sint.nat (W64 0) = 0 by word, List.take_zero, addVals_nil, HXj]
      wp_for HI
      wp_if_destruct
      · have Hlt : sint.Z j < sint.Z nsl.len :=
          Classical.byContradiction fun h => by simp [h] at Hif
        have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nsl.len := ⟨Hj.1, Hlt⟩
        simp only [Hb', _root_.and_self, ↓reduceIte]
        list_elem (nvs) (sint.nat j) as x
        wp_apply wp_load_slice_index nsl (sint.Z j) (nvs) ndq x Hj.1 $$ [Hnsl] as Hnsl
        · iframe; ipureintro; exact Hx_lookup
        (try wp_auto)
        wp_apply wp_add $$ [$HX] as ⟨%Xj', HX, %HXj'⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, x, Xj'
        iframe
        ipureintro
        have Hs : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        refine ⟨⟨by word, by word⟩, ?_⟩
        rw [Hs, HXj', addVals_step _ (viewN Xj) _ _ x key Hx_lookup HXj]
      · (try wp_auto)
        have Hjl : sint.nat j = (nvs).length := by rw [Hnl.1]; word
        rw [Hjl, List.take_length] at HXj
        iapply HΦ
        iexists <[name := (lx, Xj)]> ix, nvs
        iframe
        iframe #
        isplitl [Hip HX HIX]
        · iunfold ownIx
          rw [hfst Xj]
          iframe
          iapply BigSepM.bigSepM_insert_delete.2
          iframe
        · ipureintro
          refine hpost Xj (Or.inl ?_)
          rw [HXj, hX]

end proof

end cache
end EtcdGrove
end Perennial
