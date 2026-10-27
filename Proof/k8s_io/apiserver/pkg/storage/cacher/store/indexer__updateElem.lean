/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/indexer__updateElem.lean`. Lean-first
(no Rocq counterpart).

The loop over the index functions (a map range) keeps the indexer's fields and the two value
slices of the last iteration (`oldIndexValues`, `indexValues`, resliced to `[:0]` for a `nil`
element); each function, called on the old and the new element (`isIndexFn`: some values, no
error); the index of its name (a new one if there is none) taken out of `ownIndices` and put
back (`Hclose`); then either the single unchanged value (`indexer.add`, `continue`) or the old
values' deletions and the new values' additions (two slice ranges, `indexer.delete` and
`indexer.add`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.indexer__updateElem
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.indexer__add
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.indexer__delete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher.store

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

set_option maxHeartbeats 1600000 in
theorem indexer.updateElem.wp_proof
    (wp_add : indexer.add.spec (GF := GF) (hG := hG))
    (wp_delete : indexer.delete.spec (GF := GF) (hG := hG)) :
    indexer.updateElem.spec (GF := GF) (hG := hG) := by
  intro l key old new rv
  wp_start as ⟨Hix, #Hold, #Hnew⟩
  iunfold ownIndexer at Hix
  icases Hix with ⟨%ixs, %fns, %rv0, %fs, Hixs, Hind, Hfns, #Hfm, #Hfs, Hrv⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(∃ (x : GoString) (f : GoFunc)
      (s1 s2 : GoSlice) (v1 v2 : List GoString),
      "name" ∷ name_ptr ↦ x ∗ "indexFunc" ∷ indexFunc_ptr ↦ f ∗
      "oldIndexValues" ∷ oldIndexValues_ptr ↦ s1 ∗ "Hs1" ∷ s1 ↦* v1 ∗
      "indexValues" ∷ indexValues_ptr ↦ s2 ∗ "Hs2" ∷ s2 ↦* v2 ∗
      "err" ∷ err_ptr ↦ GoInterface.nil ∗ "Hixs" ∷ structFieldRef indexer go!"indices" l ↦ ixs ∗
      "Hind" ∷ ownIndices ixs (DFrac.own 1) ∗ "i" ∷ i_ptr ↦ l ∗ "newObj" ∷ newObj_ptr ↦ new ∗
      "oldObj" ∷ oldObj_ptr ↦ old ∗ "key" ∷ key_ptr ↦ key)) $$ Hfm
  iintro %keys %Hkeys
  isplitl [name indexFunc oldIndexValues indexValues err Hixs Hind i newObj oldObj key]
  · iexists _, _, _, _, [], []
    simp only [named]
    iframe
    isplitl
    · iapply ownSlice_nil
    iapply ownSlice_nil
  isplitr
  · imodintro
    iintro %i %name %f ⟨%Hname, %Hf⟩ HP
    iNamed HP
    (try wp_auto)
    wp_if_destruct
    -- `old` is `nil`: `oldIndexValues[:0]`
    ihave %Hl := ownSlice_len s1 (DFrac.own 1) v1 $$ Hs1
    ihave %Hw := ownSlice_wf s1 (DFrac.own 1) v1 $$ Hs1
    icases (ownSlice_slice (V := GoString) (W64 0) (W64 0) s1 (DFrac.own 1) v1
      ⟨by word, by word, by word⟩).1 $$ Hs1 with ⟨-, Hs1, -⟩
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
        sint.Z (W64 0) ≤ sint.Z s1.cap := ⟨by word, by word, by word⟩
    simp only [hb, and_self, ↓reduceIte]
    (try wp_auto)
    rotate_left
    -- otherwise, the index function's values
    icases Hold with (%Hon | #Hel)
    · exfalso; simp_all
    ihave #Hfi := BigSepM.bigSepM_lookup (Φ := fun _ f => isIndexFn (GF := GF) f) Hf $$ Hfs
    iunfold isIndexFn at Hfi
    iclear Hs1
    (try wp_auto)
    wp_apply Hfi $$ [] as %sl %vs Hs1
    · iexact Hel
    (try wp_auto)
    iclear Hfi Hel
    rotate_left
    all_goals (
      wp_if_destruct
      -- `new` is `nil`: `indexValues[:0]`
      ihave %Hl := ownSlice_len s2 (DFrac.own 1) v2 $$ Hs2
      ihave %Hw := ownSlice_wf s2 (DFrac.own 1) v2 $$ Hs2
      icases (ownSlice_slice (V := GoString) (W64 0) (W64 0) s2 (DFrac.own 1) v2
        ⟨by word, by word, by word⟩).1 $$ Hs2 with ⟨-, Hs2, -⟩
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
          sint.Z (W64 0) ≤ sint.Z s2.cap := ⟨by word, by word, by word⟩
      simp only [hb, and_self, ↓reduceIte]
      (try wp_auto)
      rotate_left
      -- otherwise, the index function's values
      icases Hnew with (%Hon | #Hel)
      · exfalso; simp_all
      ihave #Hfi := BigSepM.bigSepM_lookup (Φ := fun _ f => isIndexFn (GF := GF) f) Hf $$ Hfs
      iunfold isIndexFn at Hfi
      iclear Hs2
      (try wp_auto)
      wp_apply Hfi $$ [] as %sl %vs Hs2
      · iexact Hel
      (try wp_auto)
      iclear Hfi Hel
      rotate_left)
    all_goals (
      ihave Hov : (∃ (s : GoSlice) (vs : List GoString), oldIndexValues_ptr ↦ s ∗ s ↦* vs)
        $$ [oldIndexValues Hs1]
      · iexists _, _; iframe
      ihave Hnv : (∃ (s : GoSlice) (vs : List GoString), indexValues_ptr ↦ s ∗ s ↦* vs)
        $$ [indexValues Hs2]
      · iexists _, _; iframe
      icases Hov with ⟨%os, %ovs, oldIndexValues, Hs1⟩
      icases Hnv with ⟨%ns, %nvs, indexValues, Hs2⟩)
    all_goals (
      iunfold ownIndices at Hind
      icases Hind with ⟨%m1, Hm1, Hixm⟩
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string (go.GoType.MapType go.string (go.GoType.MapType go.string (go.GoType.PointerType Element.ty))) ixs m1 name (DFrac.own 1)) $$ [$Hm1] as Hm1
      rcases h1 : m1 !! name with _ | ix
      -- no index of that name: a new one
      simp only [Option.getD_none]
      (try wp_auto)
      wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string (go.GoType.MapType go.string (go.GoType.PointerType Element.ty))) as %ix Hm2
      (try wp_auto)
      wp_apply (wp_mapInsert go.string ixs m1 name ix) $$ [$Hm1] as Hm1
      (try wp_auto)
      ihave Hclose : (ownIdx ix (DFrac.own 1) -∗ ownIndices ixs (DFrac.own 1)) $$ [Hm1 Hixm]
      · iintro Hidx
        iunfold ownIndices
        iexists _
        iframe Hm1
        iapply (BigSepM.bigSepM_insert (Φ := fun (_ : GoString) (l2 : Loc) => ownIdx (GF := GF) l2 (DFrac.own 1)) h1).2
        iframe
      ihave Hidx : ownIdx ix (DFrac.own 1) $$ [Hm2]
      · iunfold ownIdx
        iexists ∅
        iframe
        iapply BigSepM.bigSepM_empty.2; itrivial
      rotate_left
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (l2 : Loc) => ownIdx (GF := GF) l2 (DFrac.own 1)) h1).1 $$ Hixm with ⟨Hidx, Hixm⟩
      iunfold ownIdx at Hidx
      icases Hidx with ⟨%m2, Hm2, Hs⟩
      ihave %Hnn := ownMap_not_nil ix m2 (DFrac.own 1) $$ Hm2
      rw [decide_eq_false Hnn]
      (try wp_auto)
      ihave Hclose : (ownIdx ix (DFrac.own 1) -∗ ownIndices ixs (DFrac.own 1)) $$ [Hm1 Hixm]
      · iintro Hidx
        iunfold ownIndices
        iexists m1
        iframe Hm1
        iapply (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (l2 : Loc) => ownIdx (GF := GF) l2 (DFrac.own 1)) h1).2
        iframe
      ihave Hidx : ownIdx ix (DFrac.own 1) $$ [Hm2 Hs]
      · iunfold ownIdx
        iexists m2
        iframe
      rotate_left)
    all_goals (
      ihave %Hol := ownSlice_len os (DFrac.own 1) ovs $$ Hs1
      ihave %Hnl := ownSlice_len ns (DFrac.own 1) nvs $$ Hs2
      by_cases hn : ns.len = W64 1
      · simp only [hn, _root_.decide_true]
        (try wp_auto)
        by_cases ho : os.len = W64 1
        · simp only [ho, _root_.decide_true]
          (try wp_auto)
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show nvs.length = 1 by rw [Hnl.1, hn]; decide)
          obtain ⟨b, hb'⟩ := List.length_eq_one_iff.mp (show ovs.length = 1 by rw [Hol.1, ho]; decide)
          have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ns.len := by rw [hn]; decide
          have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z os.len := by rw [ho]; decide
          simp only [hb0, hb1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index ns (sint.Z (W64 0)) nvs _ a (by decide) $$ [Hs2] as Hs2
          · iframe; ipureintro; rw [ha]; rfl
          (try wp_auto)
          simp only [hb1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index os (sint.Z (W64 0)) ovs _ b (by decide) $$ [Hs1] as Hs1
          · iframe; ipureintro; rw [hb']; rfl
          (try wp_auto)
          by_cases hab : a = b
          · simp only [hab, _root_.decide_true]
            (try wp_auto)
            simp only [hb0, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index ns (sint.Z (W64 0)) nvs _ a (by decide) $$ [Hs2] as Hs2
            · iframe; ipureintro; rw [ha]; rfl
            (try wp_auto)
            wp_apply (wp_add l key a _ ix) $$ [Hidx] as Hidx
            · iframe #; iframe
            (try wp_auto)
            ihave Hind := Hclose $$ Hidx
            unfold forMapPostcondition
            ileft
            isplitr
            · ipureintro; rfl
            iexists _, _, os, ns, ovs, nvs
            simp only [named]
            iframe
          · simp only [hab, _root_.decide_false]
            (try wp_auto)
            ihave HV : (∃ (j : w64) (vv : GoString), "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ vv ∗
                "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z os.len⌝ : IProp GF) $$ [i value]
            · iexists W64 0, _
              simp only [named]
              iframe
              ipureintro
              constructor <;> word
            wp_for HV
            wp_if_destruct
            · have hlt : sint.Z j < sint.Z os.len := by
                first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
              have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z os.len := ⟨Hj.1, hlt⟩
              simp only [hb, _root_.and_self, ↓reduceIte]
              list_elem ovs (sint.nat j) as v
              wp_apply wp_load_slice_index os (sint.Z j) ovs _ v hb.1 $$ [Hs1] as Hs1
              · iframe; ipureintro; exact Hv_lookup
              (try wp_auto)
              wp_apply (wp_delete l key v ix) $$ [Hidx] as Hidx
              · iframe #; iframe
              wp_for_post
              iframe
              iexists j + W64 1, v
              iframe
              ipureintro
              constructor <;> word
            (try wp_auto)
            ihave HV : (∃ (j : w64) (vv : GoString), "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ vv ∗
                "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ns.len⌝ : IProp GF) $$ [i value]
            · iexists W64 0, _
              simp only [named]
              iframe
              ipureintro
              constructor <;> word
            wp_for HV
            wp_if_destruct
            · have hlt : sint.Z j < sint.Z ns.len := by
                first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
              have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ns.len := ⟨Hj.1, hlt⟩
              simp only [hb, _root_.and_self, ↓reduceIte]
              list_elem nvs (sint.nat j) as v
              wp_apply wp_load_slice_index ns (sint.Z j) nvs _ v hb.1 $$ [Hs2] as Hs2
              · iframe; ipureintro; exact Hv_lookup
              (try wp_auto)
              wp_apply (wp_add l key v _ ix) $$ [Hidx] as Hidx
              · iframe #; iframe
              wp_for_post
              iframe
              iexists j + W64 1, v
              iframe
              ipureintro
              constructor <;> word
            (try wp_auto)
            ihave Hind := Hclose $$ Hidx
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _, _, os, ns, ovs, nvs
            simp only [named]
            iframe
        · simp only [ho, _root_.decide_false]
          (try wp_auto)
          ihave HV : (∃ (j : w64) (vv : GoString), "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ vv ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z os.len⌝ : IProp GF) $$ [i value]
          · iexists W64 0, _
            simp only [named]
            iframe
            ipureintro
            constructor <;> word
          wp_for HV
          wp_if_destruct
          · have hlt : sint.Z j < sint.Z os.len := by
              first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
            have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z os.len := ⟨Hj.1, hlt⟩
            simp only [hb, _root_.and_self, ↓reduceIte]
            list_elem ovs (sint.nat j) as v
            wp_apply wp_load_slice_index os (sint.Z j) ovs _ v hb.1 $$ [Hs1] as Hs1
            · iframe; ipureintro; exact Hv_lookup
            (try wp_auto)
            wp_apply (wp_delete l key v ix) $$ [Hidx] as Hidx
            · iframe #; iframe
            wp_for_post
            iframe
            iexists j + W64 1, v
            iframe
            ipureintro
            constructor <;> word
          (try wp_auto)
          ihave HV : (∃ (j : w64) (vv : GoString), "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ vv ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ns.len⌝ : IProp GF) $$ [i value]
          · iexists W64 0, _
            simp only [named]
            iframe
            ipureintro
            constructor <;> word
          wp_for HV
          wp_if_destruct
          · have hlt : sint.Z j < sint.Z ns.len := by
              first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
            have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ns.len := ⟨Hj.1, hlt⟩
            simp only [hb, _root_.and_self, ↓reduceIte]
            list_elem nvs (sint.nat j) as v
            wp_apply wp_load_slice_index ns (sint.Z j) nvs _ v hb.1 $$ [Hs2] as Hs2
            · iframe; ipureintro; exact Hv_lookup
            (try wp_auto)
            wp_apply (wp_add l key v _ ix) $$ [Hidx] as Hidx
            · iframe #; iframe
            wp_for_post
            iframe
            iexists j + W64 1, v
            iframe
            ipureintro
            constructor <;> word
          (try wp_auto)
          ihave Hind := Hclose $$ Hidx
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _, _, os, ns, ovs, nvs
          simp only [named]
          iframe
      · simp only [hn, _root_.decide_false]
        (try wp_auto)
        ihave HV : (∃ (j : w64) (vv : GoString), "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ vv ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z os.len⌝ : IProp GF) $$ [i value]
        · iexists W64 0, _
          simp only [named]
          iframe
          ipureintro
          constructor <;> word
        wp_for HV
        wp_if_destruct
        · have hlt : sint.Z j < sint.Z os.len := by
            first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
          have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z os.len := ⟨Hj.1, hlt⟩
          simp only [hb, _root_.and_self, ↓reduceIte]
          list_elem ovs (sint.nat j) as v
          wp_apply wp_load_slice_index os (sint.Z j) ovs _ v hb.1 $$ [Hs1] as Hs1
          · iframe; ipureintro; exact Hv_lookup
          (try wp_auto)
          wp_apply (wp_delete l key v ix) $$ [Hidx] as Hidx
          · iframe #; iframe
          wp_for_post
          iframe
          iexists j + W64 1, v
          iframe
          ipureintro
          constructor <;> word
        (try wp_auto)
        ihave HV : (∃ (j : w64) (vv : GoString), "i" ∷ i_ptr ↦ j ∗ "value" ∷ value_ptr ↦ vv ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ns.len⌝ : IProp GF) $$ [i value]
        · iexists W64 0, _
          simp only [named]
          iframe
          ipureintro
          constructor <;> word
        wp_for HV
        wp_if_destruct
        · have hlt : sint.Z j < sint.Z ns.len := by
            first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
          have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ns.len := ⟨Hj.1, hlt⟩
          simp only [hb, _root_.and_self, ↓reduceIte]
          list_elem nvs (sint.nat j) as v
          wp_apply wp_load_slice_index ns (sint.Z j) nvs _ v hb.1 $$ [Hs2] as Hs2
          · iframe; ipureintro; exact Hv_lookup
          (try wp_auto)
          wp_apply (wp_add l key v _ ix) $$ [Hidx] as Hidx
          · iframe #; iframe
          wp_for_post
          iframe
          iexists j + W64 1, v
          iframe
          ipureintro
          constructor <;> word
        (try wp_auto)
        ihave Hind := Hclose $$ Hidx
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _, _, os, ns, ovs, nvs
        simp only [named]
        iframe)
  iintro HP -
  iNamed HP
  (try wp_auto)
  iapply HΦ
  iunfold ownIndexer
  iexists ixs, fns, rv, fs
  iframe
  iframe #

end proof

end cacher
end EtcdGrove
end Perennial
