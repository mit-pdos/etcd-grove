/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/store/btreeStore__Replace.lean`. Lean-first
(no Rocq counterpart).

The tree cleared (`BTree.Clear`), the version set, then the elements inserted in order by
`addOrUpdateElem` (a slice range): after the first `j`, the store holds the insertions of the
first `j` (`(ents.take j).foldl insert []`) at the version `rv`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__Replace
public import Spec.k8s_io.apiserver.pkg.storage.cacher.store.btreeStore__addOrUpdateElem
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clear

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher.store

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem btreeStore.Replace.wp_proof
    (wp_Clear : btree.BTree.Clear.spec (GF := GF) (hG := hG))
    (wp_addOrUpdateElem : btreeStore.addOrUpdateElem.spec (GF := GF) (hG := hG)) :
    btreeStore.Replace.spec (GF := GF) (hG := hG) := by
  intro p s rv0 sl dq ents rv
  wp_start as ⟨Hs, Hsl, #Hents⟩
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree $$ []
  · iPkgInit
  unfold ownStore
  icases Hs with ⟨%t, Htr, Hrv, Ht⟩
  (try wp_auto)
  wp_apply (wp_Clear elemOrder t s false) $$ [$Ht] as Ht
  (try wp_auto)
  ihave %Hlen := ownSlice_len sl dq _ $$ Hsl
  rw [List.length_map] at Hlen
  ihave HV : (∃ (j : w64) (e : Loc), "i" ∷ i_ptr ↦ j ∗ "storeElem" ∷ storeElem_ptr ↦ e ∗
      "Hst" ∷ ownStore p (DFrac.own 1) ((ents.take (sint.nat j)).foldl (btree.insert go.GoStringLt) []) rv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i storeElem Htr Hrv Ht]
  · iexists W64 0, _
    simp only [named]
    iframe
    isplitl
    · unfold ownStore; iexists t; iframe
    ipureintro; constructor <;> word
  wp_for HV
  wp_if_destruct
  · have hlt : sint.Z j < sint.Z sl.len := by
      first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    list_elem ents (sint.nat j) as x
    wp_apply wp_load_slice_index sl (sint.Z j) (ents.map Prod.fst) _ x.1 hb.1 $$ [Hsl] as Hsl
    · iframe; ipureintro
      show (ents.map Prod.fst)[sint.nat j]? = some x.1
      rw [List.getElem?_map, Hx_lookup]; rfl
    (try wp_auto)
    ihave #Hx := BigSepL.bigSepL_lookup (Φ := fun _ (y : Loc × GoString) => elemOrder.item (GF := GF) y.1 y.2)
      Hx_lookup $$ Hents
    wp_apply (wp_addOrUpdateElem p _ rv x.1 x.2 rv) $$ [Hst] as Hst
    · iframe #; iframe
    wp_for_post
    have ht : ents.take (sint.nat (j + W64 1)) = ents.take (sint.nat j) ++ [x] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx_lookup]; rfl
    iframe
    iexists j + W64 1, x.1
    rw [ht, List.foldl_append]
    simp only [named, List.foldl_cons, List.foldl_nil]
    iframe
    ipureintro; constructor <;> word
  (try wp_auto)
  iapply HΦ
  have hj : sint.nat j = ents.length := by
    have : ¬ sint.Z j < sint.Z sl.len := by
      first | exact Hif | (intro h; exact Hif (by simp [h]))
    word
  have htk : ents.take (sint.nat j) = ents := by rw [hj, List.take_length]
  rw [htk]
  unfold ownStore at *
  iframe

end proof

end cacher
end EtcdGrove
end Perennial
