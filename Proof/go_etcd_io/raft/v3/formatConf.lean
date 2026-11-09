/-
Lean-first (no Rocq counterpart): the proof of `formatConf` (`Spec/go_etcd_io/raft/v3/formatConf.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.formatConf
public import Spec.strconv.FormatUint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem formatConf.wp_proof
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    formatConf.spec (GF := GF) (hG := hG) := by
  intro sl dq xs
  wp_start as Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  wp_if_destruct
  · have Hxs : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
    subst Hxs
    wp_apply wp_slice_literal (V := GoString) []
    isplitr
    · ipureintro; rfl
    iintro %out ⟨Hout, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    wp_auto
    iapply HΦ
    iframe
  wp_apply wp_slice_make2 (V := GoString) sl.len as %out ⟨Hout, -⟩
  · ipureintro; exact Hlen.2
  rename_i iu_ptr
  irename i => cnt
  irename i => iu
  ihave IH : iprop(∃ (n v0 i0 : w64) (ys : List GoString),
      "cnt" ∷ i_ptr ↦ n ∗ "v" ∷ v_ptr ↦ v0 ∗ "iu" ∷ iu_ptr ↦ i0 ∗ "Hout" ∷ out ↦* ys ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ ys.length = xs.length ∧
        ∀ k, k < (sint.Z n).toNat → ys[k]? = (xs.map decStr)[k]?⌝) $$ [cnt v iu Hout]
  · iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, Hlen.2, by simp [Hlen.1], fun k hk => ?_⟩
    simp at hk
  wp_for IH
  wp_if_destruct
  · ihave %Hol := ownSlice_len $$ Hout
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from
      ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs _ x Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hx
    try wp_auto
    wp_apply wp_FormatUint
    · ipureintro; word
    iintro %str %Hstr
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len by
      constructor <;> word))]
    wp_apply wp_store_slice_index out (sint.Z n) ys str $$ [Hout] as Hout
    · iframe; ipureintro; constructor <;> word
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hn.2.2.1], fun k hk => ?_⟩
    have hm : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
    rw [hm] at hk
    rw [List.getElem?_set]
    split
    · rename_i hkm
      subst hkm
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word)), List.getElem?_map, Hx, Hstr]
      rfl
    · exact Hn.2.2.2 k (by omega)
  · iapply HΦ
    iframe
    have hys : ys = xs.map decStr := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < xs.length
      · exact Hn.2.2.2 k (by word)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    rw [hys]
    iframe

end proof

end EtcdGrove
end Perennial
