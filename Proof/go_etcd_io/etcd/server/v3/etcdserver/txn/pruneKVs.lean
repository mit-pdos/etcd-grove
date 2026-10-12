/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.pruneKVs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.pruneKVs.wp_proof : txn.pruneKVs.spec (GF := GF) (hG := hG) := by
  intro rr rev count vs f P
  wp_start as ⟨Hrr, #Hf⟩
  iunfold txn.rangeResultIs at Hrr
  icases Hrr with ⟨%sl, %l, %Hl, Hrr, Hown⟩
  iunfold txn.kvsOwnAt at Hown
  icases Hown with ⟨Hsl, Hkvs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen
  wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (n jw ig : w64) (cs : List Loc) (kept : List (Loc × EtcdKv)),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ ig ∗ "j" ∷ j_ptr ↦ jw ∗ "Hsl" ∷ sl ↦* cs ∗
      "Hkept" ∷ txn.kvsAt kept ∗ "Hrest" ∷ txn.kvsAt (l.drop (sint.nat n)) ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ l.length ∧
        kept = (l.take (sint.nat n)).filter (fun x => !P x.2) ∧ sint.Z jw = kept.length ∧
        cs.length = l.length ∧
        (∀ t, t < kept.length → cs[t]? = (kept[t]?).map Prod.fst) ∧
        (∀ t, sint.nat n ≤ t → cs[t]? = (l[t]?).map Prod.fst)⌝) $$ [i Higo j Hsl Hkvs]
  · iexists W64 0, W64 0, _, _, []
    iframe i Higo j Hsl
    isplitl []
    · iapply txn.kvsAt_nil
    rw [show sint.nat (W64 0) = 0 by rfl, List.drop_zero]
    iframe Hkvs
    ipureintro
    refine ⟨by decide, by omega, by simp, by decide, by simp, fun t ht => by simp at ht, fun t _ => by simp⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hn0, hnl, hkept, hjw, hcsl, hpre, hsuf⟩ := Hinv
    have hlt : sint.nat n < l.length := by word
    obtain ⟨x, hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hcsn : cs[(sint.Z n).toNat]? = some x.1 := by
      rw [show (sint.Z n).toNat = sint.nat n from rfl, hsuf _ (Nat.le_refl _), hx]; rfl
    have Hbn : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨hn0, Hif⟩
    simp only [Hbn, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) cs (DFrac.own 1) x.1 hn0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hcsn
    simp only [Hbn, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) cs (DFrac.own 1) x.1 hn0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hcsn
    have hklen : kept.length ≤ sint.nat n := by
      rw [hkept]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
    have Hbj : 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z sl.len := by
      refine ⟨by omega, ?_⟩; have := Hlen.1; word
    simp only [Hbj, _root_.and_self, ite_true]
    wp_apply wp_store_slice_index sl (sint.Z jw) cs x.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact ⟨Hbj.1, by have := Hlen.1; word⟩
    have hcsn' : (cs.set (sint.Z jw).toNat x.1)[(sint.Z n).toNat]? = some x.1 := by
      rw [List.getElem?_set]
      split
      · rw [if_pos (by rw [hcsl]; word)]
      · exact hcsn
    simp only [Hbn, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) _ (DFrac.own 1) x.1 hn0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hcsn'
    have hdrop : l.drop (sint.nat n) = x :: l.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hx).2]
    rw [hdrop]
    icases (txn.kvsAt_cons x _).1 $$ Hrest with ⟨Hx, Hrest⟩
    wp_apply Hf $$ %x.1 %x.2 [$Hx] as Hx
    have htake : (l.take (sint.nat n + 1)).filter (fun x => !P x.2) =
        kept ++ (if P x.2 then [] else [x]) := by
      rw [List.take_succ, hx, List.filter_append, ← hkept]
      cases hpx : P x.2 <;> simp [hpx]
    have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hk : (sint.Z jw).toNat = kept.length := by omega
    cases hp : P x.2
    · -- kept
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, jw + W64 1, n, cs.set (sint.Z jw).toNat x.1, kept ++ [x]
      iframe
      rw [hsn]
      iframe Hrest
      isplitl [Hkept Hx]
      · unfold txn.kvsAt; iapply BigSepL.bigSepL_snoc.2; iframe
      ipureintro
      rw [hk]
      refine ⟨by word, by omega, by rw [htake, hp]; rfl, by
        have := Hlen.1
        simp only [List.length_append, List.length_singleton]
        word, by simp [hcsl], ?_, ?_⟩
      · intro t ht
        rw [List.getElem?_set]
        simp only [List.length_append, List.length_singleton] at ht
        by_cases htk : kept.length = t
        · subst htk; rw [if_pos rfl, if_pos (by omega)]; simp
        · rw [if_neg htk, hpre t (by omega), List.getElem?_append_left (by omega)]
      · intro t ht
        rw [List.getElem?_set, if_neg (by omega), hsuf t (by omega)]
    · -- pruned
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, jw, n, cs.set (sint.Z jw).toNat x.1, kept
      iframe
      rw [hsn]
      iframe Hrest
      ipureintro
      rw [hk]
      refine ⟨by word, by omega, by rw [htake, hp]; simp, hjw, by simp [hcsl], ?_, ?_⟩
      · intro t ht
        rw [List.getElem?_set, if_neg (by omega), hpre t ht]
      · intro t ht
        rw [List.getElem?_set, if_neg (by omega), hsuf t (by omega)]

  · obtain ⟨hn0, hnl, hkept, hjw, hcsl, hpre, hsuf⟩ := Hinv
    have hnlen : sint.nat n = l.length := by have := Hlen.1; word
    rw [hnlen, List.take_length] at hkept
    have hklen : kept.length ≤ l.length := by rw [hkept]; exact List.length_filter_le _ _
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z jw ∧ sint.Z jw ≤ sint.Z sl.cap := by
      refine ⟨by decide, by word, ?_⟩; have := Hlen.1; have := Hwf.2; word
    simp only [Hb, _root_.and_self, ite_true]
    icases (ownSlice_slice (W64 0) jw sl _ cs ⟨by decide, by word, by have := Hlen.1; word⟩).1 $$ Hsl
      with ⟨-, Hsl, -⟩
    wp_auto
    have hsub : subslice (sint.nat (W64 0)) (sint.nat jw) cs = kept.map Prod.fst := by
      apply List.ext_getElem?
      intro t
      simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.getElem?_take]
      by_cases ht : t < kept.length
      · rw [if_pos (by word), hpre t ht, List.getElem?_map]
      · rw [if_neg (by word), List.getElem?_map, List.getElem?_eq_none (by omega)]; rfl
    rw [hsub] at *
    iapply HΦ
    unfold txn.rangeResultIs txn.kvsOwnAt
    iexists _, kept
    iframe
    ipureintro
    rw [hkept, ← Hl, List.filter_map]
    rfl

end proof

end EtcdGrove
end Perennial
