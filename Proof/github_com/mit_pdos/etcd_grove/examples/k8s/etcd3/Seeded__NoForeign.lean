module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Seeded__NoForeign
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistoryRevs
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.isWrite

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Seeded.NoForeign.wp_proof (wp_isWrite : isWrite.spec (GF := GF) (hG := hG))
    (wp_HistoryRevs : HistoryRevs.spec (GF := GF) (hG := hG)) :
    Seeded.NoForeign.spec (GF := GF) (hG := hG) := by
  intro s sl ops xs dq Hops Hok Hcost
  have hmax : (#(functions go.max [go.uint64, go.uint64]) : val) = max.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)
  wp_start as Hs
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %wm Hwm
  (try wp_auto)
  ihave %Hlen := ownSlice_len $$ Hs
  ihave HI : (∃ (j : w64) (opv : github_com.anishathalye.porcupine.Operation) (W : GMap w64 Bool)
      (mv : w64),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ opv ∗ "Hwm" ∷ wm ↦$ W ∗ "m" ∷ m_ptr ↦ mv ∗
      "%Hinv" ∷ ⌜NfInv s.st0'.rv' (xs.take (sint.nat j)) W mv⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i op Hwm m]
  · iexists W64 0, _, _, _
    iframe
    ipureintro
    refine ⟨?_, by word, by word⟩
    rw [show sint.nat (W64 0) = 0 by word, List.take_zero]
    exact nfInv_nil _
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
      ⟨Hj.1, Hif⟩
    have h1 : sint.nat j < ops.length := by rw [Hlen.1]; word
    have h2 : sint.nat j < xs.length := Hops.length_eq ▸ h1
    have hR := nf_forall₂_getElem Hops (sint.nat j) h1 h2
    have hjx : xs.take (sint.nat (j + W64 1)) = xs.take (sint.nat j) ++ [xs[sint.nat j]] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one,
        List.getElem?_eq_getElem h2]
      rfl
    generalize xs[sint.nat j] = pj at hR hjx
    obtain ⟨x, y⟩ := pj
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) ops dq (ops[sint.nat j]) Hj.1 $$ [Hs] as Hs
    · isplit
      · iexact Hs
      · ipureintro; exact List.getElem?_eq_getElem h1
    (try wp_auto)
    rw [hR.1]
    (try wp_auto)
    rw [hR.2]
    (try wp_auto)
    wp_apply wp_isWrite
    have hnone : nfWriteRV s.st0'.rv' (x, y) = none →
        NfInv s.st0'.rv' (xs.take (sint.nat (j + W64 1))) W mv := fun h => hjx ▸ nfInv_none Hinv h
    rcases hiw : isWriteL x with _ | _
    · (try wp_auto)
      have hn : nfWriteRV s.st0'.rv' (x, y) = none := by simp [nfWriteRV, hiw]
      wp_for_post
      iframe
      iexists j + W64 1, _, _, _
      iframe
      ipureintro
      exact ⟨hnone hn, by word, by word⟩
    (try wp_auto)
    wp_if_destruct
    · wp_if_destruct
      · have hw : nfWriteRV s.st0'.rv' (x, y) = some y.RV' := by
          simp only [nfWriteRV, hiw]
          rw [if_pos]
          exact ⟨trivial, ‹y.Err' = W64 0›, by word⟩
        wp_apply (wp_mapInsert go.uint64 wm W y.RV' true) $$ Hwm as Hwm
        simp only [hmax]
        wp_auto
        wp_if_destruct
        all_goals
          wp_for_post
          iframe
          iexists j + W64 1, _, _, _
          iframe
          ipureintro
          refine ⟨?_, by word, by word⟩
          rw [hjx]
          have := nfInv_some Hinv hw
          first | (rw [if_pos (by word)] at this; exact this) | (rw [if_neg (by word)] at this; exact this)
      · have hn : nfWriteRV s.st0'.rv' (x, y) = none := by
          simp only [nfWriteRV, hiw]
          rw [if_neg]
          rintro ⟨-, -, h⟩; exact Hif (by word)
        wp_for_post
        iframe
        iexists j + W64 1, _, _, _
        iframe
        ipureintro
        exact ⟨hnone hn, by word, by word⟩
    · have hn : nfWriteRV s.st0'.rv' (x, y) = none := by
        simp only [nfWriteRV, hiw]
        rw [if_neg]
        rintro ⟨-, h, -⟩; exact Hif h
      wp_for_post
      iframe
      iexists j + W64 1, _, _, _
      iframe
      ipureintro
      exact ⟨hnone hn, by word, by word⟩
  · have hfull : xs.take (sint.nat j) = xs :=
      List.take_of_length_le (by rw [← Hops.length_eq, Hlen.1]; word)
    rw [hfull] at Hinv
    (try wp_auto)
    wp_apply (wp_map_len_lt (t := go.uint64.MapType go.bool) wm W _) $$ Hwm as ⟨Hwm, %Hsz⟩
    (try wp_auto)
    wp_if_destruct
    · have hsz : GMap.size W = uint.nat mv - uint.nat s.st0'.rv' := by
        have := Hinv.2.1
        have h := congrArg uint.nat ‹W64 ↑W.size = mv - s.st0'.rv'›
        rw [show uint.nat (W64 ↑W.size) = W.size by word] at h
        rw [h]; word
      wp_apply wp_HistoryRevs sl ops xs dq Hops Hok Hcost $$ [Hs] as %r ⟨Hs, %R, HR, %HRa⟩
      · iframe
      unfold revsOwn
      icases HR with ⟨#Ha, %Hsort, -, -⟩
      ihave %Halen := ownSlice_len $$ Ha
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        iapply HΦ
        iframe
        ipureintro
        intro _
        have hnil : R.anchors = [] := List.eq_nil_of_length_eq_zero (by rw [Halen.1]; word)
        exact ⟨mv, noForeignOk_of Hinv hsz HRa.2 (by simp [hnil])⟩
      · (try wp_auto)
        have hne : R.anchors ≠ [] := fun h => Hif (by rw [h] at Halen; simp at Halen; word)
        have hb : 0 ≤ sint.Z (r.anchors'.len - W64 1) ∧
            sint.Z (r.anchors'.len - W64 1) < sint.Z r.anchors'.len := by
          constructor <;> word
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index r.anchors' (sint.Z (r.anchors'.len - W64 1)) R.anchors
          DFrac.discard (R.anchors.getLast hne) hb.1 $$ [Ha] as -
        · isplit
          · iexact Ha
          · ipureintro
            rw [List.getLast_eq_getElem, ← List.getElem?_eq_getElem]
            congr 1; word
        (try wp_auto)
        iapply HΦ
        iframe
        ipureintro
        intro hle
        refine ⟨mv, noForeignOk_of Hinv hsz HRa.2 (fun a ha => ?_)⟩
        have := le_getLast_of_sorted Hsort hne a ha
        have : uint.nat (R.anchors.getLast hne) ≤ uint.nat mv := by
          simp at hle; word
        omega
    · (try wp_auto)
      iapply HΦ
      iframe
      ipureintro
      intro h; cases h

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
