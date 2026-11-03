/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__isWrite.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__isWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.isWrite.wp_proof : Op.isWrite.spec (GF := GF) (hG := hG) := by
  intro opv t
  obtain ⟨n, hn⟩ : ∃ n, sizeOf t = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing opv t with
  | ind n ih =>
  cases t with
  | leaf o =>
    wp_start as #Hat
    iunfold opTAtC at Hat
    icases Hat with ⟨#Hf, %Ht⟩
    iunfold opFullAt at Hf
    icases Hf with ⟨-, -, %Hf2, -, -⟩
    obtain ⟨ht, -⟩ := Hf2
    wp_auto
    rw [ht, decide_eq_false Ht]
    wp_auto
    rw [ht, show (!decide (o.t = W64 1)) = decide (o.t ≠ W64 1) by simp]
    simp only [OpT.isWrite]
    iapply HΦ
    itrivial
  | txn o cs ts es =>
    wp_start as #Hat
    iunfold opTAtC at Hat
    icases Hat with ⟨#Hf, %Ht, #Hcs, %tvs, %evs, #Htv, #Hev, -, #Htl, #Hel⟩
    iunfold opFullAt at Hf
    icases Hf with ⟨-, -, %Hf2, -, -⟩
    obtain ⟨ht, -⟩ := Hf2
    wp_auto
    rw [ht, Ht]
    wp_auto
    ihave %Htll := opListAtC_length false tvs ts $$ Htl
    ihave %Hsll := ownSlice_len $$ Htv
    ihave IH : iprop(∃ (k : w64) (ov : go_etcd_io.etcd.client.v3.Op),
        "i" ∷ i_ptr ↦ k ∗ "tOp" ∷ tOp_ptr ↦ ov ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (tvs.length : Int)⌝ ∗
        "%Hw" ∷ ⌜OpT.isWriteL (ts.take (sint.nat k)) = false⌝) $$ [i tOp]
    · iexists W64 0, _
      simp only [named]
      iframe
      simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
      isplitl []
      · ipureintro; constructor <;> word
      ipureintro; rfl
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat k < tvs.length := by word
      obtain ⟨v, Hvi⟩ : ∃ v, tvs[sint.nat k]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨t, Hti⟩ : ∃ t, ts[sint.nat k]? = some t :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Htll]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z opv.thenOps'.len := ⟨Hk.1, by word⟩
      icases ownSlice_elem_acc (sint.Z k) v opv.thenOps' DFrac.discard tvs Hk.1 Hvi $$ Htv
        with ⟨#Hve0, -⟩
      ihave ⟨#Hvt, -⟩ := opListAtC_get false tvs ts _ v t Hvi Hti $$ Htl
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_method_call
      wp_auto
      have hsz : sizeOf t < n := by
        rw [← hn]
        have := List.sizeOf_lt_of_mem (List.mem_of_getElem? Hti)
        simp only [OpT.txn.sizeOf_spec]; omega
      wp_apply (ih (sizeOf t) hsz v t rfl) $$ []
      · iframe #
      cases Hif : OpT.isWrite t
      · wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, v
        simp only [named]
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        ipureintro
        rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Hti]
        simp [OpT.isWriteL_any] at Hw ⊢
        exact ⟨Hw, by simpa using Hif⟩
      · wp_auto
        wp_for_post
        have hw : (OpT.txn o cs ts es).isWrite = true := by
          simp only [OpT.isWrite, OpT.isWriteL_any, Bool.or_eq_true, List.any_eq_true]
          exact Or.inl ⟨t, List.mem_of_getElem? Hti, Hif⟩
        rw [hw]
        iapply HΦ
        itrivial
    · have Hts : OpT.isWriteL ts = false := by
        have : sint.nat k = ts.length := by rw [← Htll]; word
        rw [this, List.take_length] at Hw; exact Hw
      clear Hif Hw Hk
      ihave %Hell := opListAtC_length false evs  es $$ Hel
      ihave %Hsel := ownSlice_len $$ Hev
      ihave IH : iprop(∃ (k : w64) (ov : go_etcd_io.etcd.client.v3.Op),
          "i" ∷ i_ptr ↦ k ∗ "tOp" ∷ tOp_ptr ↦ ov ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (evs.length : Int)⌝ ∗
          "%Hw" ∷ ⌜OpT.isWriteL (es.take (sint.nat k)) = false⌝) $$ [i tOp]
      · iexists W64 0, _
        simp only [named]
        iframe
        simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
        isplitl []
        · ipureintro; constructor <;> word
        ipureintro; rfl
      wp_for IH
      wp_if_destruct
      · have Hlt : sint.nat k < evs.length := by word
        obtain ⟨v, Hvi⟩ : ∃ v, evs[sint.nat k]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨t, Hei⟩ : ∃ t, es[sint.nat k]? = some t :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hell]; exact Hlt)⟩
        have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z opv.elseOps'.len := ⟨Hk.1, by word⟩
        icases ownSlice_elem_acc (sint.Z k) v opv.elseOps' DFrac.discard evs Hk.1 Hvi $$ Hev
          with ⟨#Hve0, -⟩
        ihave ⟨#Hvt, -⟩ := opListAtC_get false evs  es _ v t Hvi Hei $$ Hel
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_method_call
        wp_auto
        have hsz : sizeOf t < n := by
          rw [← hn]
          have := List.sizeOf_lt_of_mem (List.mem_of_getElem? Hei)
          simp only [OpT.txn.sizeOf_spec]; omega
        wp_apply (ih (sizeOf t) hsz v t rfl) $$ []
        · iframe #
        cases Hif : OpT.isWrite t
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, v
          simp only [named]
          iframe
          isplitl []
          · ipureintro; constructor <;> word
          ipureintro
          rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Hei]
          simp [OpT.isWriteL_any] at Hw ⊢
          exact ⟨Hw, by simpa using Hif⟩
        · wp_auto
          wp_for_post
          have hw : (OpT.txn o cs ts es).isWrite = true := by
            simp only [OpT.isWrite, OpT.isWriteL_any, Bool.or_eq_true, List.any_eq_true]
            exact Or.inr ⟨t, List.mem_of_getElem? Hei, Hif⟩
          rw [hw]
          iapply HΦ
          itrivial
      · have Hes : OpT.isWriteL es = false := by
          have : sint.nat k = es.length := by rw [← Hell]; word
          rw [this, List.take_length] at Hw; exact Hw
        have hw : (OpT.txn o cs ts es).isWrite = false := by
          simp only [OpT.isWrite, Hts, Hes, Bool.or_false]
        rw [hw]
        iapply HΦ
        itrivial

end proof

end EtcdGrove
end Perennial
