/-
Lean-first (no Rocq counterpart).

The proof of `storeHash`: the revision, then each item's key, object fields and flags, mixed in
(`mix`, `strHash`: some `w64`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mix
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.strHash

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

theorem storeHash.wp_proof (wp_mix : mix.spec (GF := GF) (hG := hG))
    (wp_strHash : strHash.spec (GF := GF) (hG := hG)) :
    storeHash.spec (GF := GF) (hG := hG) := by
  intro st s
  wp_start as #Hs
  unfold storeOwn
  icases Hs with ⟨#Hit, %Hrv⟩
  ihave %Hl := ownSlice_len $$ Hit
  (try wp_auto)
  wp_apply wp_mix as %h1 -
  (try wp_auto)
  ihave HI : (∃ (j : w64) (m : w64) (iv : item), "i" ∷ i_ptr ↦ j ∗ "h" ∷ h_ptr ↦ m ∗
      "it" ∷ it_ptr ↦ iv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z st.items'.len⌝ : IProp GF) $$ [i h it]
  · iexists W64 0, _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z st.items'.len := ⟨Hj.1, Hif⟩
    list_elem s.items (sint.nat j) as w
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index st.items' (sint.Z j) s.items _ w Hj.1 $$ [Hit] as -
    · isplit
      · iexact Hit
      · ipureintro; exact Hw_lookup
    (try wp_auto)
    wp_apply wp_strHash as %h2 -
    (try wp_auto)
    rename_i o_ptr
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hf, -⟩
    imod ownSlice_persist _ _ _ $$ Hf with #Hf
    ihave %Hfl := ownSlice_len $$ Hf
    (try wp_auto)
    ihave HJ : (∃ (k : w64) (m : w64) (fv : GoString), "k" ∷ i_ptr' ↦ k ∗ "h" ∷ h_ptr ↦ m ∗
        "f" ∷ f_ptr ↦ fv ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 6⌝ : IProp GF) $$ [i' h f]
    · iexists W64 0, _, _
      iframe
      ipureintro; exact ⟨by word, by word⟩
    wp_for HJ
    wp_if_destruct
    · sorry
    · sorry
  · iapply HΦ
    itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
