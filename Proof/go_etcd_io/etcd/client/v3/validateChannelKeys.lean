/-
Proof of `Spec/go_etcd_io/etcd/client/v3/validateChannelKeys.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.validateChannelKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem validateChannelKeys.wp_proof
    (wp_validateChannelKey : validateChannelKey.spec (GF := GF) (hG := hG)) :
    validateChannelKeys.spec (GF := GF) (hG := hG) := by
  intro sl dq ks
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : (∃ (n : w64) (kv : GoString),
      "i" ∷ i_ptr ↦ n ∗ "key" ∷ key_ptr ↦ kv ∗
      "Hsl" ∷ sl ↦*{dq} ks ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        ∀ j < sint.nat n, ∀ k : GoString, ks[j]? = some k → k ≠ go!"" ∧ k ≠ go!"default"⌝ :
      IProp GF) $$ [i key Hsl]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hn0, hnl, hall⟩ := Hn
    have hlt : sint.nat n < ks.length := by have := Hlen.1; word
    list_elem ks (sint.nat n) as x
    simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) ks dq x hn0 $$ [$Hsl] as Hsl
    · ipureintro; exact Hx_lookup
    wp_apply wp_validateChannelKey x as %err Herr
    by_cases hx : x = go!"" ∨ x = go!"default"
    · ihave Herr' : (∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗
        go_etcd_io.etcd.cache.v3.errorStringSpec e) $$ [Herr]
      · simp only [hx, ↓reduceIte]
        iexact Herr
      icases Herr' with ⟨%e, %He, #HeS⟩
      subst He
      wp_auto
      wp_for_post
      iapply HΦ
      iframe Hsl
      have hnot : ¬ (∀ k ∈ ks, k ≠ go!"" ∧ k ≠ go!"default") := by
        intro hall'
        have hmem : x ∈ ks := List.mem_of_getElem? Hx_lookup
        have ⟨h1, h2⟩ := hall' x hmem
        rcases hx with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
      simp only [hnot, ↓reduceIte]
      iexists e
      iframe HeS
      ipureintro; rfl
    · ihave Herr' : ⌜err = GoInterface.nil⌝ $$ [Herr]
      · simp only [hx, ↓reduceIte]
        iexact Herr
      icases Herr' with %He
      subst He
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, x
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj k hjk
      have hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hsucc] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjlt | rfl
      · exact hall j hjlt k hjk
      · rw [Hx_lookup] at hjk
        injection hjk with hjk
        subst hjk
        exact not_or.1 hx
  · iapply HΦ
    iframe Hsl
    obtain ⟨hn0, hnl, hall⟩ := Hn
    have hall' : ∀ k ∈ ks, k ≠ go!"" ∧ k ≠ go!"default" := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
      have hlen_eq : sint.nat n = ks.length := by have := Hlen.1; word
      exact hall j (by omega) _ (List.getElem?_eq_getElem hj)
    rw [if_pos hall']
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
