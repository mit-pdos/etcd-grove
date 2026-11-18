/- Lean-first (no Rocq counterpart). The proof of `runner.newVal`: proved.

The outline: the counter; `choose(MaxVal + 1)`; the padding's loop; `itoa`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.itoa

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (S1b, 2026-11-17) A number below `10 ^ k` has at most `k` decimal digits. -/
private theorem decDigits_length_le : ∀ (k n : Nat), n < 10 ^ k → (decDigits n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rw [decDigits]; simp
  | k + 1, n, h => by
    rw [decDigits]
    split
    · simp
    · simp only [List.length_append, List.length_singleton]
      have := decDigits_length_le k (n / 10) (by rw [Nat.pow_succ] at h; omega)
      omega

private theorem itoaM_length_le (n : Nat) (h : n < 2 ^ 64) : (itoaM n).length ≤ 20 := by
  unfold itoaM
  split
  · decide
  · exact decDigits_length_le 20 n (by omega)

theorem runner.newVal.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_itoa : itoa.spec (GF := GF) (hG := hG)) :
    runner.newVal.spec (GF := GF) (hG := hG) := by
  intro x cfg n h0 h1 hm0 hm1
  have hn1 : 0 ≤ sint.Z (n + W64 1) := by word
  wp_start as ⟨#Hcfg, Hv⟩
  icases typedPointsto_split _ _ _ $$ Hcfg with #Hcfgf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfgf
  wp_auto
  wp_apply wp_choose (cfg.MaxVal' + W64 1) as %c %Hc
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) c) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; exact Hc.1
  (try wp_auto)
  rename_i ui
  ihave %Hsn := ownSlice_len $$ Hsl
  ihave HI : (∃ (j u : w64) (bs : List w8),
      "i" ∷ i_ptr ↦ j ∗ "ui" ∷ ui ↦ u ∗ "Hsl" ∷ sl ↦* bs ∗ "pad" ∷ pad_ptr ↦ sl ∗
      "x" ∷ x_ptr ↦ x ∗ "Hv" ∷ rF go!"vals" x ↦ (n + W64 1) ∗
      "res" ∷ «$res0_ptr» ↦ (zero_val GoString) ∗
      "Hpost" ∷ (∀ v : GoString, rF go!"vals" x ↦ (n + W64 1) ∗ ⌜v.length ≤ etcdKeyMax⌝ -∗ Φ #v) ∗
      "%Hj" ∷ ⌜bs.length = sint.nat sl.len ∧ 0 ≤ sint.Z j⌝ : IProp GF) $$ [-Hcap]
  · iexists W64 0, _, _
    iframe
    ipureintro; constructor
    · simp only [List.length_replicate] at Hsn ⊢; exact Hsn.1
    · word
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z sl.len
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hjl : (sint.Z j).toNat < bs.length := by
      have h4 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have := Hj.1; omega
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.2, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) bs (DFrac.own 1) (bs[(sint.Z j).toNat]'hjl)
      Hj.2 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact List.getElem?_eq_getElem hjl
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply (wp_store_slice_index (V := w8) sl (sint.Z j) bs (W8 120)) $$ [Hsl] as Hsl
    · iframe; ipureintro; omega
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, j, _
    iframe
    ipureintro; constructor
    · rw [List.length_set]; exact Hj.1
    · word
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_apply wp_itoa (n + W64 1) hn1
    (try wp_auto)
    wp_apply (wp_bytes_to_string sl bs (DFrac.own 1)) $$ [Hsl] as Hsl
    · iexact Hsl
    (try wp_auto)
    iapply Hpost
    iframe
    ipureintro
    have h63 : sint.Z (n + W64 1) < 2 ^ 63 := by word
    have hil := itoaM_length_le (sint.nat (n + W64 1)) (by
      show (sint.Z (n + W64 1)).toNat < 2 ^ 64; omega)
    have hc1 : sint.Z c < sint.Z cfg.MaxVal' + 1 := by
      have := Hc.2.1 (by word); word
    have hc0 : 0 ≤ sint.Z c := Hc.1
    have hbs : bs.length = sint.nat c := by
      rw [Hj.1]; simp only [List.length_replicate] at Hsn; rw [← Hsn.1]
    simp only [List.length_append]
    have hv1 : (go!"v" : GoString).length = 1 := by decide
    have hcn : sint.nat c ≤ 2 ^ 20 := by show (sint.Z c).toNat ≤ 2 ^ 20; omega
    unfold etcdKeyMax; omega

end proof

end mvccfull
end EtcdGrove
end Perennial
