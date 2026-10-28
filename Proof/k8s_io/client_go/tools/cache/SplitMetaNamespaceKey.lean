/-
Proof of `Spec/k8s_io/client_go/tools/cache/SplitMetaNamespaceKey.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.SplitMetaNamespaceKey
public import Perennial.Proof.strings.Link
public import Perennial.Proof.fmt.Link

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

theorem SplitMetaNamespaceKey.wp_proof : SplitMetaNamespaceKey.spec (GF := GF) (hG := hG) := by
  intro key
  wp_start
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply (strings.wp_Split key go!"/" (by simp)) as %sl ⟨Hsl, -⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  unfold splitKey
  generalize hparts : strings.split key go!"/" = parts at *
  match parts, Hlen with
  | [], _ => exact absurd hparts (strings.split_ne_nil _ _)
  | [n], Hlen =>
    have hl : sl.len = W64 1 := by simp at Hlen; word
    simp only [hl, _root_.decide_true]
    wp_auto
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by rw [hl]; decide
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) [n] _ n (by decide) $$ [Hsl] as Hsl
    · isplit
      · iexact Hsl
      · ipureintro; rfl
    wp_auto
    iapply HΦ; ipureintro; simp
  | [a, n], Hlen =>
    have hl : sl.len = W64 2 := by simp at Hlen; word
    have hl1 : ¬ sl.len = W64 1 := by rw [hl]; decide
    simp only [hl1, decide_false]
    wp_auto
    rw [hl]
    wp_auto
    have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by rw [hl]; decide
    have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len := by rw [hl]; decide
    simp only [hb0, hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) [a, n] _ a (by decide) $$ [Hsl] as Hsl
    · isplit
      · iexact Hsl
      · ipureintro; rfl
    wp_auto
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 1)) [a, n] _ n (by decide) $$ [Hsl] as Hsl
    · isplit
      · iexact Hsl
      · ipureintro; rfl
    wp_auto
    iapply HΦ; ipureintro; simp
  | a :: b :: c :: rest, Hlen =>
    have hlen3 : 3 ≤ sint.Z sl.len := by
      have h := Hlen.1
      simp only [List.length_cons] at h
      have : (sint.Z sl.len).toNat = sint.nat sl.len := rfl
      omega
    have hl1 : ¬ sl.len = W64 1 := by intro h; rw [h] at hlen3; exact absurd hlen3 (by decide)
    have hl2 : ¬ sl.len = W64 2 := by intro h; rw [h] at hlen3; exact absurd hlen3 (by decide)
    simp only [hl1, decide_false]
    wp_auto
    simp only [hl2, decide_false]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    wp_auto
    wp_apply (fmt.wp_Errorf _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string key []
      _root_.Perennial.fmt.ArgsWf.nil)) $$ [$Hl1] as %err #Herr
    iapply HΦ; ipureintro; simp

end proof

end cache
end EtcdGrove
end Perennial
