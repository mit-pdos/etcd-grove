/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/Rotate.lean`. Lean-first; N7-kv.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Rotate
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

/-- Go's `%` on non-negative `int`s is the mathematical remainder. -/
theorem srem_of_nonneg (a b : w64) (ha : 0 ≤ sint.Z a) :
    sint.Z (a.srem b) = sint.Z a % sint.Z b := by
  rw [show sint.Z (a.srem b) = (a.srem b).toInt from rfl, BitVec.toInt_srem,
    Int.tmod_eq_emod_of_nonneg ha]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem Rotate.wp_proof : Rotate.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ _ xs dq xsL i
  wp_start as ⟨Hxs, %Hi⟩
  wp_auto
  ihave %Hxl := ownSlice_len _ _ _ $$ Hxs
  wp_apply (wp_slice_make2 (V := V) (t := T) xs.len) as %out ⟨Hout, -⟩
  · ipureintro; word
  ihave HI : (∃ (j : Nat) (outL : List V),
      "j" ∷ j_ptr ↦ W64 j ∗ "Hout" ∷ out ↦* outL ∗ "Hxs" ∷ xs ↦*{dq} xsL ∗
      "%Hj" ∷ ⌜j ≤ xsL.length ∧ outL.length = xsL.length ∧
        ∀ m, m < j → outL[m]? = (rotateL xsL (sint.nat i))[m]?⌝ : IProp GF)
    $$ [j Hout Hxs]
  · iexists 0, _
    iframe
    ipureintro
    refine ⟨by omega, by simp; word, fun m hm => by omega⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hj3⟩ := Hj
  wp_if_destruct
  · have hj : j < xsL.length := by word
    have hk : 0 < xsL.length := by omega
    have hxlen : sint.Z xs.len = (xsL.length : Int) := by word
    have hlen0 : ¬ sint.Z xs.len = 0 := by omega
    have hsum : 0 ≤ sint.Z (i + W64 (j : Int)) ∧
        sint.Z (i + W64 (j : Int)) = ((sint.nat i + j : Nat) : Int) := by
      constructor <;> word
    have hidx : sint.Z ((i + W64 (j : Int)).srem xs.len) = ((sint.nat i + j) % xsL.length : Nat) := by
      rw [srem_of_nonneg _ _ hsum.1, hsum.2, hxlen, Int.natCast_emod]
    simp only [hlen0, ↓reduceIte]
    wp_auto
    have hm : (sint.nat i + j) % xsL.length < xsL.length := Nat.mod_lt _ hk
    have hb1 : 0 ≤ sint.Z ((i + W64 (j : Int)).srem xs.len) := by rw [hidx]; omega
    have hb2 : sint.Z ((i + W64 (j : Int)).srem xs.len) < sint.Z xs.len := by rw [hidx, hxlen]; omega
    simp only [hb1, hb2, and_self, ↓reduceIte]
    obtain ⟨x, hx⟩ : ∃ x, xsL[(sint.nat i + j) % xsL.length]? = some x :=
      ⟨_, List.getElem?_eq_getElem hm⟩
    wp_apply (wp_load_slice_index xs _ xsL dq x hb1) $$ [Hxs] as Hxs
    · iframe
      ipureintro
      rw [hidx, Int.toNat_natCast]
      exact hx
    ihave %Hol := ownSlice_len _ _ _ $$ Hout
    have hj0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    have hjo : sint.Z (W64 (j : Int)) < sint.Z out.len := by word
    simp only [hj0, hjo, and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index out (sint.Z (W64 (j : Int))) outL x) $$ [Hout] as Hout
    · iframe
      ipureintro
      constructor <;> word
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    have hwj : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by
      rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega, W64, W64, W64, BitVec.ofInt_add]
    rw [hsj]
    wp_for_post
    iframe
    iexists (j + 1), outL.set j x
    rw [hwj]
    iframe
    ipureintro
    refine ⟨hj, by rw [List.length_set]; exact Hj2, fun m hm' => ?_⟩
    rw [List.getElem?_set]
    by_cases hmj : m = j
    · subst hmj
      rw [if_pos rfl, if_pos (by omega)]
      simp only [rotateL, List.getElem?_map, List.getElem?_range hj, Option.map_some]
      rw [getElem!_pos xsL _ hm, ← hx]
      simp [List.getElem?_eq_getElem hm]
    · rw [if_neg (Ne.symm hmj)]
      exact Hj3 m (by omega)
  · have hj : j = xsL.length := by word
    subst hj
    iapply HΦ
    iframe
    have : outL = rotateL xsL (sint.nat i) := by
      apply List.ext_getElem?
      intro m
      by_cases hm : m < xsL.length
      · exact Hj3 m hm
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [rotateL_length]; omega)]
    rw [this]
    iframe
