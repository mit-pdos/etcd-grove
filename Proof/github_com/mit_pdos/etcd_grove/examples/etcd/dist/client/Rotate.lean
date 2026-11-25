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
  rfl

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
  wp_auto
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
    have hidx : sint.Z ((i + W64 (j : Int)).srem (W64 (xsL.length : Int))) =
        ((sint.nat i + j) % xsL.length : Nat) := by
      sorry
    sorry
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
