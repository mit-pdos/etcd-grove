/- Lean-first (no Rocq counterpart). The proof of `mmapSize`: the loop keeps `sz` a whole number of pages, from 32 KiB up, and at most `max 32768 (2 * size)`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.mmapSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

/-- The values of `mmapSize`'s doubling up to 1 GiB: the powers of two from 32 KiB. -/
def mmapPows : List Int :=
  [32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432,
    67108864, 134217728, 268435456, 536870912, 1073741824]

/-- `mmapSize`'s loop invariant: from 32 KiB, whole pages, at most twice `size`, and, if `size` is
at most 1 GiB, a power of two at most 1 GiB. -/
def mmapSizeInv (size z : w64) : Prop :=
  32768 ≤ sint.Z z ∧ sint.Z z % 4096 = 0 ∧ sint.Z z ≤ max 32768 (2 * sint.Z size) ∧
    (sint.Z size ≤ 2 ^ 30 → sint.Z z ∈ mmapPows)

theorem mmapSize_init (size : w64) : mmapSizeInv size (W64 32768) := by
  have : sint.Z (W64 32768) = 32768 := by rfl
  refine ⟨by omega, by omega, by omega, fun _ => ?_⟩
  rw [this]; simp [mmapPows]

theorem mmapSize_step (size z : w64) (Hs : sint.Z size ≤ 2 ^ 40) (Hz : mmapSizeInv size z)
    (Hif : sint.Z z < sint.Z size) : mmapSizeInv size (z * W64 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := Hz
  have h : sint.Z z < 2 ^ 40 := by omega
  have hmul : sint.Z (z * W64 2) = 2 * sint.Z z := by clear h4; word
  unfold mmapSizeInv
  rw [hmul]
  refine ⟨by omega, by omega, by omega, fun hs => ?_⟩
  have := h4 hs
  simp only [mmapPows, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  omega

theorem mmapSize_done (size z : w64) (Hz : mmapSizeInv size z) (Hif : ¬sint.Z z < sint.Z size) :
    sint.Z size ≤ sint.Z z ∧ 32768 ≤ sint.Z z ∧ sint.Z z ≤ max 32768 (2 * sint.Z size) ∧
      sint.Z z % 4096 = 0 ∧ (sint.Z size ≤ 2 ^ 30 → sint.Z z ≤ 2 ^ 30) := by
  obtain ⟨h1, h2, h3, h4⟩ := Hz
  refine ⟨by omega, h1, h3, h2, fun hs => ?_⟩
  have := h4 hs
  simp only [mmapPows, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem mmapSize.wp_proof : mmapSize.spec (GF := GF) (hG := hG) := by
  intro size
  wp_start as %Hs
  wp_auto
  ihave HI : (∃ (z : w64), "sz" ∷ sz_ptr ↦ z ∗
      "%Hz" ∷ ⌜mmapSizeInv size z⌝ : IProp GF) $$ [sz]
  · iexists W64 32768; iframe; ipureintro; exact mmapSize_init size
  wp_for HI
  wp_if_destruct
  · (try wp_auto)
    wp_for_post
    iframe
    iexists (z * W64 2)
    iframe
    ipureintro
    exact mmapSize_step size z Hs Hz Hif
  · (try wp_auto)
    iapply HΦ
    ipureintro
    exact mmapSize_done size z Hz Hif
