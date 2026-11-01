/- Lean-first (no Rocq counterpart). The proof of `mmapSize`: the loop keeps `sz` a whole number of pages, from 32 KiB up, and at most `max 32768 (2 * size)`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.mmapSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

theorem mmapSize_step (size z : w64) (Hs : sint.Z size ≤ 2 ^ 40)
    (Hz : 32768 ≤ sint.Z z ∧ sint.Z z % 4096 = 0 ∧ sint.Z z ≤ max 32768 (2 * sint.Z size))
    (Hif : sint.Z z < sint.Z size) :
    32768 ≤ sint.Z (z * W64 2) ∧ sint.Z (z * W64 2) % 4096 = 0 ∧
      sint.Z (z * W64 2) ≤ max 32768 (2 * sint.Z size) := by
  have h : sint.Z z < 2 ^ 40 := by omega
  have hmul : sint.Z (z * W64 2) = 2 * sint.Z z := by word
  rw [hmul]; omega

theorem mmapSize_done (size z : w64)
    (Hz : 32768 ≤ sint.Z z ∧ sint.Z z % 4096 = 0 ∧ sint.Z z ≤ max 32768 (2 * sint.Z size))
    (Hif : ¬sint.Z z < sint.Z size) :
    sint.Z size ≤ sint.Z z ∧ 32768 ≤ sint.Z z ∧ sint.Z z ≤ max 32768 (2 * sint.Z size) ∧
      sint.Z z % 4096 = 0 := by
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
      "%Hz" ∷ ⌜32768 ≤ sint.Z z ∧ sint.Z z % 4096 = 0 ∧
        sint.Z z ≤ max 32768 (2 * sint.Z size)⌝ : IProp GF) $$ [sz]
  · iexists W64 32768; iframe; ipureintro; word
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
