/- Lean-first (no Rocq counterpart).

`dirFits.spec` proved: the loop's `run` is `tailRun` of the bytes read, under 256 after each byte so
far (`Proof/runtime/RootClaim.lean`'s `dirFits_iff_tailRun`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.dirFits
public import Proof.runtime.RootClaim
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem dirFits.wp_proof : dirFits.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hpl
  try wp_auto
  wp_if_destruct
  · -- `len(r) >= 3800`
    iapply HΦ
    ipureintro
    constructor
    · intro h; cases h
    · intro hd
      have h1 := hd.1
      revert Hif; word
  · have hlt : r.length < 3800 := by revert Hif; word
    ihave HI : (∃ (i run : w64), "i" ∷ i_ptr ↦ i ∗ "run" ∷ run_ptr ↦ run ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ r.length ∧ 0 ≤ sint.Z run ∧ sint.Z run ≤ sint.Z i ∧
          sint.nat run = tailRun (r.take (sint.nat i)) ∧
          ∀ m, m ≤ sint.nat i → tailRun (r.take m) < 256⌝ : IProp GF) $$ [i run]
    · iexists _, _
      iframe
      ipureintro
      rw [show sint.nat (W64 0) = 0 from rfl]
      refine ⟨by decide, Nat.zero_le _, by decide, by decide, rfl, fun m hm => ?_⟩
      have : m = 0 := by omega
      subst this
      rw [List.take_zero]
      exact (by decide : tailRun [] < 256)
    wp_for HI
    obtain ⟨Hi0, Hik, Hr0, Hri, Hrun, Hall⟩ := Hk
    try (wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-)
    try wp_auto
    wp_if_destruct
    · -- an iteration: the byte `r[i]`
      have hk : sint.nat i < r.length := by revert Hif; word
      obtain ⟨c, hpc⟩ : ∃ c, r[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hk⟩
      try simp only [show (0 : Int) ≤ sint.Z i from Hi0, ↓reduceIte, hpc]
      try wp_auto
      have hts := tailRun_take_succ r (sint.nat i) c hpc
      have hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by revert Hik hlt; word
      wp_if_destruct
      · -- a `/`: the run starts again
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        rw [hsucc]
        have hc : (W8 47 : w8) = Fs.slashB := by decide
        rw [hts, if_pos hc]
        refine ⟨by word, by omega, by word, by word, by word, fun m hm => ?_⟩
        rcases Nat.lt_or_ge m (sint.nat i + 1) with hlt' | hge
        · exact Hall m (by omega)
        · have : m = sint.nat i + 1 := by omega
          subst this; rw [hts, if_pos hc]; omega
      · have hc : c ≠ Fs.slashB := by
          rw [show Fs.slashB = (W8 47 : w8) by decide]; exact Hif
        rw [if_neg hc] at hts
        try wp_auto
        wp_if_destruct
        · -- the run reaches 256: no
          wp_for_post
          iapply HΦ
          ipureintro
          constructor
          · intro h; cases h
          · intro hd
            have h256 := ((dirFits_iff_tailRun r).1 hd).2 (sint.nat i + 1) (by omega)
            rw [hts] at h256
            revert Hif Hrun; word
        · wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro
          rw [hsucc, hts]
          refine ⟨by word, by omega, by word, by revert Hif; word, by revert Hrun Hif; word,
            fun m hm => ?_⟩
          rcases Nat.lt_or_ge m (sint.nat i + 1) with hlt' | hge
          · exact Hall m (by omega)
          · have : m = sint.nat i + 1 := by omega
            subst this; rw [hts]; revert Hif Hrun; word
    · -- the end: every prefix's run under 256
      have hend : sint.nat i = r.length := by revert Hif Hik; word
      iapply HΦ
      ipureintro
      constructor
      · intro _
        exact (dirFits_iff_tailRun r).2 ⟨hlt, fun m hm => Hall m (by omega)⟩
      · intro _; rfl

end proof

end mvccrand
end EtcdGrove
end Perennial
