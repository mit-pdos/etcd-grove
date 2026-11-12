/-
The proof of `Spec/github_com/mit_pdos/gokv/trusted_proph/ResolveBytes.lean`. Lean-first (no Rocq
counterpart): the model's conversion (`wp_bytes_to_string`), then GooseLang's `ResolveProph`
(`wp_resolve_proph`).
-/
module

public import Spec.github_com.mit_pdos.gokv.trusted_proph.ResolveBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.trusted_proph.Assumptions]

theorem github_com.mit_pdos.gokv.trusted_proph.ResolveBytes.wp_proof :
    github_com.mit_pdos.gokv.trusted_proph.ResolveBytes.spec (GF := GF) (hG := hG) := by
  intro p pvs sl s dq
  wp_start as ⟨Hp, Hsl⟩
  wp_apply wp_bytes_to_string sl s dq $$ Hsl as Hsl
  wp_apply wp_resolve_proph p pvs #s $$ Hp as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hpvs

end proof

end Perennial
