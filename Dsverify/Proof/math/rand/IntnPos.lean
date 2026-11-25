/-
The package-level `rand.Intn(n)` for a positive `n`, in the form the kits call it (the bound a
premise of the theorem, `math/rand`'s `isPkgInit` the precondition): Perennial's proved
`math.rand.wp_Intn` (`Perennial/Proof/math/rand/Intn.lean`, over the trusted models `globalRand`
and `runtime_rand`), no hypothesis.

(Until 2026-11-24, math-rand-isinit: the field `Intn` of the hypothesis classes `math.rand.Hyps`
(rabia, swiftpaxos) and `raxos.hyp.RandHyp` (QuePaxa). Since Perennial 47ec64a9d translates `Intn`,
those fields were unsatisfiable while `math/rand`'s `isPkgInit` was the main tree's `True`:
notes/math-rand-isinit.md.)
-/
module

public import Perennial.Proof.math.rand.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

/-- `rand.Intn(n)` for `0 < n`: some `x` in `[0, n)` (Perennial's `math.rand.wp_Intn`). -/
theorem math.rand.wp_Intn_pos (n : w64) (hn : 0 < sint.Z n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.Intn)) (Val #n))
    {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }} := by
  iintro %Φ Hpkg HΦ
  iapply (math.rand.wp_Intn (GF := GF) (hG := hG) n) $$ [Hpkg] HΦ
  iframe Hpkg
  ipureintro
  exact hn

end proof

end Perennial
