/-
`sort.Ints(x)` sorts the slice's elements ascending in signed order, a permutation of them (the
spec `raxos.hyp.sort.Ints.spec`, `Dsverify/Proof/raxos/Hyp.lean`), from Perennial's translation
of `sort.Ints` (`slices.Sort(x)`, go sort.go:170) and its proof `sort.wp_Ints` (over
`slices.wp_Sort` and `cmp.Less` at `int`). Until #49 step 1 (2026-11-25) a trust-boundary axiom of dsv-fix4
(`notes/axiom-review/dsv-fix4/quepaxa-misc.md`), retired by the translation.
-/
module

public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.sort.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- Perennial's linked result, at the hypothesis' statement (the file header). -/
theorem raxos.hyp.sort.Ints.wp_proof : raxos.hyp.sort.Ints.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.sort.wp_Ints

end proof

end Perennial
