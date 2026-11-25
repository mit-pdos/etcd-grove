/-
`t.UTC()` on a `time.Time` value returns some `Time` (the spec `raxos.hyp.time.Time.UTC.spec`,
`Dsverify/Proof/raxos/Hyp.lean`), from Perennial's translation of `Time.UTC` and `Time.setLoc`
(`t.setLoc(&utcLoc); return t`, go time.go:1368) and its proof `time.Time.wp_UTC`. Until #49 step 1 (2026-11-25) a trust-boundary axiom of dsv-fix4
(`notes/axiom-review/dsv-fix4/quepaxa-misc.md`), retired by the translation.
-/
module

public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- Perennial's linked result, at the hypothesis' statement (the file header). -/
theorem raxos.hyp.time.Time.UTC.wp_proof : raxos.hyp.time.Time.UTC.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.time.Time.wp_UTC

end proof

end Perennial
