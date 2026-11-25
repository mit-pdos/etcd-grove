/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `t.UTC()` on a `time.Time` value returns some `Time` (the spec `raxos.hyp.time.Time.UTC.spec`,
`Dsverify/Proof/raxos/Hyp.lean`). Perennial leaves `Time.UTC` untranslated
(`Perennial/Code/time.toml`). Go's `time.go`: `func (t Time) UTC() Time { t.setLoc(&utcLoc);
return t }`, and `setLoc` on a value receiver's copy writes only that copy: no panic, no state. The
premise `raxos.hyp.UtcHyp` of QuePaxa's statement until dsv-fix4, its field verbatim. Review: `notes/axiom-review/dsv-fix4/quepaxa-misc.md`.
-/
module

public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom raxos.hyp.time.Time.UTC.wp_proof : raxos.hyp.time.Time.UTC.spec (GF := GF) (hG := hG)

end ax

end Perennial
