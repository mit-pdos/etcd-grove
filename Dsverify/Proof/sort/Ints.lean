/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `sort.Ints(x)` sorts the slice's elements ascending in signed order, a permutation of them (the
spec `raxos.hyp.sort.Ints.spec`, `Dsverify/Proof/raxos/Hyp.lean`). Perennial leaves `sort.Ints`
untranslated (`Perennial/Code/sort.toml`). Go's `sort.go` (go1.27.3): `func Ints(x []int) {
intsImpl(x) }`, `intsImpl` is `slices.Sort`, pdqsort on `cmp.Less` of `int`s: it permutes the
elements by swaps within the slice and ends sorted; no panic. The premise `raxos.hyp.SortHyp` of
QuePaxa's statement until dsv-fix4, its field verbatim. Review: `notes/axiom-review/dsv-fix4/quepaxa-misc.md`.
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
axiom raxos.hyp.sort.Ints.wp_proof : raxos.hyp.sort.Ints.spec (GF := GF) (hG := hG)

end ax

end Perennial
