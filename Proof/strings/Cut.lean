/-
`strings.Cut`'s spec (`Spec/strings/Cut.lean`), assumed: Perennial translates `strings.Cut` as a
name only at the pin (`b3f2fc485`). Perennial's `lean` proves it at `ed1955557` and after
(`Perennial/Proof/strings/Cut.lean`, from `strings-cut-lastindex`), over a spec that implies this
one: the same result (`internal.stringslite.cut s sep`, the first occurrence by `internal.bytealg.index`, the same value as `strings.cut`), under a
precondition this one's implies. Lean-first.
-/
module

public import Spec.strings.Cut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust-boundary axiom, interim**: `strings.Cut` meets its spec. Interim, retired by the
Perennial pin bump past strings-cut-lastindex (ed1955557): Perennial proves both,
`Perennial/Proof/strings/{Cut,TrimLeft}.lean`. -/
axiom strings.Cut.wp_proof : strings.Cut.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
