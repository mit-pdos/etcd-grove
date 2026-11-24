/-
`strings.TrimLeft`'s spec (`Spec/strings/TrimLeft.lean`), assumed: Perennial translates `strings.TrimLeft` as a
name only at the pin (`b3f2fc485`). Perennial's `lean` proves it at `ed1955557` and after
(`Perennial/Proof/strings/TrimLeft.lean`, from `strings-cut-lastindex`), over a spec that implies this
one: the same result (`strings.trimLeft`, the same definition), under a
precondition this one's implies. Lean-first.
-/
module

public import Spec.strings.TrimLeft

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust-boundary axiom, interim**: `strings.TrimLeft` meets its spec. Interim, retired by the
Perennial pin bump past strings-cut-lastindex (ed1955557): Perennial proves both,
`Perennial/Proof/strings/{Cut,TrimLeft}.lean`. -/
axiom strings.TrimLeft.wp_proof : strings.TrimLeft.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
