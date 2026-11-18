/-
Trust boundary: `io.NewSectionReader` (an axiom; see `Spec/io/NewSectionReader.lean`). S4,
2026-11-18; proposed in Perennial as a translation of `io`'s `SectionReader` with bodies
(`notes/perennial-changes.md`, "`io.NewSectionReader`, `io.CopyN`").
-/
module

public import Spec.io.NewSectionReader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (S4): Go's `io.NewSectionReader(r, off, n)` (go1.27 `io/io.go`) computes its
limit (`off + n`, as `off ≤ MaxInt64 - n` here) and returns a fresh `&SectionReader{r, off, off,
off + n, n}`, touching nothing else: `io.secReader sr r off n` is that struct, owned, and only
`io.CopyN`'s axiom uses it. What would discharge it: `io`'s `SectionReader` translated with its
bodies, `secReader` its struct's points-to. -/
axiom io.NewSectionReader.wp_proof : io.NewSectionReader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
