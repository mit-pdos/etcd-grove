/-
The trust boundary: `io.ReadFull` (names-only in Perennial; see `Spec/io/ReadFull.lean`). Proposed
in Perennial as a translation of `ReadFull`/`ReadAtLeast` with bodies and this spec proved over the
`Reader` interface (`notes/perennial-changes.md`, "No translation of `hash/crc32`, `bufio`, ...").
**Pending the user's review** (WAL leaf specs, 2026-11-13).
-/
module

public import Spec.io.ReadFull

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

axiom io.ReadFull.wp_proof : io.ReadFull.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
