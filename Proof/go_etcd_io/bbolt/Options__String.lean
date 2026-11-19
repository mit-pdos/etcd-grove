/-
The trust boundary: `Spec/go_etcd_io/bbolt/Options__String.lean`. True of Go: `String` only reads
the 15 fields and formats them with `fmt.Sprintf`, which cannot fail. (2026-11-17, S2 of
`notes/bbolt-integration-plan.md`) `Options` is translated and its fields' reads are lemmas
(`Proof/go_etcd_io/bbolt/Options.lean`), but the call to `fmt.Sprintf` has no spec here: its format
has `%p` of the `OpenFile` func and of the `Logger` interface, and `%s` of a `time.Duration` (a
`Stringer`), and every `fmt.Sprintf` spec of this repository (`Spec/fmt/Sprintf*.lean`, over
Perennial's `fmt.ArgWf`) takes under a verb other than `v s x X q` only predeclared basic types or
named integers. So it stays an axiom until a `fmt.Sprintf` spec covers `%p` (a Perennial change).
-/
module

public import Spec.go_etcd_io.bbolt.Options__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

axiom Options.String.wp_proof : Options.String.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
