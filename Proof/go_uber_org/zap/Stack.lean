/-
The trust boundary: `zap.Stack` (names only). (zap-z2, 2026-11-23) Not provable over Perennial's trusted
`runtime.callers` (`ca6df841b`), which may fill its buffer on every call: `stacktrace.Capture(skip, Full)`
then doubles its buffer until `make` fails (at the latest when the length overflows), where Go's
finite stack stops it
(`notes/perennial-changes.md`, "`runtime.callers` may fill its buffer every time").
-/
module

public import Spec.go_uber_org.zap.Stack

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom zap.Stack.wp_proof : zap.Stack.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
