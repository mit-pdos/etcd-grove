/-
The trust boundary: `strings.TrimSuffix` (`Spec/strings/TrimSuffix.lean`; a Perennial gap,
`notes/perennial-changes.md`).
-/
module

public import Spec.strings.TrimSuffix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 5e-3): Go's `TrimSuffix` (`strings.go`) slices `s`, reading
no memory but the strings and not panicking. -/
axiom strings.TrimSuffix.wp_proof : strings.TrimSuffix.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
