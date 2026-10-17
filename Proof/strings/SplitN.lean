/-
Proof of `Spec/strings/SplitN.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.strings.SplitN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 5): `strings.SplitN` returns a fresh slice (`genSplit`: `make`), or
`nil` for `n == 0`; it does not panic. -/
axiom strings.SplitN.wp_proof : strings.SplitN.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
