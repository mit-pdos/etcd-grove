/-
The trust boundary: `rate.Every` (`golang.org/x/time/rate` is names-only).
-/
module

public import Spec.golang_org.x.time.rate.Every

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

/-- **Trust boundary** (rafthttp stage 6c): `rate.Every(d)` (`rate.go`) is `Inf` for `d <= 0` and
`1 / d.Seconds()` otherwise, a floating-point division, which does not panic. -/
axiom rate.Every.wp_proof : rate.Every.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
