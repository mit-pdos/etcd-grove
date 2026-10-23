/-
The trust boundary: `rate.NewLimiter` (`golang.org/x/time/rate` is names-only).
-/
module

public import Spec.golang_org.x.time.rate.NewLimiter

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

/-- **Trust boundary** (rafthttp stage 6b): `rate.NewLimiter` (`rate.go`) allocates a `Limiter`
of the limit and burst given; its methods take its own mutex (`Wait`'s spec, `limiterOk`). -/
axiom rate.NewLimiter.wp_proof : rate.NewLimiter.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
