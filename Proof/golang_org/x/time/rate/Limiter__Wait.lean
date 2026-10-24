/-
The trust boundary: `(*rate.Limiter).Wait` (`golang.org/x/time/rate` is names-only).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

axiom rate.Limiter.Wait.wp_proof : rate.Limiter.Wait.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
