/-
The trust boundary: `(*time.Ticker).Reset`.
-/
module

public import Spec.time.Ticker__Reset

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
variable [package_sem : time.Assumptions]

axiom time.Ticker.Reset.wp_proof : time.Ticker.Reset.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
