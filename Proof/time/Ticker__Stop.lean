/-
The trust boundary: `(*time.Ticker).Stop`.
-/
module

public import Spec.time.Ticker__Stop

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

axiom time.Ticker.Stop.wp_proof : time.Ticker.Stop.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
