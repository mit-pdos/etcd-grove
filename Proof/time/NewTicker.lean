/-
The trust boundary: `time.NewTicker` (tickers are not translated, the runtime's timers not modelled).
-/
module

public import Spec.time.NewTicker

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

axiom time.NewTicker.wp_proof : time.NewTicker.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
