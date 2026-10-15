/-
The trust boundary: a context's `Value` at `traceutil.StartTimeKey` (Perennial's `isContext`
specifies `Value` only at `&cancelCtxKey`; a `valueCtx` looks the key up along its parents, which
returns some value, without effect).
-/
module

public import Spec.context.ValueStartTime

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
variable [package_sem : context.Assumptions]

axiom context.ValueStartTime.wp_proof : context.ValueStartTime.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
