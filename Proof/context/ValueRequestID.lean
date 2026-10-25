/-
The trust boundary: a context's `Value` at `requestid.requestIDKey` (Perennial's `isContext`
specifies `Value` only at `&cancelCtxKey`; a `valueCtx` looks the key up along its parents, which
returns `nil` or the `uint64` stored by `requestid.NewContext`, without effect).
-/
module

public import Spec.context.ValueRequestID

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

axiom context.ValueRequestID.wp_proof : context.ValueRequestID.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
