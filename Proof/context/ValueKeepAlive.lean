/-
The trust boundary: a context's `Value` at clientv3's `keepAliveCtxKey` (item 1, the client lease;
Perennial's `isContext` specifies `Value` only at `&cancelCtxKey`; a `valueCtx` looks the key up
along its parents, and only `lessor.KeepAlive` stores a value, a `*context.Context`, under it).
-/
module

public import Spec.context.ValueKeepAlive

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **Trust boundary** (item 1, the client lease): see `Spec/context/ValueKeepAlive.lean`. -/
axiom context.ValueKeepAlive.wp_proof : context.ValueKeepAlive.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
