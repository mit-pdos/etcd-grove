/-
**Trust boundary**: `errors.Is` of an error grpc accepts, against an `EtcdError` value, a pointer error or a comparable error, returns (an axiom; see `Spec/errors/IsStatusErr.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.errors.IsStatusErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- **Trust boundary**: `errors.Is` of an error grpc accepts, against an `EtcdError` value, a pointer error or a comparable error, returns. -/
axiom errors.IsStatusErr.wp_proof : errors.IsStatusErr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
