/-
**Trust boundary**: `errors.Is` of a tree of `status` errors and joins against a pointer error
(an axiom; see `Spec/errors/IsJoinedStatusErr.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.errors.IsJoinedStatusErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- **Trust boundary**: Perennial's `errors.wp_Is` with Go's typing of the tree's errors
(`TreeTyped`) assumed. -/
axiom errors.IsJoinedStatusErr.wp_proof : errors.IsJoinedStatusErr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
