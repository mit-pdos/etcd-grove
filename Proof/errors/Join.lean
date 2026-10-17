/-
**Trust boundary**: `errors.Join` of trees of `status` errors and joins (an axiom; see
`Spec/errors/Join.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.errors.Join

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

/-- **Trust boundary**: `errors.Join` is not translated (names only in Perennial's `errors`). -/
axiom errors.Join.wp_proof : errors.Join.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
