/-
Trust boundary: `errors.As` into a `*rpctypes.EtcdError` returns, having possibly written the target. (an axiom; see `Spec/errors/As.lean`).
-/
module

public import Spec.errors.As

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- **Trust boundary**: `errors.As` into a `*rpctypes.EtcdError` returns, having possibly written the target. -/
axiom errors.As.wp_proof : errors.As.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
