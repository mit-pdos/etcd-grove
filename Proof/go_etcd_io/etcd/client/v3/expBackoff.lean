/-
**Trust boundary**: `expBackoff` (floats: `math.Pow`, `math.Min`, a float-to-integer conversion, none modeled) returns some duration (an axiom; see `Spec/go_etcd_io/etcd/client/v3/expBackoff.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.expBackoff

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary**: `expBackoff` (floats: `math.Pow`, `math.Min`, a float-to-integer conversion, none modeled) returns some duration. -/
axiom expBackoff.wp_proof : expBackoff.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
