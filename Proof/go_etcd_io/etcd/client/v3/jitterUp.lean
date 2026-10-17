/-
**Trust boundary**: `jitterUp` (math/rand, floats) returns some duration (an axiom; see `Spec/go_etcd_io/etcd/client/v3/jitterUp.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.jitterUp

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

/-- **Trust boundary**: `jitterUp` (math/rand, floats) returns some duration. -/
axiom jitterUp.wp_proof : jitterUp.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
