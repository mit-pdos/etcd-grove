/-
**Trust boundary**: `http.Error` records the error response on the writer (an axiom; see `Spec/net/http/Error.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.net.http.Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Trust boundary**: `http.Error` records the error response on the writer. -/
axiom http.Error.wp_proof : http.Error.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
