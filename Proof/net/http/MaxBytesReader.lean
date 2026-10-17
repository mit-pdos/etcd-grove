/-
**Trust boundary**: `http.MaxBytesReader` returns a reader of `body` bounded by `n` (an axiom; see `Spec/net/http/MaxBytesReader.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.net.http.MaxBytesReader

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

/-- **Trust boundary**: `http.MaxBytesReader` returns a reader of `body` bounded by `n`. -/
axiom http.MaxBytesReader.wp_proof : http.MaxBytesReader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
