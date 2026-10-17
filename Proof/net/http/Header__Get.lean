/-
**Trust boundary**: `Header.Get` returns the header's first value (an axiom; see `Spec/net/http/Header__Get.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.net.http.Header__Get

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

/-- **Trust boundary**: `Header.Get` returns the header's first value. -/
axiom http.Header.Get.wp_proof : http.Header.Get.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
