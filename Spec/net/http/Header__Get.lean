/-
`(*http.Header).Get(k)` on a request's header map: the trust boundary (`net/http` is
names-only; PR etcd#22243, the peer hashKV handler). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvHashKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `hp.Get(k)`, for the request header at `hp` whose (first) value for `k` is `v`, returns
`v`. -/
abbrev http.Header.Get.spec : Prop :=
  ∀ (hp : Loc) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ http.reqHdrGet hp k v }}
    (App (Val (hp @!! go.GoType.PointerType _root_.Perennial.net.http.Header.ty @!! go!"Get"))
      (Val #k))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
