/-
`http.Header.Set(k, v)` on a response's header map: the trust boundary (`net/http` is
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

/-- `hm.Set(k, v)`, for the header map `hm` of the response writer `w`, sets the response's
header `k` to `v`: the response's next event is `.header k v`. -/
abbrev http.Header.Set.spec : Prop :=
  ∀ (w : GoInterface) (hm : Loc) (evs : List http.RespEv) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ http.respHdr w hm ∗ http.respLog w evs }}
    (App (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Set")) (Val #k)) (Val #v))
  {{ RET #(); http.respLog w (evs ++ [.header k v]) }}

end spec

end EtcdGrove
end Perennial
