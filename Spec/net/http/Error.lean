/-
`http.Error(w, msg, code)`: the trust boundary (`net/http` is names-only; PR etcd#22243, the
peer hashKV handler). Lean-first (no Rocq counterpart).
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

/-- `http.Error(w, msg, code)` replies to the request with the status `code` and the body `msg`
(and the headers it sets for an error): the response's next event is `.error code msg`. -/
abbrev http.Error.spec : Prop :=
  ∀ (w : GoInterface) (evs : List http.RespEv) (msg : GoString) (code : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ http.respLog w evs }}
    (App (App (App (Val (@! _root_.Perennial.net.http.Error)) (Val #w)) (Val #msg)) (Val #code))
  {{ RET #(); http.respLog w (evs ++ [.error code msg]) }}

end spec

end EtcdGrove
end Perennial
