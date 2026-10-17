/-
`http.MaxBytesReader(w, body, n)`: the trust boundary (`net/http` is names-only; PR etcd#22243,
the peer hashKV handler). Lean-first (no Rocq counterpart).
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

/-- `http.MaxBytesReader(w, body, n)` returns a reader `lr` of `body` bounded by `n` (it reads
nothing yet; what reading it does is `io.ReadAllMaxBytes`'s). -/
abbrev http.MaxBytesReader.spec : Prop :=
  ∀ (w body : GoInterface) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http }}
    (App (App (App (Val (@! _root_.Perennial.net.http.MaxBytesReader)) (Val #w)) (Val #body))
      (Val #n))
  {{ (lr : GoInterface), RET #lr; http.maxBytesR lr body n }}

end spec

end EtcdGrove
end Perennial
