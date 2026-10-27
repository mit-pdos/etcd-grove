/-
`transport.IsClosedConnError`: the trust boundary (`go.etcd.io/etcd/client/pkg/v3/transport` is
names-only; rafthttp stage 5c, the stream reader's `run`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.net.http.Boundary
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.transport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `transport.IsClosedConnError(err)` (`listener.go`: `err != nil && strings.Contains(err.Error(),
"closed")`) of an error whose `Error()` returns: some `bool`. -/
abbrev transport.IsClosedConnError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport ∗
      http.errStrOk err }}
    (App (Val (@! transport.IsClosedConnError)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
