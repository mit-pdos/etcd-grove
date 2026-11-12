/-
`v3rpc.LeaseServer.leaseKeepAlive` (`server/etcdserver/api/v3rpc/`).

Users: `LeaseServer.LeaseKeepAlive` (its goroutine).

Proof sketch: a loop: `Recv` (`Grpc.srvRecv_recv`: a request with its `up`, `io.EOF`, or grpc's error), a fresh response with the request's `ID` and a filled header, `ls.le.LeaseRenew(ctx, id)` (2c's: a TTL or an error; `ErrLeaseNotFound` becomes TTL `0`), `Send` (`srvSend_send`, `dn` is `True`); errors logged (`isClientCtxErr.spec`, W0's `Zap`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__leaseKeepAlive.lean`.

Margin: the responses' `ID` is the request's (1c's item 4); `kaSpec` does not record it.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `ls.leaseKeepAlive(stream)`: the loop, until the client closes (`nil`) or an error. -/
def LeaseServer.leaseKeepAlive.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (st : GoInterface) (g : StreamName) (md : MD) (i j : Nat) (gq : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ leaseServerAt p s γ ∗ srvGate s gq ∗ (∃ ctx, srvCtxOf st ctx md) ∗ srvRecv st g (kaSpec γ) md i ∗
      srvSend st g (kaSpec γ) md j }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"leaseKeepAlive")) (Val #st))
  {{ (err : GoInterface), RET #err; srvGate s gq ∗ (⌜err = GoInterface.nil⌝ ∨ ∃ code msg, sentStatus err code msg) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
