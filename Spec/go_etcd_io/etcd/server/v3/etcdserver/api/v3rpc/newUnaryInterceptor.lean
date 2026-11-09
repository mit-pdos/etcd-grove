/-
`v3rpc.newUnaryInterceptor` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server` (the unary chain).

Proof sketch: the capability check (`ErrGRPCNotCapable`, indefinite), the learner check (the fork's fixed `IsLocalMemberLearner`, `issues/etcd-unary-interceptor-learner-removed.md`; `ErrGRPCNotSupportedForLearner`: the contract's second way, the update given back), the incoming metadata (`FromIncomingContext`, `MD.Get`; an invalid client version: `ErrGRPCInvalidClientAPIVersion`, unmapped, so a status that settles nothing), the require-leader key (`ErrGRPCNoLeader`, indefinite), then the handler once with its arguments.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newUnaryInterceptor.lean`: as `icEtcdOk` (was `srvInterceptorOk` with a per-interceptor predicate).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `newUnaryInterceptor(s)`: an interceptor preserving etcd's contracts. -/
def newUnaryInterceptor.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newUnaryInterceptor)) (Val #s))
  {{ (i : GoFunc), RET #i; icEtcdOk i γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
