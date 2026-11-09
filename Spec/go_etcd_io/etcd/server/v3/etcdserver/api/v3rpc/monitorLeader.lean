/-
`v3rpc.monitorLeader` (`server/etcdserver/api/v3rpc/`).

Users: `newStreamInterceptor`.

Proof sketch: a fresh `streamsMap` (a mutex over a map, `streamsMapAt`); `s.GoAttach` (2e: the goroutine forked, its token from `Fork`) of the loop: every election timeout, the leader (2d's `Leader`), and after three without one, each registered stream's context canceled (`cancellableContext.Cancel.spec`) and waited for (`Done`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/monitorLeader.lean`.

Margin: the loop's liveness (it stops at `StoppingNotify`).
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

/-- `monitorLeader(s)`: the streams map, the monitor started. -/
def monitorLeader.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.monitorLeader)) (Val #s))
  {{ (sm : Loc), RET #sm; streamsMapAt sm }}

end spec

end V3rpc
end EtcdGrove
end Perennial
