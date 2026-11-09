/-
`v3rpc.isClientCtxErr` (`server/etcdserver/api/v3rpc/`).

Users: `LeaseServer.leaseKeepAlive` (log levels), 2b's watch loops.

Proof sketch: `status.FromError` (`errView`), `Code()`, `Message()`, `strings.HasPrefix`/`HasSuffix` (Perennial's).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/isClientCtxErr.lean`: any error grpc's `status` can view.

Margin: the result is not specified: callers only choose a log level.
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

/-- `isClientCtxErr(ctxErr, err)`: returns, no panic. -/
def isClientCtxErr.spec : Prop :=
  ∀ (ctxErr err : GoInterface) (c : w32) (m : GoString) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ errView err c m ok }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr)) (Val #ctxErr)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end V3rpc
end EtcdGrove
end Perennial
