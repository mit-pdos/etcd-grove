/-
`v3rpc.newHealthNotifier` (`v3rpc/health.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newHealthNotifier(hs, s)`** over grpc's (non-nil) health server returns a notifier, having
set the health server's status to serving; the logger's reader slot comes back. -/
abbrev v3rpc.newHealthNotifier.spec : Prop :=
  ∀ (hs s lg : Loc) (fg : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ ⌜hs ≠ null⌝ ∗ grpcHealthSrv hs ∗ srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg }}
    (App (App (Val (@! v3rpc.newHealthNotifier)) (Val #hs)) (Val #s))
  {{ (n : GoInterface), RET #n; srvLgReader s }}

end spec

end EtcdGrove
end Perennial
