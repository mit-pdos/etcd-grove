/-
`v3rpc.healthNotifier.startServe` (`v3rpc/health.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`hc.startServe()`** on a health notifier over grpc's health server `hs` with a non-nil
logger: it logs and sets the health server's status. -/
abbrev v3rpc.healthNotifier.startServe.spec : Prop :=
  ∀ (hc hs lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ structFieldRef v3rpc.healthNotifier go!"hs" hc ↦□ hs ∗ grpcHealthSrv hs ∗
      structFieldRef v3rpc.healthNotifier go!"lg" hc ↦□ lg ∗ ⌜lg ≠ null⌝ }}
    (App (Val (hc @!! go.GoType.PointerType v3rpc.healthNotifier.ty @!! go!"startServe"))
      (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
