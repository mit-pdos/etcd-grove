/-
`isCancelError(err)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:253-267`): whether the error is a
cancellation (`context.Canceled`, an `etcdError` or `grpcError` with code `Canceled`). Returns some
boolean for an error the watcher's error paths accept (`kErrOk`: the comparison with
`context.Canceled`, the type assertions and the `Code()`/`GRPCStatus()` methods they find). Proved
(k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev isCancelError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ kErrOk err }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.isCancelError)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end k8s
end EtcdGrove
end Perennial
