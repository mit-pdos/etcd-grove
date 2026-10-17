/-
`(*clientv3.watcher).Close()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.Close()`: closes the watcher (its streams map `nil`) and every stream (`close`); returns an
error. -/
abbrev watcher.Close.spec : Prop :=
  ∀ (V : WEnv GF) (w : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      (∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗
        ⌜_root_.Perennial.errors.IsPointerError e⌝) ∗ isClientWatcher V w }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

/-- **What `Close` promises** ("Consider context.Canceled as a successful close", its comment; the
intent etcd#19935 keeps): if every stream's `close` reports `nil` or `context.Canceled`
(the scenario `watchGRPCStream.close.spec_nilOrCanceled`), `Close` returns `nil`. Holds of the
code before etcd#19935 (`notes/pr-verify/etcd-19935.md`); not of etcd#19935's code, whose
`errors.Is(err, context.Canceled)` tests the accumulated `err` instead of the stream's `werr`, so
that a stream reporting `context.Canceled` makes `Close` return it wrapped by `errors.Join`
(`notes/pr-verify/etcd-19935/watch_close_errors_test.go`). Not proved on this branch. -/
abbrev watcher.Close.spec_canceledIsSuccess : Prop :=
  ∀ (V : WEnv GF) (w : Loc) (ce : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok ce ∗
      ⌜_root_.Perennial.errors.IsPointerError ce⌝ ∗ isClientWatcher V w }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
