/-
`(*clientv3.watchGRPCStream).close()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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

/-- `w.close()`: cancels the stream's context, waits for `run` to stop (`donec`), and returns
`ContextError` of the receive error left in `errc`, if any: an error grpc's `status` accepts. -/
abbrev watchGRPCStream.close.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"close")) (Val #()))
  {{ (err : GoInterface), RET #err; statusErrOk err }}

/-- **A scenario, not a spec of `close`** (etcd#19935): the stream's `close` reports `nil` or
`context.Canceled` (the value `ce` of `context.Canceled`), as it does when the stream's own
cancellation is what ended it (`ContextError` maps grpc's `Canceled` to the context's error).
The premise of `watcher.Close.spec_canceledIsSuccess`. -/
abbrev watchGRPCStream.close.spec_nilOrCanceled : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (ce : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isWGS V G callSl ∗
      globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok ce }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"close")) (Val #()))
  {{ (err : GoInterface), RET #err; statusErrOk err ∗
      ⌜err = GoInterface.nil ∨ err = GoInterface.ok ce⌝ }}

end spec

end EtcdGrove
end Perennial
