/-
`(*store).Rev()` (`kv_view.go:32`). Promoted from the store's `ReadView` field (`&readView{s}`, set by `NewStore`, read-only): the method value at `*store` is `readView.Rev` on that field.

**Users**: `KV.Rev` on the server's store: the response headers (`v3_server.go:429, 730`,
`v3rpc/header.go:35`, `apply/backend.go:310`), the compactor's `RevGetter` (2e's `revGetter`), the
tester (`mvccrand.go:349, 507, 623`). Snippet `ReqReadFloor`.

**Proof sketch**: `rv.kv.Read(SharedBufReadTxMode, traceutil.TODO())` (`KV.Read.contract` at `*store`,
the caller's update fired there; a fresh trace: 4b's `TODO`), `Rev()` (`Txn.Rev.contract`:
`σ.rev`), the deferred `End()` (the token back).

**Changes** from `specs-ref`'s `store__Rev.lean`: the contract at `*store`.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Rev`'s contract at `*store`. -/
def store.Rev.spec : Prop :=
  ∀ s : Loc, KV.Rev.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
