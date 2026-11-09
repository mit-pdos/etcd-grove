/-
`(*store).FirstRev()` (`kv_view.go:26`). Promoted from the store's `ReadView` field (`&readView{s}`, set by `NewStore`, read-only): the method value at `*store` is `readView.FirstRev` on that field.

**Users**: `KV.FirstRev` (no caller in etcd outside mvcc; part of `ReadView`'s contract, as
`txn/range.go:180`'s `rv.FirstRev()` of a transaction). Snippet `ReqReadFloor`.

**Proof sketch**: as `Rev`: `Read`, `FirstRev()` (`σ.crev`), `End()`.

**Changes**: the contract at `*store` (no old spec file of its own).

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

/-- `KV.FirstRev`'s contract at `*store`. -/
def store.FirstRev.spec : Prop :=
  ∀ s : Loc, KV.FirstRev.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
