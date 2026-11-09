/-
`(*store).Put(key, value, lease)` (`kv_view.go:52`). Promoted from the store's `WriteView` field (`&writeView{s}`): the method value at `*store` is `writeView.Put` on that field.

**Users**: `KV.Put` (the server goes through `txn.Put`'s transaction instead; the contract's own
users). Snippets `ReqPutRev`, `ReqPutLease`.

**Proof sketch**: `wv.kv.Write(TODO())` (`KV.Write.contract`: the hook `Pre` to `Q'`; `Write`'s
update reads `σ` and the pending check), the transaction's `Put` (`Txn.Put.contract`: the event
`putEv σ [] k v l`, the lessor's item map moved), the deferred `End()` (`Txn.End.contract`:
`Q' ={⊤}=∗ Pk ∗ Post` gives `End` its `Pk`; the caller's notify step, then its commit step, at
`σ`).

**Changes** from `specs-ref`'s `writeView__Put.lean`: the contract at `*store`; the lessor's items
over the provisional `leaseItems` (3c's).

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

/-- `KV.Put`'s contract at `*store`. -/
def store.Put.spec : Prop :=
  ∀ s : Loc, KV.Put.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
