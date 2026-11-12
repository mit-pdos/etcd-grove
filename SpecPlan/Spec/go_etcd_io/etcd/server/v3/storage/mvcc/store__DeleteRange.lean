/-
`(*store).DeleteRange(key, end)` (`kv_view.go:46`). Promoted from the store's `WriteView` field (`&writeView{s}`): the method value at `*store` is `writeView.DeleteRange` on that field.

**Users**: `KV.DeleteRange` (the server uses `txn.DeleteRange`'s transaction). Snippet
`ReqDeleteRange`.

**Proof sketch**: as `Put`: `Write`, `Txn.DeleteRange` (the range's present keys `ds` of
`σ.kv.store`), `End` (both steps; for `ds = []` the commit of nothing).

**Changes** from `specs-ref`'s `writeView__DeleteRange.lean`: the contract at `*store`.

**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- `KV.DeleteRange`'s contract at `*store`. -/
def store.DeleteRange.spec : Prop :=
  ∀ s : Loc, KV.DeleteRange.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
