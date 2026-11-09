/-
`(*watchableStoreTxnWrite).FirstRev`: promoted from the embedded `TxnWrite` (3e's transaction): the `TxnWrite` interface's `FirstRev` contract (3e's `Txn.FirstRev.contract`) at the watchable transaction.

**Users.** every write transaction of the watchable store (`watchableStore.Write`'s users: `etcdserver/txn`, the lessor's revoke `lessor.go:361`, the write view).

**Proof sketch.** The embedded transaction's method (its contract), the wrapper's `mvccTxn` the inner one's.

**Changes.** The canonical instance.

**Margin.** As the contract's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `t.FirstRev` meets `Txn.FirstRev`'s contract. -/
def watchableStoreTxnWrite.FirstRev.spec : Prop := ∀ t : Loc, Txn.FirstRev.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t

end spec

end Mvcc
end EtcdGrove
end Perennial
