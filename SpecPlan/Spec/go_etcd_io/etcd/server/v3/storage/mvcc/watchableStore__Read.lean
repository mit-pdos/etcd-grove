/-
`(*watchableStore).Read`: the `KV` interface's `Read` contract (3e's `KV.Read.contract`) at the watchable store.

**Users.** the server's reads (`EtcdServer.Range` through `txn.Range`, 2c/2d), the read view (`kv_view.go`).

**Proof sketch.** Promoted from the embedded `*store` (Go's method set; Goose's wrapper): 3e's `store.Read` spec, whose contract this is (the watchable store's invariant is the store's, with the watch half: `watchableAt`).

**Changes.** The canonical instance (PRINCIPLES, "Canonical specs are per (concrete type, method)").

**Margin.** As the contract's.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import SpecPlan.Spec.go_uber_org.zap.Api

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

/-- `s.Read` meets `KV.Read`'s contract. -/
def watchableStore.Read.spec : Prop := ∀ s : Loc, KV.Read.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
