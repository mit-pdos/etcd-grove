/-
`(*watchableStore).Commit`: the `KV` interface's `Commit` contract (3e's `KV.Commit.contract`) at the watchable store.

**Users.** the snapshot path (`etcdserver/server.go`, 2d: `KV().Commit()`).

**Proof sketch.** Promoted from the embedded `*store` (Go's method set; Goose's wrapper): 3e's `store.Commit` spec, whose contract this is (the watchable store's invariant is the store's, with the watch half: `watchableAt`).

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

/-- `s.Commit` meets `KV.Commit`'s contract. -/
def watchableStore.Commit.spec : Prop := ∀ s : Loc, KV.Commit.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
