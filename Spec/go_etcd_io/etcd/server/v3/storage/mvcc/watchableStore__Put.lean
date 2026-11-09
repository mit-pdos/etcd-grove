/-
`(*watchableStore).Put`: the `KV` interface's `Put` contract (3e's `KV.Put.contract`) at the watchable store.

**Users.** the write view (`kv_view.go`); etcd's apply goes through `Write`.

**Proof sketch.** Promoted from the embedded `*store` (Go's method set; Goose's wrapper): 3e's `store.Put` spec, whose contract this is (the watchable store's invariant is the store's, with the watch half: `watchableAt`).

**Changes.** The canonical instance (PRINCIPLES, "Canonical specs are per (concrete type, method)").

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

/-- `s.Put` meets `KV.Put`'s contract. -/
def watchableStore.Put.spec : Prop := ∀ s : Loc, KV.Put.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
