/-
`(*watchableStore).FirstRev`: the `KV` interface's `FirstRev` contract (3e's `KV.FirstRev.contract`) at the watchable store.

**Users.** the read view (`kv_view.go`), the server's `Status` (2d).

**Proof sketch.** Promoted from the embedded `*store` (Go's method set; Goose's wrapper): 3e's `store.FirstRev` spec, whose contract this is (the watchable store's invariant is the store's, with the watch half: `watchableAt`).

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

/-- `s.FirstRev` meets `KV.FirstRev`'s contract. -/
def watchableStore.FirstRev.spec : Prop := ∀ s : Loc, KV.FirstRev.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
