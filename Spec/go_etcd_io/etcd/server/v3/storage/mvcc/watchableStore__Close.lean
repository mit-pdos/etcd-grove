/-
`(*watchableStore).Close()`: stops the two loops, waits for them, closes the store: the `KV`
interface's `Close` contract (3e's) at the watchable store.

**Users.** `EtcdServer.Cleanup` (`etcdserver/server.go:950`, 2e: `s.kv.Close()` before the backend's
close). Snippet: `mvccwatch/store.go` `ReqClose`.

**Proof sketch.** `close(s.stopc)` (the open token: a second `Close` panics); `s.wg.Wait()` (each
loop exits at `stopc`, between passes, so with its store share parked, depositing its loop share at
`Done`: Perennial's wait group backed by the two goroutines); with both deposits no pass can run, so
the parked shares `storeLoops st γ mvccLoopN` are taken (`oneshot-close.md`: a closer gives back
what the goroutines it waits for held); `s.store.Close()` (3e's watched instance,
`store.Close.watched.spec`, `InternalWatched.lean`: the shares back into the store, `mvccClosed`;
3e's `mvccClosed_rest` then gives the storage's rest, the loops' slots among `mvccOwnN`'s).

**Changes** from `specs-ref`'s file: the canonical instance of 3e's restated contract.

**Margin.** As the contract's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalWatched
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

/-- `s.Close` meets `KV.Close`'s contract. -/
def watchableStore.Close.spec : Prop := ∀ s : Loc, KV.Close.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
