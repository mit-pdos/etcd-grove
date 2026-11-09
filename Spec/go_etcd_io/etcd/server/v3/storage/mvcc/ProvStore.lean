/-
# mvcc's store constructor: the slots batch 3f assumes of batch 3e (provisional)

**Provisional.** `New` (`watchable_store.go`, batch 3f) is `NewStore` (`kvstore.go`, batch 3e) plus the
watchable store and its two loops. 3e's `Api.lean` has no constructor contract yet (its `NewStore`
spec, when written, fixes what a store needs and gives); until then `New.spec` is stated over two
slots with the meaning below, and `notes/specs-only/req/go_etcd_io_etcd_server_v3_storage_mvcc.md`,
"from 3f", asks 3e for them (or for `NewStore`'s contract as an `abbrev` over a constructor value, of
which `New.spec` becomes an instance with `watchableAt` added). At integration this module is
deleted.

* `storeBoot lg b le cfg h` (exclusive): **what `NewStore(lg, b, le, cfg)` needs**: the storage `b`
  ready for a store at the history `h` (3e's `mvccStorageFor` with its batch lock's invariant), the
  lessor `le` (`lessorAt`, its range-deleter slot `rdSlot`), the configuration's bounds.
* `storeBooted kv γ le` (exclusive): **what it gives besides the handle, the state and the open
  token**: the reader tokens (`mvccReaders γ mvccTokN`), the backend share (`mvccBackend γ 1 B Pk`),
  the lessor's binding (`mvccLessorIs`) and its deleter (`rdSlot γl rd ∗ mvccDeleter rd γ`, when `le`
  is not `nil`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- (provisional, 3e's) What `NewStore(lg, b, le, cfg)` needs: its storage `b` at the history `h`. -/
opaque storeBoot (lg : Loc) (b le : GoInterface) (cfg : go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig)
  (h : KVHist) : IProp GF := iprop(True)

/-- (provisional, 3e's) What `NewStore` gives besides the handle, the state and the open token. -/
opaque storeBooted (kv : GoInterface) (γ : MvccName) (le : GoInterface) : IProp GF := iprop(True)

end res

end Mvcc
end EtcdGrove
end Perennial
