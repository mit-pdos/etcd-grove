/-
Trust boundary: `(*mvcc.watchableStore).HashStorage` (`(*store).HashStorage`, promoted) (an axiom; see `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/watchableStore__HashStorage.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__HashStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): `func (s *store) HashStorage() HashStorage {
return s.hashes }`, promoted through the watchable store's embedded `*store`: it reads two pointer
fields that `newWatchableStore` and `NewStore` set before the store is shared and nothing writes
after (`store.hashes`, `watchableStore.store`). -/
axiom mvcc.watchableStore.HashStorage.wp_proof : mvcc.watchableStore.HashStorage.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
