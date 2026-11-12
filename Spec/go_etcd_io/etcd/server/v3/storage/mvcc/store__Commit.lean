/-
`store.Commit` (`kvstore.go`; translated since D22 S-l's sender items, 2026-10-22: names-only until
then, the server's `srvKVCommitOk` its contract). Lean-first (no Rocq counterpart); see
`InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Commit()`: under `s.mu` held exclusively, the backend's `ForceCommit()` (the batch
transaction committed, its pre-commit hooks run: for the server, the consistent index saved). The
caller's share of the store's current objects (`curAt γ qf o`: `γ`'s names are the store's current
ones, so `s.b` is `γ`'s backend), a reader of the store (under a later: a pool's loan; its ticket of
the index's readers' pool gives `ForceCommit` a reader token of the backend, `readerPool_checkout`,
given back) and a write session's token or its supply (`storeWT`: the real backend's write-back
budget, which the commit spends; a step's receipt buys one). (2026-11-06: until then the sole
writer's fragment and retired reader, `writerFrag`/`writerOwn`, which the API's `KV.Commit` does
not have.) The commit's effect on the backend's data is not in the store's model (the readers' view
is unchanged: `isKeyBackendG`'s `ForceCommit`). -/
abbrev mvcc.store.Commit.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (qf : Qp) (o : mvcc.StoreObjs) (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.curAt γ (DFrac.own qf) o ∗ ▷ mvcc.storeReaderC s γ ∗
      (mvcc.storeWT γ ∨ □ (⧗ 1 ={⊤}=∗ mvcc.storeWT γ)) ∗ X ∗ mvcc.storeReq γ X Y }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Commit")) (Val #()))
  {{ RET #(); mvcc.curAt γ (DFrac.own qf) o ∗ mvcc.storeReaderC s γ ∗ Y }}

end spec

end EtcdGrove
end Perennial
