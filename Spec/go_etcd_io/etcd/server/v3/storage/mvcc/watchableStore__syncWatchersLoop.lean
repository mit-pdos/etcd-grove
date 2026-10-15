/-
`watchableStore.syncWatchersLoop` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.syncWatchersLoop()` (a goroutine `New` starts), with reader slots of the store and a done
token of its wait group: syncs the unsynced watchers (`syncWatchers`) on every tick of its ticker
until the stop channel is closed, then `s.wg.Done()`. It returns (no panic). -/
abbrev mvcc.watchableStore.syncWatchersLoop.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.watchReader s st γ ∗ mvcc.wsDone s }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"syncWatchersLoop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
