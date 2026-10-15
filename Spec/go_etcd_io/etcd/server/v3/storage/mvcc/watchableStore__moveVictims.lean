/-
`watchableStore.moveVictims` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
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

/-- `s.moveVictims()` with the caller's reader slots: takes the victim batches out of `s.mu`
(their watchers out with the mover: `moverRes`), resends each batch outside the lock, and puts
each watcher whose batch was sent back under the lock (unsynced at or below the current revision,
else synced); the others become victims again (one batch appended). The lock invariant is kept;
the number returned is the batches sent. -/
abbrev mvcc.watchableStore.moveVictims.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.watchReader s st γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"moveVictims")) (Val #()))
  {{ (moved : w64), RET #moved; mvcc.watchReader s st γ }}

end spec

end EtcdGrove
end Perennial
