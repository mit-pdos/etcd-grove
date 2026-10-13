/-
`watchableStore.cancelWatcher` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

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

/-- `s.cancelWatcher(wa)`: the watcher is cancelled (out of its group or victim batch, its
channel `nil`, its live ghost `false` for good); idempotent; a victim being resent is waited for
(the loop retries). The `panic("watcher not victim but not in watch groups")` is unreachable. -/
abbrev mvcc.watchableStore.cancelWatcher.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (wa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ (mvcc.storeWatchParams s st γ).IW wa }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"cancelWatcher")) (Val #wa))
  {{ RET #(); (mvcc.storeWatchParams s st γ).WC wa }}

end spec

end EtcdGrove
end Perennial
