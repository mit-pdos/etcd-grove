/-
`watchableStore.syncVictimsLoop` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
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

/-- `s.syncVictimsLoop()` (a goroutine `New` starts), with reader slots of the store and a done
token of its wait group: resends the victims' batches (`moveVictims`, while it moves some), then
waits for a tick (if victims are left), a new victim (`victimc`) or the stop channel's close,
until the latter, then `s.wg.Done()`. It returns (no panic). -/
abbrev mvcc.watchableStore.syncVictimsLoop.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.watchReader s st γ ∗ mvcc.wsDone s }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"syncVictimsLoop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
