/-
`watchStream.Cancel` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream

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

/-- **`ws.Cancel(id)`**: `nil` (the watcher of `id` cancelled) or `ErrWatcherNotExist` (no
watcher of that id, or the stream closed). Unit W-K (K1b): with the cancellation's reason for
`id` (`rsnFor`: the stream's creator's predicate), which the channel then has for the watcher
(a progress response of id `-1` covers every registered watcher not cancelled for its reason). -/
abbrev mvcc.watchStream.Cancel.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : mvcc.WsStreamNames) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchStream ws wa P γ ∗ mvcc.rsnFor γ.rsn id }}
    (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"Cancel")) (Val #id))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ globalAddr ErrWatcherNotExist ↦□ err }}

end spec

end EtcdGrove
end Perennial
