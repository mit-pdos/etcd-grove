/-
`watchableStore.Close` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR

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

/-- `s.Close()`, with the right to close the store (`wsCloser`, once: `New` returns it): closes the
stop channel (the loops return), waits for the loops (`s.wg.Wait()`), and closes the inner store
(`store.Close`), returning its `nil`; (R-D1, 2026-11-04) with the loops' readers of the inner store,
which each loop leaves at its deferred `wg.Done()` (its last action), and the inner store's job
budget (`store.Close`'s): what the caller retires for the backend's `Close`. Until then `True`. (M2, the storage side, the approval's
item 23, "alike" `store.Close`: the right to close by the mode, `wsCloserM`: off, `wsCloser`; on,
`wsCloserR`, with the inner store's restorable compaction right at its compaction revision `c`.) -/
abbrev mvcc.watchableStore.Close.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.wsCloserM s st γ.st c }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Close")) (Val #()))
  {{ RET #(GoInterface.nil);
      ([∗list] _x ∈ List.replicate mvcc.wsLoopN (), mvcc.storeReader st γ.st) ∗
      mvcc.compactJobResM γ.st.kb }}

end spec

end EtcdGrove
end Perennial
