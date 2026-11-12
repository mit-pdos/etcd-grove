/-
`watchableStore.progressIfSync` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

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

/-- `s.progressIfSync(m, id)` under `s.mu`'s read side: if every watcher of the map is synced and
at or below the current revision, a progress response (no events, the revision, the id given)
is sent (without blocking) on the first one's channel; the result says whether all were synced
and caught up. Unit W-M2: the response's id `rid` is each watcher's own (`progress`) or `-1` and
the watchers' channel carries its progress fact (`progressAll`'s). Unit W-K (K1b): the watchers
are on one channel (`γc`), and the response covers every one of them (`respCov`, in the channel's
invariant); a response of id `-1` is also complete (`respCompl`), from the caller's `CS` (lent)
and `complWS`. -/
abbrev mvcc.watchableStore.progressIfSync.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (m : Loc) (dq : DFrac) (M : GMap w64 Loc) (rid : w64)
    (γc : mvcc.WatchChanNames) (CS : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ m ↦${dq} M ∗
      □ (∀ (id : w64) (w : Loc), ⌜M !! id = some w⌝ -∗ (mvcc.storeWatchParams s st γ).IW w ∗
        ∃ (γw : mvcc.WatcherNames) (r : mvcc.WatchRange) (fcs : GoSlice), mvcc.watcherMeta γ w γw ∗
          ⌜γw.wc = γc⌝ ∗ mvcc.watcherFixed w r fcs ∗
          (⌜rid = r.id⌝ ∨ ⌜rid = W64 (-1)⌝ ∗ mvcc.progFact γw.wc.prog)) ∗
      CS ∗ (⌜rid ≠ W64 (-1)⌝ ∨ mvcc.complWS γ γc M CS) ∗
      mvcc.watchReader s st γ }}
    (App (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"progressIfSync"))
      (Val #m)) (Val #rid))
  {{ (b : Bool), RET #b; m ↦${dq} M ∗ CS ∗ mvcc.watchReader s st γ }}

end spec

end EtcdGrove
end Perennial
