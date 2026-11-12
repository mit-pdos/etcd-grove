/-
`watchableStore.watch` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
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

/-- `s.watch(key, end, startRev, id, ch, fcs)`: the `watchable` contract's `watch`
(`storeWatchParams`): a new watcher of the range (`end` nil: the single key), registered on the
stream's channel `ch` (the close right's watchers grow), synced (a start revision `0` or past
the current revision: from the next revision, or `startRev`) or unsynced (from `startRev`,
behind), with its cancel closure (`cancelWatcher`), what the registration says of it
(`P.IWF`, `watcherIs`: its names, fixed fields, and first revision, `startRev` or, for `0`, the
length of a committed log at the registration) and the bound on the channel's registered
watchers (the watcher budget). Unit W-M2: the registration callback (`isWatchable`), applied
to the new watcher when it is registered on the channel `γc`, whose result the channel's
invariant keeps (`chanRegFact`); the watcher is on `γc` (`P.OC`). Stage 2 of the mvcc API
(2026-11-05): the filters decide the caller's predicates `fs` (`P.FI`, `filtersImpl`), and the
callback is the store's (`regCb`): run with the channel's invariant open, it appends the
registration to the stream's history, with `s.revMu`'s part of the API's view and the lock's
pending revision (at `none`) in hand, for the caller's `Watch` update. -/
abbrev mvcc.watchableStore.watch.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (key endk fcs : GoSlice) (k e : List w8) (fs : List (mvcc.EvM → Bool))
    (startRev id : w64) (ch : GoChan) (γc : mvcc.WatchChanNames) (L : List Loc)
    (Back : Loc → IProp GF),
  let P := mvcc.storeWatchParams s st γ
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗
      key ↦*□ k ∗ endk ↦*□ e ∗ P.FI fcs fs ∗ P.C ch ∗
      P.CR ch γc L ∗ P.R ∗ P.T ∗ ⌜0 ≤ sint.Z startRev ∧ id ≠ W64 (-1)⌝ ∗
      P.RegCb ch γc (mvcc.watchRangeOf k e endk startRev id) fs Back }}
    (App (App (App (App (App (App
      (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"watch")) (Val #key))
      (Val #endk)) (Val #startRev)) (Val #id)) (Val #ch)) (Val #fcs))
  {{ (w : Loc) (c : GoFunc), RET (PairV #w #c);
      ⌜w ≠ null⌝ ∗ P.IW w ∗ P.OC w γc ∗ mvcc.cancelSpec P c w ∗ P.CR ch γc (w :: L) ∗ P.R ∗
      (∃ lo : Nat, P.IWF w (mvcc.watchRangeOf k e endk startRev id) fcs lo) ∗
      ⌜(w :: L).length + 3 ≤ 2 ^ 63⌝ ∗ P.WS w ∗ Back w }}

end spec

end EtcdGrove
end Perennial
