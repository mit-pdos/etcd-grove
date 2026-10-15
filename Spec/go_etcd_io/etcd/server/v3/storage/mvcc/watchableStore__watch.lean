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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.watch(key, end, startRev, id, ch, fcs)`: the `watchable` contract's `watch`
(`storeWatchParams`): a new watcher of the range (`end` nil: the single key), registered on the
stream's channel `ch` (the close right's watchers grow), synced (a start revision `0` or past
the current revision: from the next revision, or `startRev`) or unsynced (from `startRev`,
behind), with its cancel closure (`cancelWatcher`). -/
abbrev mvcc.watchableStore.watch.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (key endk fcs : GoSlice) (k e : List w8) (fs : List GoFunc)
    (startRev id : w64) (ch : GoChan) (L : List Loc),
  let P := mvcc.storeWatchParams s st γ
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗
      key ↦*□ k ∗ endk ↦*□ e ∗ fcs ↦*□ fs ∗ ([∗list] f ∈ fs, P.F f) ∗ P.C ch ∗ P.CR ch L ∗
      P.R ∗ P.T ∗ ⌜0 ≤ sint.Z startRev⌝ }}
    (App (App (App (App (App (App
      (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"watch")) (Val #key))
      (Val #endk)) (Val #startRev)) (Val #id)) (Val #ch)) (Val #fcs))
  {{ (w : Loc) (c : GoFunc), RET (PairV #w #c);
      ⌜w ≠ null⌝ ∗ P.IW w ∗ mvcc.cancelSpec P c w ∗ P.CR ch (w :: L) ∗ P.R }}

end spec

end EtcdGrove
end Perennial
