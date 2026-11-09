/-
`(*watchStream).Watch(ctx, id, key, end, startRev, fcs...)` (`watcher.go`): registers a watcher of
`[key, end)` (`end` `nil`: the key; empty: from the key) from `startRev` (`0`: from the store's
current revision on), filtered by `fcs`, under a fresh id.

**Users.** `serverWatchStream.recvLoop` (`v3rpc/watch.go:342`, 2b: `mvcc.WatchID(creq.WatchId)`,
`0` for every client the wire model admits: 2b's `watchReqOwn_unfold`; the end normalized; the
filters of `FiltersFromRequest`; a start revision not negative, refused before). Snippets:
`mvccwatch/history.go` `ReqFromStart`, `ReqFromCurrent`, `ReqFilters`; `lifecycle.go` `ReqFreshIds`,
`ReqEmptyRange`.

**Proof sketch.** The empty-range check (`bytes.Compare`); under `ws.mu` (the stream's invariant):
`closed` gives the error (and `wsClosed`); the auto id: the loop skips live ids from `nextID` (the
stream's next id is `n`, `wsCtl`, and with auto ids only no live id is skipped; `nextID` stays
below `2 ^ 63 - 1` by the time receipts of the `Watch` calls, `ReceiptBoundLe`, the bound at its
owner, so the id is neither wrapped nor `-1`);
`watchable.watch` (`watchableStore.watch.spec`: the caller's update fired under `s.mu` and
`revMu` at the state read, a reader token (3e's `mvccReaders`) for `revMu`'s reader slot: the
watcher registered under `s.mu`, synced or unsynced, at the store's revision `R`, the registration
`wsReg` with the stream's send count as its stamp); `trace.SpanFromContext(ctx)` (otel's boundary,
4b: any `ctxOk` context); the cancel closure and the watcher stored in the maps.

**Changes** from `specs-ref`'s file: the stream's state update (an atomic update over `wsState`)
replaced by the persistent facts the consumer needs (`wsReg` with the watcher's position and stamp,
`mvccLb` at the registration's state) and the control token; the store's state read by the
caller's update (3e's `KV.Rev` form: 2b's floor, the `Created` header's `Rev()` read after it, is at
least the position); a context is any `ctxOk` one (W0's) in place of `TODO` or an `isContext` with
its span; the id `0` stays a premise (a scope restriction, below). (Round 1: the read update, F2;
`id = n` with `wsReg_ctl`, the range non-empty on success, F4; the error value, F6; the receipt
bound, S2.)

**Margin.** A caller-chosen id (`id ≠ 0`) is out of scope: it can reuse a cancelled watcher's id,
whose queued responses then read as the new watcher's (`issues/etcd-watch-id-reuse-stale-events.md`);
every verified caller passes `0`. A negative start revision is out of scope too (the code sends a
compaction response with a revision `-1`, or replays from revision `0`:
`nonissues/etcd-mvcc-watch-negative-start-rev.md`; v3rpc refuses it first).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.context.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`w.Watch(ctx, 0, key, end, startRev, fcs...)`**: an empty range (`end` neither `nil` nor
empty, and not above `key`), or a closed stream, is refused (`-1`, the package's
`ErrEmptyWatcherRange`, the caller's update back); else, by the caller's read update fired at the
state `σ` the registration reads (nothing pending: under `s.mu`), a watcher registered under the
stream's next id `n`, as `W`: its range, its filters, its start revision, its position
(`startRev - 1`, or `σ.rev` for `0`), stamped with the stream's send count (`wsSentLb`). -/
def watchStream.Watch.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (w : Loc) (γ : MvccName) (ι : WsNames) (n : Int)
    (ctx : GoInterface) (key endk fcs : GoSlice) (k e : GoString) (ds : List (EvM → Bool))
    (startRev : w64) (Q : MvccState → IProp GF),
  let empty : Prop := endk ≠ slice.nil ∧ e ≠ [] ∧ ¬ go.GoStringLt k e
  let au : IProp GF := iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
    <{ mvccState γ σ, COMM Q σ }>)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsAt w γ ι ∗ wsCtl ι n ∗ Context.ctxOk ctx ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      filtersAt fcs ds ∗ ⌜0 ≤ sint.Z startRev⌝ ∗ mvccReaders γ 1 ∗ au }}
    (App (App (App (App (App (App (Val (w @!! go.GoType.PointerType watchStream.ty @!! go!"Watch")) (Val #ctx)) (Val #(W64 0)))
      (Val #key)) (Val #endk)) (Val #startRev)) (Val #fcs))
  {{ (id : w64) (err : GoInterface), RET (PairV #id #err); mvccReaders γ 1 ∗
      ((⌜id = W64 (-1)⌝ ∗ globalAddr ErrEmptyWatcherRange ↦□ err ∗ wsCtl ι n ∗ au ∗
          (⌜empty⌝ ∨ wsClosed ι)) ∨
       (⌜err = GoInterface.nil ∧ sint.Z id = n ∧ ¬ empty⌝ ∗ wsCtl ι (n + 1) ∗
          ∃ (W : WatcherM) (σ : MvccState), Q σ ∗ wsReg ι id W ∗ wsSentLb ι W.stamp ∗
            mvccLb γ σ.kv ∗
            ⌜σ.pending = [] ∧
              W.range = { key := k, endNil := decide (endk = slice.nil), rangeEnd := e } ∧
              W.drops = ds ∧ W.startRev = sint.Z startRev ∧
              W.pos = (if startRev = W64 0 then σ.rev else (sint.Z startRev).toNat - 1)⌝)) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
