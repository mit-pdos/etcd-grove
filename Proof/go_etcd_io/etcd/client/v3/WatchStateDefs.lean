/-
**The watch's responses, as reads of etcd's KV state: the definitions** (D46, 2026-10-26).
Lean-first (no Rocq counterpart). `WatchState.lean` has the triple (`watcher.Watch.specσ`) and the
firing of the caller's read update; the client watcher's pipeline (`InvWatch.lean`, ...) reads these.

* `KVState.revEvents σ r`: revision `r`'s events, one per change in order, as
  `watchableStoreTxnWrite.End`/`kvsToEvents` make them (`mvcc.evsOfRevM`: a put's event carries
  the key-value the put wrote, a delete's the key with `ModRevision = r`);
* `KVState.rangeEvents σ o lo hi`: the events of the revisions `[lo, hi)` whose key is in the
  range of `o`, in revision order (`rangeEvents`/`kvsToEvents`' filter); at a log's state they are
  the log's (`rangeEvents_kvStateOf`, `mvcc.logEvents`);
* `watchStateRespOk o σ c c' v r`: a response `v` (modelled by `r`), received when the stream is
  at revision `c` and leaving it at `c'`, is an error (position kept), a response without events
  that is not a progress notification (position kept), a progress notification at `p` (if `p > c`:
  `p ≤ σ.rev`, no event in `(c, p]`, position `p`; else the position kept), or events: exactly
  `rangeEvents σ o (c + 1) (c' + 1)` for some `c < c' ≤ σ.rev` (`eventsIs`: each event's type,
  key, revision and key-value);
* `watchStateElem`: the `i`-th response of a watch, with the update's `□ Q σ`, at the positions
  `i` and `i + 1` of the watch's cursor;
* `client.rawRespOk`: the same at the server's level (the client watcher's pipeline's, before the
  update fires): the events those of a watched log of the server (`mvcc.evLog`), the progress
  notification's revision within one.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The events of the state (pure) -/

section pure
variable [ext : FfiSyntax]

/-- **Revision `r`'s events in the state `σ`**: one per change of the revision, in order, each the
key-value the change wrote at `r` (a put's, from the store before the revision and the changes up
to it) or the deleted key with `ModRevision = r` (`mvcc.evsOfRevM`, as
`watchableStoreTxnWrite.End` and `kvsToEvents` make them). -/
def KVState.revEvents (σ : KVState) (r : Nat) : List mvcc.EvM :=
  mvcc.evsOfRevM r (σ.at (r - 1)).kvs (σ.changesAt r)

/-- **The events of the revisions `[lo, hi)` in the range of `o`**, in revision order (etcd's
`rangeEvents` over the key bucket, filtered by the watcher's range). -/
def KVState.rangeEvents (σ : KVState) (o : OpFull) (lo hi : Nat) : List mvcc.EvM :=
  (((List.range' lo (hi - lo)).map σ.revEvents).flatten).filter
    fun ev => inRange o.key o.base.rangeEnd ev.kv.key

/-- **A log's events of the revisions `[lo, hi)` in the range of `o`** (mvcc's watch events,
filtered by the range). -/
def rangeLogEvents (L : mvcc.Log) (o : OpFull) (lo hi : Nat) : List mvcc.EvM :=
  (mvcc.logEvents L lo hi).filter fun ev => inRange o.key o.base.rangeEnd ev.kv.key

/-- At a log's state, a later revision's events are the log's (mvcc's watch events of it). -/
theorem revEvents_kvStateOf (l : mvcc.Log) (r : Nat) (h0 : 0 < r) (hr : r ≤ l.length - 1) :
    (kvStateOf l).revEvents r = mvcc.evsOfRevM r (mvcc.stateAt l (r - 1)) (l.getD r []) := by
  unfold KVState.revEvents
  rw [kvStateOf_at_kvs l (r - 1) (by omega), kvStateOf_changesAt l r h0]

/-- **At a log's state, the range's events are the log's** (its revisions from `lo ≥ 1` below
`hi ≤ l.length`): what the server sends. -/
theorem rangeEvents_kvStateOf (l : mvcc.Log) (o : OpFull) (lo hi : Nat) (h0 : 0 < lo)
    (hh : hi ≤ l.length) :
    (kvStateOf l).rangeEvents o lo hi = rangeLogEvents l o lo hi := by
  unfold KVState.rangeEvents rangeLogEvents mvcc.logEvents
  congr 2
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range'] at hm
  rw [revEvents_kvStateOf l m (by omega) (by omega)]

/-- A log's range events agree with a longer log's on the revisions it has. -/
theorem rangeLogEvents_prefix {L C : mvcc.Log} (hp : L <+: C) (o : OpFull) {lo hi : Nat}
    (hh : hi ≤ L.length) : rangeLogEvents L o lo hi = rangeLogEvents C o lo hi := by
  unfold rangeLogEvents; rw [mvcc.logEvents_prefix hp hh]

end pure

/-! ## A response, as a read of the state -/

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A delivered event is the state's event `ev`** (persistent): its type (`PUT` `0`, `DELETE`
`1`), key and revision, and its `*KeyValue`'s fields `ev`'s (a delete's the key and `ModRevision`
alone, the others empty, as etcd sends them). -/
def eventIs (e : EvModel) (ev : mvcc.EvM) : IProp GF :=
  iprop(⌜e.typ = (if ev.del then W32 1 else W32 0) ∧ e.key = ev.kv.key ∧ e.rev = ev.kv.modRev⌝ ∗
    kvValAt e.kv ev.kv)

instance eventIs_persistent (e : EvModel) (ev : mvcc.EvM) : Persistent (eventIs (GF := GF) e ev) := by
  unfold eventIs; infer_instance

/-- **The delivered events are the state's events `evs`**, one by one. -/
def eventsIs (es : List EvModel) (evs : List mvcc.EvM) : IProp GF :=
  iprop(⌜es.length = evs.length⌝ ∗
    □ ∀ (i : Nat) (e : EvModel) (ev : mvcc.EvM), ⌜es[i]? = some e⌝ -∗ ⌜evs[i]? = some ev⌝ -∗
      eventIs e ev)

instance eventsIs_persistent (es : List EvModel) (evs : List mvcc.EvM) :
    Persistent (eventsIs (GF := GF) es evs) := by
  unfold eventsIs; infer_instance

/-- **A watch's response `v` (modelled by `r`) as a read of the state `σ`**, received when the
stream is at revision `c` and leaving it at `c'` (see the file header). -/
def watchStateRespOk (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop((⌜watchErr v ∧ c' = c⌝ ∗ statusErrOk v.closeErr') ∨
    ⌜¬ watchErr v ∧ r.events = [] ∧ r.isProgressNotify = false ∧ c' = c⌝ ∨
    ⌜¬ watchErr v ∧ r.isProgressNotify = true ∧ 0 ≤ sint.Z r.hdrRev ∧
      (sint.Z c < sint.Z r.hdrRev → c' = r.hdrRev ∧ sint.Z r.hdrRev ≤ (σ.rev : Int) ∧
        σ.rangeEvents o (sint.nat c + 1) (sint.nat r.hdrRev + 1) = []) ∧
      (sint.Z r.hdrRev ≤ sint.Z c → c' = c)⌝ ∨
    (⌜¬ watchErr v ∧ r.events ≠ [] ∧ 0 ≤ sint.Z c ∧ sint.Z c < sint.Z c' ∧
        sint.Z c' ≤ (σ.rev : Int) ∧
        (r.events.getLast?.map EvModel.rev) = some c'⌝ ∗
      eventsIs r.events (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))))

instance watchStateRespOk_persistent (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (watchStateRespOk (GF := GF) o σ c c' v r) := by
  unfold watchStateRespOk; infer_instance

/-- **The `i`-th response `v` of a watch of `o` with the read update's `Q`**: modelled by some `r`
(`respAt`: its events, header and flags), the update's `□ Q σ` at the state `σ` it fired at, and
`watchStateRespOk` at the positions `i` and `i + 1` of the watch's cursor. -/
def watchStateElem (γw : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF) (i : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (σ : KVState) (c c' : w64), respAt v r ∗ □ Q σ ∗
    monoListIdxOwn γw.cur i.toNat c ∗ monoListIdxOwn γw.cur (i.toNat + 1) c' ∗
    watchStateRespOk o σ c c' v r)

end resp

namespace client

/-! ## The same, at the server's level (the pipeline's, before the update fires) -/

section raw
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The client's model of an mvcc event at `ev` whose key-value is at `kv`. -/
def evModelOf (ev : mvcc.EvM) (kv : Loc) : EvModel :=
  { typ := mvcc.evType ev, key := ev.kv.key, kv := kv, rev := ev.kv.modRev }

/-- **A response, at the server's level** (the client watcher's pipeline's second cursor; see the
file header): as `watchStateRespOk`, but the events and the progress notification's revision are
a watched log's of the server's store `γs` (`mvcc.evLog`: sealed and certified), the events'
key-values fixed (`mvcc.kvPtrFixed`). -/
def rawRespOk (γs : mvcc.StoreNames) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop((⌜watchErr v ∧ c' = c⌝ ∗ statusErrOk v.closeErr') ∨
    ⌜¬ watchErr v ∧ r.events = [] ∧ r.isProgressNotify = false ∧ c' = c⌝ ∨
    (⌜¬ watchErr v ∧ r.isProgressNotify = true ∧ 0 ≤ sint.Z r.hdrRev⌝ ∗
      ((⌜sint.Z c < sint.Z r.hdrRev ∧ c' = r.hdrRev ∧ 0 ≤ sint.Z c⌝ ∗
          ∃ L : mvcc.Log, mvcc.evLog γs L ∗ ⌜sint.Z r.hdrRev < L.length ∧
            rangeLogEvents L o (sint.nat c + 1) (sint.nat r.hdrRev + 1) = []⌝) ∨
        ⌜sint.Z r.hdrRev ≤ sint.Z c ∧ c' = c⌝)) ∨
    (⌜¬ watchErr v ∧ r.events ≠ [] ∧ 0 ≤ sint.Z c ∧ sint.Z c < sint.Z c' ∧
        (r.events.getLast?.map EvModel.rev) = some c'⌝ ∗
      ∃ (L : mvcc.Log) (kvs : List Loc), mvcc.evLog γs L ∗
        ⌜sint.Z c' < L.length ∧ kvs.length = (rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1)).length ∧
          r.events = List.zipWith evModelOf (rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1)) kvs⌝ ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc),
          ⌜(rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1))[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv)))

instance rawRespOk_persistent (γs : mvcc.StoreNames) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (rawRespOk (GF := GF) γs o c c' v r) := by
  unfold rawRespOk; infer_instance

end raw

end client

end EtcdGrove
end Perennial
