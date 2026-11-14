/-
**The watch's responses, as reads of etcd's KV state: the definitions** (D47, 2026-10-26).
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
  that is not a progress notification (position kept), a progress notification at `p ≥ c`
  (position `p`; unless it is at the watch's start, `c = p = rev - 1`: `p ≤ σ.rev`, no event in
  `(c, p]`), or events: exactly
  `rangeEvents σ o (c + 1) (c' + 1)` for some `c < c' ≤ σ.rev` (`eventsIs`: each event's type,
  key, revision and key-value); when the position moves, `σ` is a well-formed small log's state
  through the new one (`kvLogOkTo`, D48);
* `watchStateElem`: the `i`-th response of a watch, with the update's `□ Q σ`, at the positions
  `i` and `i + 1` of the watch's cursor;
* `client.rawRespOk`: the same at the server's level (the client watcher's pipeline's, before the
  update fires): the events those of a watched log of the server (its certified lower bound of the
  notified log, `v3rpc.SrvW.histLb`), the progress notification's revision within one.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The events of the state (pure) -/

section pure
variable [GooseExts]

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
    ⌜¬ watchErr v ∧ r.isProgressNotify = true ∧ 0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z r.hdrRev ∧
      c' = r.hdrRev ∧
      ((sint.Z c = sint.Z r.hdrRev ∧ sint.Z c + 1 = sint.Z o.base.rev) ∨
        (sint.Z r.hdrRev ≤ (σ.rev : Int) ∧
          σ.rangeEvents o (sint.nat c + 1) (sint.nat r.hdrRev + 1) = [] ∧
          kvLogOkTo σ (sint.nat r.hdrRev)))⌝ ∨
    (⌜¬ watchErr v ∧ r.events ≠ [] ∧ 0 ≤ sint.Z c ∧ sint.Z c < sint.Z c' ∧
        sint.Z c' ≤ (σ.rev : Int) ∧
        (r.events.getLast?.map EvModel.rev) = some c' ∧ kvLogOkTo σ (sint.nat c')⌝ ∗
      eventsIs r.events (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))))

instance watchStateRespOk_persistent (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (watchStateRespOk (GF := GF) o σ c c' v r) := by
  unfold watchStateRespOk; infer_instance

open Iris.ProofMode in
/-- A response's header, owned (`watchHdrOwn`: a response with events owns its `Revision`), made
read-only (`hdrAt`, `respAt`'s). -/
theorem hdrAt_of_hdrOwn (h : Loc) (r : RespModel) :
    watchHdrOwn (GF := GF) h r ⊢ |==> hdrAt h r.hdrRev := by
  unfold watchHdrOwn
  split
  · iintro #H; imodintro; iexact H
  · iintro ⟨%hn, H⟩
    ipersist H
    imodintro
    unfold hdrAt
    iright
    iframe H
    ipureintro; exact hn

/-- **A watch response's compaction revision is the cluster's permit** (persistent; C3's watch side,
2026-11-02): none (`0`), or a positive revision at least the cluster's retention behind one its KV
has reached (`kvCmpPermit`). Margin: the code also gives that a compaction response's revision is
past the watch's next revision (mvcc sends one only when `w.minRev < compactRev`); not stated. -/
def cmpOkOf (γk : KVNames) (c : w64) : IProp GF :=
  iprop(⌜c = W64 0⌝ ∨ kvCmpPermit γk (sint.Z c))

instance cmpOkOf_persistent (γk : KVNames) (c : w64) : Persistent (cmpOkOf (GF := GF) γk c) := by
  unfold cmpOkOf; infer_instance

/-- No compaction revision is permitted. -/
theorem cmpOkOf_zero (γk : KVNames) : ⊢ cmpOkOf (GF := GF) γk (W64 0) := by
  iintro; iunfold cmpOkOf; ileft; ipureintro; rfl

/-- **A compaction revision's permit** (C3's watch side): a non-zero one is positive and its
revision plus the cluster's retention is reached. -/
theorem cmpOkOf_permit (γk : KVNames) (c : w64) (hc : c ≠ W64 0) :
    cmpOkOf (GF := GF) γk c ⊢ ⌜0 < sint.Z c⌝ ∗ kvRevLbZ γk (sint.Z c + γk.cret) := by
  iintro #H
  iunfold cmpOkOf at H
  icases H with (%h | #Hp)
  · exact absurd h hc
  iapply kvCmpPermit_revLb γk (sint.Z c) $$ Hp

/-- The same cluster's KV names agree on the permit. -/
theorem cmpOkOf_same (γk γk' : KVNames) (h : kvSame γk γk') (c : w64) :
    cmpOkOf (GF := GF) γk c ⊢ cmpOkOf γk' c := by
  unfold cmpOkOf; rw [kvCmpPermit_same γk γk' h]

/-- **The `i`-th response `v` of a watch of `o` with the read update's `Q`**: modelled by some `r`
(`respAt`: its events, header and flags), the update's `□ Q σ` at the state `σ` it fired at, and
`watchStateRespOk` at the positions `i` and `i + 1` of the watch's cursor, and (G2, 2026-10-30)
`Au` when the response has events (the caller's auth fact: `watcher.Watch.spec`'s gated row);
(C3's watch side, 2026-11-02) its compaction revision the permit of the cluster's KV names `γk`
(`cmpOkOf`). -/
def watchStateElem (γk : KVNames) (γw : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF)
    (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (σ : KVState) (c c' : w64), respAt v r ∗ □ Q σ ∗
    monoListIdxOwn γw.cur i.toNat c ∗ monoListIdxOwn γw.cur (i.toNat + 1) c' ∗
    watchStateRespOk o σ c c' v r ∗ □ (⌜r.events ≠ []⌝ → Au) ∗ cmpOkOf γk v.CompactRevision')

/-- **A delivered response's compaction revision is the cluster's permit** (C3's watch side). -/
theorem watchStateElem_cmp (γk : KVNames) (γw : EtcdWatchNames) (o : OpFull)
    (Q : KVState → IProp GF) (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) :
    watchStateElem (GF := GF) γk γw o Q Au i v ⊢
      watchStateElem γk γw o Q Au i v ∗ cmpOkOf γk v.CompactRevision' := by
  iintro H
  ihave #Hc : cmpOkOf γk v.CompactRevision' $$ [H]
  · iunfold watchStateElem at H
    icases H with ⟨%r, %σ, %c, %c', -, -, -, -, -, -, #Hc⟩
    iexact Hc
  iframe H Hc

/-- **A position of a watch of `o` with the read update's `Q`** (persistent; D48): the watch's start
(`c + 1` its revision), or a revision of a state the update fired at, well formed through it. -/
def posQ (o : OpFull) (Q : KVState → IProp GF) (c : w64) : IProp GF :=
  iprop(⌜sint.Z c + 1 = sint.Z o.base.rev⌝ ∨
    ∃ σ : KVState, □ Q σ ∗ ⌜0 ≤ sint.Z c ∧ sint.Z c ≤ (σ.rev : Int) ∧ kvLogOkTo σ (sint.nat c)⌝)

instance posQ_persistent (o : OpFull) (Q : KVState → IProp GF) (c : w64) :
    Persistent (posQ (GF := GF) o Q c) := by
  unfold posQ; infer_instance

open Iris.ProofMode in
/-- **A response moves the watch to a position**: the one before, the start, or a revision of the
state it read. -/
theorem posQ_of_resp (o : OpFull) (Q : KVState → IProp GF) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    posQ (GF := GF) o Q c ∗ □ Q σ ∗ watchStateRespOk o σ c c' v r ⊢ posQ o Q c' := by
  iintro ⟨#Hc, #HQ, #Hr⟩
  unfold watchStateRespOk
  icases Hr with (⟨%H, -⟩ | %H | %H | ⟨%H, -⟩)
  · rw [H.2]; iexact Hc
  · rw [H.2.2.2]; iexact Hc
  · obtain ⟨-, -, h0, hle, hc', hcase⟩ := H
    rcases hcase with ⟨heq, hst⟩ | ⟨hrv, -, hok⟩
    · unfold posQ; ileft; ipureintro; rw [hc', ← heq]; exact hst
    · unfold posQ; iright; iexists σ; iframe HQ; ipureintro
      rw [hc']; exact ⟨by omega, hrv, hok⟩
  · obtain ⟨-, -, h0, hlt, hrv, -, hok⟩ := H
    unfold posQ; iright; iexists σ; iframe HQ; ipureintro
    exact ⟨by omega, hrv, hok⟩

/-! ## Previous key-values (k8s 7f-3c, `WithPrevKV`) -/

/-- **An event's `PrevKv` pointer `pk`** (persistent; k8s 7f-3a/3c), for the state's event `ev` of a
watch of `o` read at `σ`: without `WithPrevKV`, `nil`; with it, `nil` (the server sends none for a
create, after a failed range, or before `recvLoop` records the watch's `prevKV` entry:
`issues/etcd-watch-prevkv-before-created.md`), or, the event not a create, a `*KeyValue` holding
the key's record at the revision before the event's (`v3rpc/watch.go:442-455`: a range of the key
at `ModRevision - 1`). -/
def prevKvOk (o : OpFull) (σ : KVState) (ev : mvcc.EvM) (pk : Loc) : IProp GF :=
  if o.base.prevKV then
    iprop(⌜pk = null⌝ ∨
      ∃ r : KVRec, ⌜¬ v3rpc.evIsCreate ev ∧ σ.at (sint.nat ev.kv.modRev - 1) !! ev.kv.key = some r⌝ ∗
        kvValAt pk (KVRec.toKv ev.kv.key r))
  else iprop(⌜pk = null⌝)

instance prevKvOk_persistent (o : OpFull) (σ : KVState) (ev : mvcc.EvM) (pk : Loc) :
    Persistent (prevKvOk (GF := GF) o σ ev pk) := by
  unfold prevKvOk; split <;> infer_instance

/-- Without `WithPrevKV` the pointer is `nil`. -/
theorem prevKvOk_noPrev (o : OpFull) (σ : KVState) (ev : mvcc.EvM) (pk : Loc)
    (h : o.base.prevKV = false) : prevKvOk (GF := GF) o σ ev pk ⊣⊢ ⌜pk = null⌝ := by
  unfold prevKvOk; rw [h]; simp

open Iris.ProofMode in
/-- `nil` is always allowed. -/
theorem prevKvOk_null (o : OpFull) (σ : KVState) (ev : mvcc.EvM) :
    ⊢ prevKvOk (GF := GF) o σ ev null := by
  unfold prevKvOk
  split
  · iintro; ileft; ipureintro; rfl
  · iintro; ipureintro; rfl

/-- The slice `sl` of `*mvccpb.Event` (read-only) holds events whose `PrevKv` fields are the
models' (`eventsAt`'s companion). -/
def eventsPkAt (sl : GoSlice) (evs : List EvModel) : IProp GF :=
  iprop(∃ ls : List Loc, sl ↦*□ ls ∗ ⌜ls.length = evs.length⌝ ∗
    □ (∀ (i : Nat) (ev : Loc) (e : EvModel), ⌜ls[i]? = some ev⌝ -∗ ⌜evs[i]? = some e⌝ -∗
      structFieldRef mvccpb.Event go!"PrevKv" ev ↦□ e.prevKv))

instance eventsPkAt_persistent (sl : GoSlice) (evs : List EvModel) :
    Persistent (eventsPkAt (GF := GF) sl evs) := by
  unfold eventsPkAt; infer_instance

/-- `respAt` with the events' `PrevKv` fields. -/
def respAtP (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop(respAt resp r ∗ eventsPkAt resp.Events' r.events)

instance respAtP_persistent (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (respAtP (GF := GF) resp r) := by
  unfold respAtP; infer_instance

/-- The pointers' part of a response, read at `σ`: each delivered event's `PrevKv` pointer
`prevKvOk` of the state's event it is. -/
def respPkOk (o : OpFull) (σ : KVState) (c c' : w64) (r : RespModel) : IProp GF :=
  iprop(□ ∀ (i : Nat) (e : EvModel) (ev : mvcc.EvM), ⌜r.events[i]? = some e⌝ -∗
      ⌜(σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))[i]? = some ev⌝ -∗
      prevKvOk o σ ev e.prevKv)

instance respPkOk_persistent (o : OpFull) (σ : KVState) (c c' : w64) (r : RespModel) :
    Persistent (respPkOk (GF := GF) o σ c c' r) := by
  unfold respPkOk; infer_instance

/-- **A watch's response, as a read of the state, with `PrevKv`** (k8s 7f-3a/3c):
`watchStateRespOk`, and each delivered event's `PrevKv` pointer `prevKvOk` of the state's event it
is (vacuous for a response without events: the range read is empty then). -/
def watchStateRespOkP (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop(watchStateRespOk o σ c c' v r ∗ respPkOk o σ c c' r)

instance watchStateRespOkP_persistent (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (watchStateRespOkP (GF := GF) o σ c c' v r) := by
  unfold watchStateRespOkP; infer_instance

open Iris.ProofMode in
/-- An empty range read has no pointer to say anything of. -/
theorem respPkOk_nil (o : OpFull) (σ : KVState) (c c' : w64) (r : RespModel)
    (h : σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1) = []) :
    ⊢ respPkOk (GF := GF) o σ c c' r := by
  unfold respPkOk
  iintro !> %i %e %ev %_ %hev
  rw [h] at hev; simp at hev

/-- `watchStateElem` with `respAtP` and `watchStateRespOkP` (k8s 7f-3a/3c). -/
def watchStateElemP (γk : KVNames) (γw : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF)
    (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (σ : KVState) (c c' : w64), respAtP v r ∗ □ Q σ ∗
    monoListIdxOwn γw.cur i.toNat c ∗ monoListIdxOwn γw.cur (i.toNat + 1) c' ∗
    watchStateRespOkP o σ c c' v r ∗ □ (⌜r.events ≠ []⌝ → Au) ∗ cmpOkOf γk v.CompactRevision')

open Iris.ProofMode in
/-- **The new element gives the old one** (the users at `prevKV = false` read what they read). -/
theorem watchStateElemP_elem (γk : KVNames) (γw : EtcdWatchNames) (o : OpFull)
    (Q : KVState → IProp GF) (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) :
    watchStateElemP (GF := GF) γk γw o Q Au i v ⊢ watchStateElem γk γw o Q Au i v := by
  unfold watchStateElemP watchStateElem respAtP watchStateRespOkP
  iintro ⟨%r, %σ, %c, %c', ⟨Hr, -⟩, HQ, H1, H2, ⟨Hs, -⟩, HA, Hc⟩
  iexists r, σ, c, c'
  iframe

end resp

namespace client

/-! ## The same, at the server's level (the pipeline's, before the update fires) -/

section raw
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The client's model of an mvcc event at `ev` whose key-value is at `kv`. -/
def evModelOf (ev : mvcc.EvM) (kv : Loc) : EvModel :=
  { typ := mvcc.evType ev, key := ev.kv.key, kv := kv, rev := ev.kv.modRev }

/-- An event model without its `PrevKv` pointer (the server-level equations read the events up
to their pointers). -/
def _root_.Perennial.EtcdGrove.EvModel.erasePk (e : EvModel) : EvModel := { e with prevKv := null }

@[simp] theorem evModelOf_erasePk (ev : mvcc.EvM) (kv : Loc) :
    (evModelOf ev kv).erasePk = evModelOf ev kv := rfl

@[simp] theorem _root_.Perennial.EtcdGrove.EvModel.erasePk_rev (e : EvModel) : e.erasePk.rev = e.rev := rfl

/-- The events `es` with the `PrevKv` pointers `qs`. -/
def withPk (es : List EvModel) (qs : List Loc) : List EvModel :=
  List.zipWith (fun e q => { e with prevKv := q }) es qs

theorem withPk_length (es : List EvModel) (qs : List Loc) (h : qs.length = es.length) :
    (withPk es qs).length = es.length := by
  unfold withPk; simp [h]

theorem withPk_erase (es : List EvModel) (qs : List Loc) (h : qs.length = es.length) :
    (withPk es qs).map EvModel.erasePk = es.map EvModel.erasePk := by
  induction es generalizing qs with
  | nil => cases qs <;> rfl
  | cons e es ih =>
    cases qs with
    | nil => simp at h
    | cons q qs =>
      simp only [withPk, List.zipWith_cons_cons, List.map_cons] at ih ⊢
      rw [ih qs (by simpa using h)]; rfl

theorem withPk_revs (es : List EvModel) (qs : List Loc) (h : qs.length = es.length) :
    (withPk es qs).map EvModel.rev = es.map EvModel.rev := by
  have := congrArg (List.map EvModel.rev) (withPk_erase es qs h)
  simpa [List.map_map, Function.comp_def] using this

theorem withPk_getElem? (es : List EvModel) (qs : List Loc) (i : Nat) :
    (withPk es qs)[i]? = (match es[i]?, qs[i]? with
      | some e, some q => some { e with prevKv := q }
      | _, _ => none) := by
  unfold withPk; rw [List.getElem?_zipWith]
  cases es[i]? <;> cases qs[i]? <;> rfl

theorem zipWith_evModelOf_erase (evs : List mvcc.EvM) (kvs : List Loc) :
    (List.zipWith evModelOf evs kvs).map EvModel.erasePk = List.zipWith evModelOf evs kvs := by
  rw [List.map_zipWith]; rfl

/-- **An event's `PrevKv` pointer at the server's level** (persistent; k8s 7f-3a/3c): `prevKvOk`
with a watched log's state at the revision before (`mvcc.stateAt L (r - 1)`, which the send loop's
range at `ModRevision - 1` reads), the key-value fixed (`mvcc.kvPtrFixed`, as the event's own). -/
def prevKvLogOk (o : OpFull) (L : mvcc.Log) (ev : mvcc.EvM) (pk : Loc) : IProp GF :=
  if o.base.prevKV then
    iprop(⌜pk = null⌝ ∨
      ∃ kv : EtcdKv, ⌜¬ v3rpc.evIsCreate ev ∧
          mvcc.findKey ev.kv.key (mvcc.stateAt L (sint.nat ev.kv.modRev - 1)) = some kv⌝ ∗
        mvcc.kvPtrFixed pk kv)
  else iprop(⌜pk = null⌝)

instance prevKvLogOk_persistent (o : OpFull) (L : mvcc.Log) (ev : mvcc.EvM) (pk : Loc) :
    Persistent (prevKvLogOk (GF := GF) o L ev pk) := by
  unfold prevKvLogOk; split <;> infer_instance

/-- **A response, at the server's level** (the client watcher's pipeline's second cursor; see the
file header): as `watchStateRespOk`, but the events and the progress notification's revision are
a watched log's of the server's watch facts `W` (strict M1: a certified lower bound of its
notified log, `□ W.histLb`; until M1 mvcc's `evLog`, sealed and certified), the events'
key-values fixed (`mvcc.kvPtrFixed`, the API's `evIs`'s); (k8s 7f-3c, the Draft's `rawRespOkP`)
the events the log's up to their `PrevKv` pointers, each pointer `prevKvLogOk` of its event. -/
def rawRespOk (W : v3rpc.SrvW GF) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop((⌜watchErr v ∧ c' = c⌝ ∗ statusErrOk v.closeErr') ∨
    ⌜¬ watchErr v ∧ r.events = [] ∧ r.isProgressNotify = false ∧ c' = c⌝ ∨
    (⌜¬ watchErr v ∧ r.isProgressNotify = true ∧ 0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z r.hdrRev ∧
        c' = r.hdrRev ∧ sint.Z r.hdrRev < 2 ^ 63 - 1⌝ ∗
      (⌜sint.Z c = sint.Z r.hdrRev⌝ ∨
        ∃ L : mvcc.Log, □ W.histLb L ∗ ⌜sint.Z r.hdrRev < L.length ∧
          rangeLogEvents L o (sint.nat c + 1) (sint.nat r.hdrRev + 1) = []⌝)) ∨
    (⌜¬ watchErr v ∧ r.events ≠ [] ∧ 0 ≤ sint.Z c ∧ sint.Z c < sint.Z c' ∧
        (r.events.getLast?.map EvModel.rev) = some c'⌝ ∗
      ∃ (L : mvcc.Log) (kvs : List Loc), □ W.histLb L ∗
        ⌜sint.Z c' < L.length ∧ kvs.length = (rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1)).length ∧
          r.events.map EvModel.erasePk =
            List.zipWith evModelOf (rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1)) kvs⌝ ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc),
          ⌜(rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1))[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (e : EvModel),
          ⌜(rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1))[k]? = some ev⌝ →
          ⌜r.events[k]? = some e⌝ → prevKvLogOk o L ev e.prevKv)))

instance rawRespOk_persistent (W : v3rpc.SrvW GF) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (rawRespOk (GF := GF) W o c c' v r) := by
  unfold rawRespOk; infer_instance

end raw

end client

end EtcdGrove
end Perennial
