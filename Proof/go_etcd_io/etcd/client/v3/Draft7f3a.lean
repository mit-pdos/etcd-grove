/-
**k8s 7f-3a, the statements (S2 Draft, for etcd-grove-81's review; `notes/k8s-7f3a-draft.md`).**
Lean-first. Not linked: nothing imports this module, and no linked definition changes yet (Q1: no
`sorry` under a linked result). Each definition is the new form of an existing one, under the old
name with a `P` suffix; 7f-3b/3c replace the old definitions by these (and re-prove their users),
after the review. Only the pure laws relating the two forms are proved here.

* `OpFull.isRangeWatchP`: `isRangeWatch` without `o.base.prevKV = false` (`isRangeWatch_eq`).
* `prevKvOk o σ ev pk`: an event's `PrevKv` pointer: `nil` without `WithPrevKV`; with it, `nil`
  (always admitted: `issues/etcd-watch-prevkv-before-created.md`, Q5) or a `*KeyValue` holding the
  key's record at the revision before the event's (`σ.at (r - 1)`), the event not a create.
* `eventsPkAt`, `respAtP`: the consumer reads each event's `PrevKv` field (read-only).
* `watchStateRespOkP`, `watchStateElemP`, `watcher.Watch.specP`: the client's watch with them.
* `client.prevKvLogOk`, `client.rawRespOkP`: the same at the server's level (a watched log's state
  at `r - 1`, `mvcc.stateAt`; the key-value fixed, `mvcc.kvPtrFixed`).
* (`v3rpc.watchReqOkP`, `v3rpc.swsMuP`: adopted in 7f-3b as `v3rpc.watchReqOk` and `v3rpc.swsMu`.)
* (`WithRequireLeader.specGen` moved into `WithRequireLeader.spec`, the restated axiom: decision D1.)
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.WithRequireLeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver
  client

/-! ## The option (pure) -/

section pure
variable [GooseExts]

/-- A watch of the range of `o` from revision `rev`, with `WithPrevKV` allowed (7f-3a): as
`isRangeWatch`, without `o.base.prevKV = false`. -/
def OpFull.isRangeWatchP (rev : w64) (o : OpFull) : Bool :=
  decide (o.t = W64 1 ∧ o.base.rev = rev ∧ o.base.fragment = false ∧
    o.base.filterPut = false ∧ o.base.filterDelete = false)

/-- The old condition is the new one without `WithPrevKV`. -/
theorem OpFull.isRangeWatch_eq (rev : w64) (o : OpFull) :
    o.isRangeWatch rev = (o.isRangeWatchP rev && !o.base.prevKV) := by
  unfold OpFull.isRangeWatch OpFull.isRangeWatchP
  cases o.base.prevKV <;> simp [and_left_comm]

/-- An event is a create (`mvccpb.Event.IsCreate`, `v3rpc.IsCreateEvent`): `v3rpc.evIsCreate`
(7f-3b). -/
abbrev mvccEvIsCreate (ev : mvcc.EvM) : Prop := v3rpc.evIsCreate ev

end pure

/-! ## The client's watch -/

section client
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An event's `PrevKv` pointer `pk`** (persistent), for the state's event `ev` of a watch of `o`
read at `σ`: without `WithPrevKV`, `nil`; with it, `nil` (the server sends none for a create, after
a failed range, or before `recvLoop` records the watch's `prevKV` entry:
`issues/etcd-watch-prevkv-before-created.md`), or, the event not a create, a `*KeyValue` holding
the key's record at the revision before the event's (`v3rpc/watch.go:442-455`: a range of the key
at `ModRevision - 1`). -/
def prevKvOk (o : OpFull) (σ : KVState) (ev : mvcc.EvM) (pk : Loc) : IProp GF :=
  if o.base.prevKV then
    iprop(⌜pk = null⌝ ∨
      ∃ r : KVRec, ⌜¬ mvccEvIsCreate ev ∧ σ.at (sint.nat ev.kv.modRev - 1) !! ev.kv.key = some r⌝ ∗
        kvValAt pk (KVRec.toKv ev.kv.key r))
  else iprop(⌜pk = null⌝)

instance prevKvOk_persistent (o : OpFull) (σ : KVState) (ev : mvcc.EvM) (pk : Loc) :
    Persistent (prevKvOk (GF := GF) o σ ev pk) := by
  unfold prevKvOk; split <;> infer_instance

/-- Without `WithPrevKV` the pointer is `nil`. -/
theorem prevKvOk_noPrev (o : OpFull) (σ : KVState) (ev : mvcc.EvM) (pk : Loc)
    (h : o.base.prevKV = false) : prevKvOk (GF := GF) o σ ev pk ⊣⊢ ⌜pk = null⌝ := by
  unfold prevKvOk; rw [h]; simp

/-- `nil` is always allowed. -/
theorem prevKvOk_null (o : OpFull) (σ : KVState) (ev : mvcc.EvM) :
    ⊢ prevKvOk (GF := GF) o σ ev null := by
  unfold prevKvOk
  split
  · iintro; ileft; ipureintro; rfl
  · iintro; ipureintro; rfl

/-- The slice `sl` of `*mvccpb.Event` (read-only) holds events whose `PrevKv` fields are the
models' (`eventsAt`'s companion, 7f-3a). -/
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

/-- **A watch's response, as a read of the state, with `PrevKv`** (7f-3a): `watchStateRespOk`,
and each delivered event's `PrevKv` pointer `prevKvOk` of the state's event it is (vacuous for a
response without events: the range read is empty then). -/
def watchStateRespOkP (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop(watchStateRespOk o σ c c' v r ∗
    □ ∀ (i : Nat) (e : EvModel) (ev : mvcc.EvM), ⌜r.events[i]? = some e⌝ -∗
      ⌜(σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))[i]? = some ev⌝ -∗
      prevKvOk o σ ev e.prevKv)

/-- `watchStateElem` with `respAtP` and `watchStateRespOkP`. -/
def watchStateElemP (γk : KVNames) (γw : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF)
    (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (σ : KVState) (c c' : w64), respAtP v r ∗ □ Q σ ∗
    monoListIdxOwn γw.cur i.toNat c ∗ monoListIdxOwn γw.cur (i.toNat + 1) c' ∗
    watchStateRespOkP o σ c c' v r ∗ □ (⌜r.events ≠ []⌝ → Au) ∗ cmpOkOf γk v.CompactRevision')

/-- The new element gives the old one (the users at `prevKV = false` read what they read). -/
theorem watchStateElemP_elem (γk : KVNames) (γw : EtcdWatchNames) (o : OpFull)
    (Q : KVState → IProp GF) (Au : IProp GF) (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse) :
    watchStateElemP (GF := GF) γk γw o Q Au i v ⊢ watchStateElem γk γw o Q Au i v := by
  unfold watchStateElemP watchStateElem respAtP watchStateRespOkP
  iintro ⟨%r, %σ, %c, %c', ⟨Hr, -⟩, HQ, H1, H2, ⟨Hs, -⟩, HA, Hc⟩
  iexists r, σ, c, c'
  iframe

end client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`watcher.Watch`, with `WithPrevKV`** (7f-3a): `watcher.Watch.spec` with `isRangeWatchP` (any
`prevKV`) and `watchStateElemP` (each event's `PrevKv` field, `prevKvOk`). Everything else as
before. -/
abbrev watcher.Watch.specP : Prop :=
  ∀ (w : Loc) (V : WEnv GF) (γ : KVNames) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ∗ ⌜V.kst = γ.st⌝ ∗
      EtcdGrove.context.watchCtx ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatchP rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev ∧ watchSizeOk (opWatchModel key opts)⌝ ∗
      □ (⌜V.nm = 1 ∧ 0 < n⌝ → auth.authPubLbM (V.mem 0).2.E.authMode n) ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElemP V.kv γw (opWatchModel key opts).watchNorm Q
        iprop(□ (⌜V.nm = 1⌝ → watchCheckOk (V.mem 0).2.tag (V.mem 0).2.s V.conn
          (GoInterface.ok ctx) n (opWatchModel key opts).key (opWatchModel key opts).base.rangeEnd)))
        (fun _ => iprop(True)) ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) }}

end spec

/-! ## The server's level -/

namespace client

section raw
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An event's `PrevKv` pointer at the server's level** (persistent; 7f-3a): `prevKvOk` with a
watched log's state at the revision before (`mvcc.stateAt L (r - 1)`, which the send loop's range
at `ModRevision - 1` reads), the key-value fixed (`mvcc.kvPtrFixed`, as the event's own). -/
def prevKvLogOk (o : OpFull) (L : mvcc.Log) (ev : mvcc.EvM) (pk : Loc) : IProp GF :=
  if o.base.prevKV then
    iprop(⌜pk = null⌝ ∨
      ∃ kv : EtcdKv, ⌜¬ mvccEvIsCreate ev ∧
          mvcc.findKey ev.kv.key (mvcc.stateAt L (sint.nat ev.kv.modRev - 1)) = some kv⌝ ∗
        mvcc.kvPtrFixed pk kv)
  else iprop(⌜pk = null⌝)

instance prevKvLogOk_persistent (o : OpFull) (L : mvcc.Log) (ev : mvcc.EvM) (pk : Loc) :
    Persistent (prevKvLogOk (GF := GF) o L ev pk) := by
  unfold prevKvLogOk; split <;> infer_instance

/-- **`rawRespOk` with `PrevKv`** (7f-3a): as `rawRespOk`, but the events are the log's up to their
`PrevKv` pointers (`evModelOf` with the pointer erased), each pointer `prevKvLogOk` of its event. -/
def rawRespOkP (W : v3rpc.SrvW GF) (o : OpFull) (c c' : w64)
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
          r.events.map (fun e => { e with prevKv := null }) =
            List.zipWith evModelOf (rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1)) kvs⌝ ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc),
          ⌜(rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1))[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (e : EvModel),
          ⌜(rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1))[k]? = some ev⌝ →
          ⌜r.events[k]? = some e⌝ → prevKvLogOk o L ev e.prevKv)))

instance rawRespOkP_persistent (W : v3rpc.SrvW GF) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (rawRespOkP (GF := GF) W o c c' v r) := by
  unfold rawRespOkP; infer_instance

end raw

end client


end EtcdGrove
end Perennial
