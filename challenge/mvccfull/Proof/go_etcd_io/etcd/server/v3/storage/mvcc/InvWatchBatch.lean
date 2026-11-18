/-
The watcher group's batches (`watcher_group.go`: `eventBatch`, `watcherBatch`,
`newWatcherBatch`) and its choice of watchers (`choose`, `chooseAll`). Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The watcher group and the stream (unit 2)".

**Model.** An event is `EvM` (a put or a delete, its key-value, the previous one if any); an
`eventBatch` is `EventBatch` (its events, its count of revisions, `moreRev`), and
`eventBatch.add` is `ebAdd`, exactly. `newWatcherBatch` is `batchOf`: per member, the fold of
`ebAdd` over the events whose key its range holds at or above its `minRev` (`memberBatch`),
absent if there is none; the code's loops (the events in order, inside the members of the
event's key in the map's order) compute it whatever the order (`batchStepL_lookup`,
`batchOf_snoc`). `chooseAll`'s result is `minRevOf`: the least `minRev` of the members
(`2^63 - 1` if none), whatever the order (`minRevL_eq`).

**Representation.** The store's events are a persistent fact of their pointers (`evIs`: their
fields, the key-value read-only for good, `kvPtrFixed`). A batch holds its watcher's own copies
(`evOwn`, k8s 7f-3b: `newWatcherBatch` copies each event per watcher): the fields read-only
(`evRd`), the `PrevKv` field owned (`evPk`), which the response hands to its receiver.
`ownEventBatch eb B` owns the batch struct, its slice and its copies; `ownWatcherBatch wb Bm` the
map and each batch. The members' mutable fields are the caller's (`ownStates ST`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchGroup
public import Proof.go_etcd_io.etcd.cache.v3.InvWatcher
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.SavedProp
public import Perennial.Proof.sync.RWMutexGuard
public import Proof.go_etcd_io.etcd.cache.v3.EtcdModel
public import Lean
public import Perennial.Proof.context
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Code.google_golang_org.grpc.metadata
public import Perennial.GeneratedProof.context
public import Code.net
public import Code.google_golang_org.grpc.credentials
public import Code.google_golang_org.grpc.peer
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## Events and batches (pure) -/

/-- An `mvccpb.Event`: a put or a delete (`del`), its key-value, the previous one if any. -/
structure EvM where
  del : Bool
  kv : EtcdKv
  prevKv : Option EtcdKv

/-- `eventBatch`'s model: its events, its count of distinct revisions (`revs`), and the first
revision left out (`moreRev`, `0` if none). -/
structure EventBatch where
  evs : List EvM
  revs : w64
  moreRev : w64

/-! ## Ownership -/

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A `*mvccpb.KeyValue` holding `kv`, read-only for good (as `kvPtrIs true`, persistent). -/
def kvPtrFixed (p : Loc) (kv : EtcdKv) : IProp GF :=
  iprop(∃ (ks vs : GoSlice) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (uf : GoSlice) (sc : w32),
    ks ↦*□ kv.key ∗ vs ↦*□ kv.value ∗
    p ↦□ ({
      state' := st, Key' := ks, CreateRevision' := kv.createRev, ModRevision' := kv.modRev,
      Version' := kv.version, Value' := vs, Lease' := kv.lease, unknownFields' := uf,
      sizeCache' := sc } : go_etcd_io.etcd.api.v3.mvccpb.KeyValue))

/-- The type of an event: `Event_DELETE` or `Event_PUT`. -/
def evType (ev : EvM) : w32 := if ev.del then W32 1 else W32 0

/-- An event, read-only for good (events are shared by the batches of all watchers): its
type, its key-value, its previous key-value or `nil`. -/
def evIs (e : Loc) (ev : EvM) : IProp GF :=
  iprop(∃ (p q : Loc) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (uf : GoSlice) (sc : w32), ⌜e ≠ null ∧ p ≠ null⌝ ∗
    e ↦□ ({ state' := st, Type' := evType ev, Kv' := p, PrevKv' := q, unknownFields' := uf,
            sizeCache' := sc } : go_etcd_io.etcd.api.v3.mvccpb.Event) ∗
    kvPtrFixed p ev.kv ∗
    (match ev.prevKv with
     | none => ⌜q = null⌝
     | some pk => kvPtrFixed q pk))

/-! ### A watcher's own copy of an event (k8s 7f-3b)

`newWatcherBatch` (`watcher_group.go:79-96`) allocates a fresh `&mvccpb.Event{Type, Kv, PrevKv}`
per (watcher, event), and the batch's responses carry those copies; v3rpc's `sendWatch`
(`watch.go:447-455`) writes `PrevKv` into them. So a copy's `PrevKv` field is owned (`evPk`) by
whoever holds the copy (the batch, then the response), while its other fields and the key-value it
shares with the store's event are read-only for good (`evRd`). -/

/-- The `PrevKv` pointer `q` of an event whose previous key-value is `pk`: `nil` for none. -/
def prevKvIs (q : Loc) (pk : Option EtcdKv) : IProp GF :=
  match pk with
  | none => iprop(⌜q = null⌝)
  | some k => kvPtrFixed q k

/-- **An event's fields but `PrevKv`, read-only for good** (persistent): its type, its key-value
(a non-nil pointer, `kvPtrFixed`) and its protobuf bookkeeping. What the readers of an event
(`eventBatch.add`, the filters, `IsCreateEvent`) need. -/
def evRd (e : Loc) (ev : EvM) : IProp GF :=
  iprop(∃ (p : Loc) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (uf : GoSlice) (sc : w32), ⌜e ≠ null ∧ p ≠ null⌝ ∗
    e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"state"] ↦□ st ∗
    e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Type"] ↦□ evType ev ∗
    e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Kv"] ↦□ p ∗
    e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"unknownFields"] ↦□ uf ∗
    e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"sizeCache"] ↦□ sc ∗
    kvPtrFixed p ev.kv)

/-- **An event's `PrevKv` field, owned** (at the fraction `q`: a victim batch, under the watchable
store's lock): its pointer is `ev`'s previous key-value (`prevKvIs`). -/
def evPk (e : Loc) (ev : EvM) (q : Qp := 1) : IProp GF :=
  iprop(∃ pq : Loc, e.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"PrevKv"] ↦{DFrac.own q} pq ∗
    prevKvIs pq ev.prevKv)

/-- **A watcher's own copy of an event**: its fields read-only (`evRd`) and its `PrevKv` field
owned (`evPk`). -/
def evOwn (e : Loc) (ev : EvM) (q : Qp := 1) : IProp GF :=
  iprop(evRd e ev ∗ evPk e ev q)

/-- The batch at `eb` holds `B`: its fields, its slice of events (owned, with its capacity),
each event a copy of its own (`evOwn`, k8s 7f-3b: `newWatcherBatch` copies them); at the fraction
`q` (a victim batch, under the watchable store's lock). -/
def ownEventBatch (eb : Loc) (B : EventBatch) (q : Qp := 1) : IProp GF :=
  iprop(∃ (s : GoSlice) (ps : List Loc),
    typedPointsto eb ({ evs' := s, revs' := B.revs, moreRev' := B.moreRev } : eventBatch)
      (DFrac.own q) ∗
    ownSlice s ps (DFrac.own q) ∗ ownSliceCap Loc s (DFrac.own q) ∗ ⌜ps.length = B.evs.length⌝ ∗
    [∗list] x ∈ ps.zip B.evs, evOwn x.1 x.2 q)

/-- The watcher batch `wb` (a `map[*watcher]*eventBatch`) holds `Bm`: each member's batch,
owned, at a non-nil pointer. -/
def ownWatcherBatch (wb : GoMap) (Bm : GMap Loc EventBatch) (q : Qp := 1) : IProp GF :=
  iprop(∃ PB : GMap Loc (Loc × EventBatch),
    ownMap wb (DFrac.own q) (GMap.fmap Prod.fst PB) ∗ ⌜Bm = GMap.fmap Prod.snd PB⌝ ∗
    [∗map] _w ↦ p ∈ PB, ⌜p.1 ≠ null⌝ ∗ ownEventBatch p.1 p.2 q)

end reprs

end mvcc
end EtcdGrove
end Perennial
