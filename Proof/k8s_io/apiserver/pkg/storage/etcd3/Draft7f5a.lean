/-
Lean-first (no Rocq counterpart).

# k8s 7f-5a-D: the Draft of the etcd3 watcher's serial branch (UNLINKED; hard stop S3)

Statements only, no proofs; `notes/k8s-7f5a-draft.md` explains each in plain words. Nothing imports
this file. After etcd-grove-81's review, its definitions move to `WatchDefs.lean` (the vocabulary)
and `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean` (the triple), and this file goes.

1. **The ideal stream** (pure, generic in the store's object type, over etcd's history read as a
   `KVState`): `KWEv` (a watch event as the consumer sees it), `kEvOfL` (an etcd event's watch event,
   as `transform` computes it from the event and the key's record at the revision before),
   `kInitialL` (a watch-list's initial events), `KTail` (the events of a watch from a cursor, with
   progress bookmarks), `kModeOf` (what the request asks: initial events, the initial-events-end
   bookmark, the requested revision) and **`kStreamOk`**: the events received, Error events removed,
   are a prefix of the ideal stream.
2. **The consumer's view**, `k8sWatch`: `ResultChan()` returns an SPSC channel (`isSpsc`, the
   consumer's half) whose `i`-th element is a `watch.Event` (`wevAt`) and carries the persistent
   fact that the first `i + 1` events' models are `kStreamOk` at a state the caller's read update
   fired at; `Stop()` is callable at any time.
3. **`store.Watch.spec`** (`Draft.store.Watch.spec`).
4. **The protocol** (the proof's ghost state, internal): `KRaw` (an `*event` the producer queues),
   `kRawStreamOk`, `kInElem` (the `incomingEventChan` SPSC's element), `kResInv` (the `resultChan`'s
   two producers: the producer token in an invariant).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s
namespace Draft

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-! ## 1. The ideal stream (pure) -/

section pure
variable [GooseExts]
variable {Obj : Type}

/-- **A watch event as the consumer sees it**: its type `t` (`0` Added, `1` Modified, `2` Deleted,
`3` Bookmark, `4` Error: the driver's `WEv` numbering), its object's body `o` and resource version
`rv`, and whether the object carries the initial-events-end annotation. An Error event's `o`, `rv`
and `ann` mean nothing (`wevAt` reads none of them). -/
structure KWEv (Obj : Type) where
  t : Nat
  o : Obj
  rv : Nat
  ann : Bool

/-- The events that are not errors. -/
def kNonErr (evs : List (KWEv Obj)) : List (KWEv Obj) := evs.filter fun e => e.t ≠ 4

/-- The object a stored value decodes to (`ObjSpec.dec`'s object). -/
def kDecObj (dec : Dec Obj) (v : GoString) : Option Obj := (dec v).map Prod.fst

/-- The key's record at the revision before the event's (what the client's `PrevKv` holds when it
is not `nil`: `prevKvOk`). -/
def kPrevAt (σ : KVState) (ev : mvcc.EvM) : Option KVRec :=
  σ.at (sint.nat ev.kv.modRev - 1) !! ev.kv.key

/-- **An etcd event's watch event** (`parseEvent` then `transform`, `watcher.go:676-747`), at the
history `σ`, for the predicate `sel` (empty: `emp`): a delete gives Deleted with the previous object
(at the delete's revision) if it passes; a create gives Added with the new object if it passes; an
update gives Modified (always, for an empty predicate), or Modified/Added/Deleted as the new and the
previous object pass. None if filtered out, or if a value does not decode (which `kvWfHist` excludes
under the store's prefix; the watcher would send an Error event and stop). -/
def kEvOfL (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (σ : KVState) (ev : mvcc.EvM) :
    Option (KWEv Obj) :=
  let r := sint.nat ev.kv.modRev
  let prev := (kPrevAt σ ev).bind fun p => kDecObj dec p.value
  if ev.del then prev.bind fun o => if sel o then some ⟨2, o, r, false⟩ else none
  else (kDecObj dec ev.kv.value).bind fun o =>
    if decide (ev.kv.createRev = ev.kv.modRev) then
      (if sel o then some ⟨0, o, r, false⟩ else none)
    else if emp then some ⟨1, o, r, false⟩
    else prev.bind fun o' =>
      if sel o && sel o' then some ⟨1, o, r, false⟩
      else if sel o then some ⟨0, o, r, false⟩
      else if sel o' then some ⟨2, o', r, false⟩
      else none

/-- **A watch-list's initial events** at the store `s` (`syncPaginated`, then `parseKV` and
`transform`): an Added event for each key-value in scope (`inS`) whose object passes, in key order,
at its mod revision. -/
def kInitialL (dec : Dec Obj) (sel : Obj → Bool) (inS : GoString → Bool) (s : KVStore) :
    List (KWEv Obj) :=
  (s.kvs.filter fun v => inS v.key).filterMap fun v =>
    (kDecObj dec v.value).bind fun o => if sel o then some ⟨0, o, sint.nat v.modRev, false⟩ else none

/-- etcd's events of the revisions `[lo, hi)` of keys in scope (the client watch's range), in order. -/
def kRangeEvsL (σ : KVState) (inS : GoString → Bool) (lo hi : Nat) : List mvcc.EvM :=
  (((List.range' lo (hi - lo)).map σ.revEvents).flatten).filter fun ev => inS ev.kv.key

/-- Their watch events. -/
def kEventsInL (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (σ : KVState)
    (inS : GoString → Bool) (lo hi : Nat) : List (KWEv Obj) :=
  (kRangeEvsL σ inS lo hi).filterMap (kEvOfL dec sel emp σ)

/-- **A watch's events from the cursor `c`** (the last revision it reported), at the history `σ`:
the watch events of whole revisions past the cursor, in order, none missing, none repeated, and
progress bookmarks (object `z`, the zero object `newFunc()` makes, at the bookmark's revision, no
annotation) at revisions `p` with no etcd event in scope in `(c, p]`. -/
inductive KTail (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ : KVState)
    (inS : GoString → Bool) : Nat → List (KWEv Obj) → Prop
  | nil (c : Nat) : KTail dec sel emp z σ inS c []
  | chg (c r : Nat) (rest : List (KWEv Obj)) : c < r → r ≤ σ.rev →
      KTail dec sel emp z σ inS r rest →
      KTail dec sel emp z σ inS c (kEventsInL dec sel emp σ inS (c + 1) (r + 1) ++ rest)
  | bm (c p : Nat) (rest : List (KWEv Obj)) : c ≤ p → p ≤ σ.rev →
      kRangeEvsL σ inS (c + 1) (p + 1) = [] →
      KTail dec sel emp z σ inS p rest →
      KTail dec sel emp z σ inS c (⟨3, z, p, false⟩ :: rest)

/-- **What a watch request asks** (with `WatchList` on): initial events (`areInitialEventsRequired`:
`SendInitialEvents` unset at resource version 0, the legacy case, or set to true), the
initial-events-end bookmark (`isInitialEventsEndBookmarkRequired`: `SendInitialEvents` true and
`AllowWatchBookmarks`), and the requested revision. -/
structure KWatchMode where
  forceInit : Bool
  bmReq : Bool
  req : Nat

/-- The mode of a request (`SendInitialEvents` as `sie`, `AllowWatchBookmarks` as `allowBm`, the
parsed resource version `n`). -/
def kModeOf (sie : Option Bool) (allowBm : Bool) (n : w64) : KWatchMode :=
  { forceInit := decide ((sie = none ∧ uint.nat n = 0) ∨ sie = some true),
    bmReq := decide (sie = some true ∧ allowBm = true),
    req := uint.nat n }

/-- **The events received are a prefix of the ideal stream** (at the history `σ`, Error events
removed wherever they are: `nonissues/k8s-etcd3-watcher-events-after-error.md`):
- with initial events: the initial events at some revision `r0` (at least the requested one, and
  1), then the annotated bookmark at `r0` if asked, then a tail from `r0`;
- without: a tail from some cursor `s0`, the requested revision when positive (for 0 with
  `SendInitialEvents` false, the store's current revision when the watch started). -/
def kStreamOk (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (inS : GoString → Bool)
    (m : KWatchMode) (σ : KVState) (evs : List (KWEv Obj)) : Prop :=
  (∀ e ∈ evs, e.t ≤ 4) ∧
  if m.forceInit then
    ∃ r0 full, max m.req 1 ≤ r0 ∧ r0 ≤ σ.rev ∧ KTail dec sel emp z σ inS r0 full ∧
      kNonErr evs <+: kInitialL dec sel inS (σ.at r0) ++
        ((if m.bmReq then [⟨3, z, r0, true⟩] else []) ++ full)
  else ∃ s0 full, (0 < m.req → s0 = m.req) ∧ KTail dec sel emp z σ inS s0 full ∧
      kNonErr evs <+: full

/-! ### The protocol's pure part: the raw events the producer queues -/

/-- **An `*event` the producer (`startWatching`) queues**: an initial key-value (`parseKV`), an etcd
event (`parseEvent`), or a bookmark at a revision (`progressNotifyEvent`, annotated for the
initial-events-end one). -/
inductive KRaw where
  | kv (v : EtcdKv)
  | ev (e : mvcc.EvM)
  | bm (rev : Nat) (ann : Bool)

/-- **What the processing goroutine makes of a raw event** (`transform`): none when filtered out. -/
def kRawToEv (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ : KVState) :
    KRaw → Option (KWEv Obj)
  | .kv v => (kDecObj dec v.value).bind fun o =>
      if sel o then some ⟨0, o, sint.nat v.modRev, false⟩ else none
  | .ev e => kEvOfL dec sel emp σ e
  | .bm r a => some ⟨3, z, r, a⟩

/-- A tail of raw events from the cursor `c` (`KTail` before `transform`). -/
inductive KRawTail (σ : KVState) (inS : GoString → Bool) : Nat → List KRaw → Prop
  | nil (c : Nat) : KRawTail σ inS c []
  | chg (c r : Nat) (rest : List KRaw) : c < r → r ≤ σ.rev → KRawTail σ inS r rest →
      KRawTail σ inS c ((kRangeEvsL σ inS (c + 1) (r + 1)).map KRaw.ev ++ rest)
  | bm (c p : Nat) (rest : List KRaw) : c ≤ p → p ≤ σ.rev → kRangeEvsL σ inS (c + 1) (p + 1) = [] →
      KRawTail σ inS p rest → KRawTail σ inS c (KRaw.bm p false :: rest)

/-- **The raw events queued so far are a prefix of the ideal raw stream** (the producer's
invariant; `kStreamOk`'s shape). -/
def kRawStreamOk (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (raws : List KRaw) : Prop :=
  if m.forceInit then
    ∃ r0 full, max m.req 1 ≤ r0 ∧ r0 ≤ σ.rev ∧ KRawTail σ inS r0 full ∧
      raws <+: ((σ.at r0).kvs.filter fun v => inS v.key).map KRaw.kv ++
        ((if m.bmReq then [KRaw.bm r0 true] else []) ++ full)
  else ∃ s0 full, (0 < m.req → s0 = m.req) ∧ KRawTail σ inS s0 full ∧ raws <+: full

end pure

/-! ## 2. The consumer's view -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- The encoding of a `watch.Event` (for `Pos.Countable`, which the channel's ghost state needs). -/
instance watchEvent_countable : Pos.Countable k8s_io.apimachinery.pkg.watch.Event :=
  .ofInjective (fun e => Pos.Countable.encode (e.Type', e.Object'))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rfl)

/-- `KWEv` is countable when the objects are (the received models' ghost list). -/
instance kwev_countable [Pos.Countable Obj] : Pos.Countable (KWEv Obj) :=
  .ofInjective (fun e => Pos.Countable.encode (e.t, e.o, e.rv, e.ann))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      rfl)

/-- **The watch path's additions to the store's object contract** (proved for the driver's codec in
7f-5a-P; not trusted): the initial-events-end annotation's effect on a body. -/
structure WatchSpec (Obj : Type) where
  annotate : Obj → Obj

/-- **The watch path's object contract** (persistent): `runtime.Decode(codec, data)` (no target,
`decodeObj`) gives a fresh object of the data's body (some resource version string) or an error;
`storage.AnnotateInitialEventsEndBookmark(x)` annotates the body (`W.annotate`) and returns `nil`. -/
def watchContractOk (S : ObjSpec GF Obj) (W : WatchSpec Obj) (codec : GoInterface) : IProp GF :=
  iprop(□ (∀ (dsl : GoSlice) (d : GoString) (Φ : val → IProp GF),
      dsl ↦*□ d -∗
      ▷ (∀ (x err : GoInterface),
          (match S.decode d with
            | some o => ⌜err = GoInterface.nil⌝ ∗ ∃ rv, S.objAt x o rv
            | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err) -∗
          Φ (PairV #x #err)) -∗
      WP (App (App (Val (@! k8s_io.apimachinery.pkg.runtime.Decode)) (Val #codec)) (Val #dsl))
        {{ Φ }}) ∗
    □ (∀ (x : GoInterface) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
      S.objAt x o rv -∗
      ▷ (∀ err : GoInterface, ⌜err = GoInterface.nil⌝ ∗ S.objAt x (W.annotate o) rv -∗ Φ #err) -∗
      WP (App (Val (@! k8s_io.apiserver.pkg.storage.AnnotateInitialEventsEndBookmark)) (Val #x))
        {{ Φ }}))

instance watchContractOk_persistent (S : ObjSpec GF Obj) (W : WatchSpec Obj) (codec : GoInterface) :
    Persistent (watchContractOk S W codec) := by
  unfold watchContractOk; infer_instance

/-- **The default gate has `ConcurrentWatchObjectDecode` off** (persistent; the TEMPORARY premise of
Q6, removed by 7f-5b): `processEvents` takes the serial branch. Producer: the driver's
`Set("ConcurrentWatchObjectDecode=false")` (the table `k8sSetValue` already maps it to `false`). -/
def concurrentDecodeOff : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
    k8sfeature.featureOff g go!"ConcurrentWatchObjectDecode")

instance concurrentDecodeOff_persistent : Persistent (concurrentDecodeOff (GF := GF)) := by
  unfold concurrentDecodeOff; infer_instance

/-- `SendInitialEvents` (a `*bool`) is `sie`: `nil` for none, a read-only cell for some. -/
def sendInitIs (p : Loc) : Option Bool → IProp GF
  | none => iprop(⌜p = null⌝)
  | some b => iprop(p ↦□ b)

instance sendInitIs_persistent (p : Loc) (sie : Option Bool) : Persistent (sendInitIs (GF := GF) p sie) := by
  unfold sendInitIs; split <;> infer_instance

/-- **The store's watcher** (persistent; the store invariant's growth, produced by `New`): the
store's `watcher` field holds a `*watcher` whose fields are the store's (client, codec, versioner,
transformer, group-resource), a `newFunc` making the zero object, `getCurrentStorageRV` calling the
store's `GetCurrentResourceVersion`, `getResourceSizeEstimator` calling the store's (which answers
`nil`: `storeListOk`'s `rseNilR`); the client's watcher over the cluster's KV `γk`; the watch path's
object contract. -/
def storeWatchOk (sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γk : KVNames) : IProp GF :=
  iprop(∃ (wp : Loc) (nf crv rse : GoFunc),
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"watcher" sp ↦□ wp ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"client" wp ↦□ c.cl ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"codec" wp ↦□ c.codec ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"newFunc" wp ↦□ nf ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"groupResource" wp ↦□ c.gr ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"versioner" wp ↦□
      GoInterface.ok c.vi ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"transformer" wp ↦□
      GoInterface.ok c.ti ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"getCurrentStorageRV" wp ↦□ crv ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"getResourceSizeEstimator" wp ↦□
      rse ∗
    newItemOk c.S nf ∗
    □ (∀ (ctx : GoInterface) (Φ : val → IProp GF),
      WP (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
        go!"GetCurrentResourceVersion")) (Val #ctx)) {{ Φ }} -∗
      WP (App (Val #crv) (Val #ctx)) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
      WP (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
        go!"getResourceSizeEstimator")) (Val #())) {{ Φ }} -∗
      WP (App (Val #rse) (Val #())) {{ Φ }}) ∗
    clientWatchOk c.cl γk ∗
    watchContractOk c.S W c.codec)

instance storeWatchOk_persistent (sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γk : KVNames) :
    Persistent (storeWatchOk sp c W γk) := by
  unfold storeWatchOk; infer_instance

/-- The Go string of an event type (`watch.Added`, ...). -/
def kEvTypeStr (t : Nat) : GoString :=
  if t = 0 then go!"ADDED" else if t = 1 then go!"MODIFIED" else if t = 2 then go!"DELETED"
  else if t = 3 then go!"BOOKMARK" else go!"ERROR"

/-- **An Error event's object** (persistent): a `*metav1.Status` whose status is `Failure` (what
`transformErrorToEvent` makes of an `APIStatus`; the driver's `WError`). -/
def statusFailureAt (x : GoInterface) : IProp GF :=
  iprop(∃ (p : Loc) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status),
    ⌜x = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.Status.ty) #p ∧
      st.Status' = go!"Failure"⌝ ∗ p ↦□ st)

/-- **The received `watch.Event` `v` is the event `e`**: an Error event's object a failure status;
any other event's type, and its object owned, holding the body (annotated if `e.ann`) at the
resource version `e.rv`. -/
def wevAt (S : ObjSpec GF Obj) (W : WatchSpec Obj) (v : k8s_io.apimachinery.pkg.watch.Event)
    (e : KWEv Obj) : IProp GF :=
  if e.t = 4 then iprop(⌜v.Type' = go!"ERROR"⌝ ∗ statusFailureAt v.Object')
  else iprop(⌜e.t < 4 ∧ v.Type' = kEvTypeStr e.t⌝ ∗
    S.objAt v.Object' (if e.ann then W.annotate e.o else e.o) (S.fmtRV (W64 (e.rv : Int))))

/-- The ghost names of one store watch. -/
structure KWatchNames where
  /-- `resultChan`'s SPSC (the consumer's view) -/
  res : SpscNames
  /-- the models of the events sent on it, in order (a mono list) -/
  evs : GName
  /-- `incomingEventChan`'s SPSC (internal) -/
  inc : SpscNames
  /-- the raw events queued on it, in order (a mono list; internal) -/
  raws : GName

/-- **The `i`-th element of `resultChan`** (see the file header): the event `v` is `e`, the models
of the first `i + 1` events are `evs ++ [e]` (each at its index of the ghost list `γ.evs`), and they
are `kStreamOk` at a state `σ` the caller's read update fired at. -/
def kResElem [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (i : Int) (v : k8s_io.apimachinery.pkg.watch.Event) :
    IProp GF :=
  iprop(∃ (e : KWEv Obj) (evs : List (KWEv Obj)) (lb : Nat) (σ : KVState),
    wevAt c.S W v e ∗ ⌜evs.length = i.toNat⌝ ∗
    ([∗list] j ↦ e' ∈ evs ++ [e], monoListIdxOwn γ.evs j e') ∗
    □ Q lb σ ∗ ⌜kStreamOk c.S.dec sel emp c.S.zero inS m σ (evs ++ [e])⌝)

/-- **The consumer's view of a store watch** (see the file header): `wi`'s `ResultChan()` returns
the channel `ch` and `Stop()` returns, each callable at any time from anywhere; `ch` is an SPSC
channel of `kResElem` elements, and the caller holds its consumer's half (nothing received yet). -/
def k8sWatch [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec Obj) (wi : GoInterface)
    (γ : KWatchNames) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) : IProp GF :=
  iprop(∃ (wo : GoInterfaceOk) (ch : Loc), ⌜wi = GoInterface.ok wo⌝ ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #ch -∗
      WP (App (Val #(methods wo.ty go!"ResultChan" wo.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #() -∗
      WP (App (Val #(methods wo.ty go!"Stop" wo.v)) (Val #())) {{ Φ }}) ∗
    isSpsc γ.res ch (kResElem c W γ sel emp inS m Q) (fun _ => iprop(True)) ∗
    spscConsumer γ.res ([] : List k8s_io.apimachinery.pkg.watch.Event))

/-- **The caller's read update at every member and at the watch's KV** (persistent): `Q` fires at the
state each linearizable read (`Get`, the client watch's responses) reads. -/
def readAus (c : StoreCfg GF Obj) (γk : KVNames) (Q : KVState → IProp GF) : IProp GF :=
  iprop(kvReadAu γk Q ∗ [∗list] x ∈ c.ms, kvReadAu x.γr.kv Q)

instance readAus_persistent (c : StoreCfg GF Obj) (γk : KVNames) (Q : KVState → IProp GF) :
    Persistent (readAus c γk Q) := by
  unfold readAus; infer_instance

/-- A watch's scope, as `kInScope` of the prepared key (the client watch's range, `WithPrefix` when
recursive). -/
def kScopeOf (c : StoreCfg GF Obj) (k : GoString) (recur : Bool) : GoString → Bool :=
  kInScope (c.pathPrefix ++ k) recur

/-! ## 4. The protocol (internal; the proof's ghost state) -/

/-- **An `*event` holds the raw event `r`** (read-only once queued): its key, value and previous
value slices, revision and flags as `parseKV`/`parseEvent`/`progressNotifyEvent` set them (an etcd
event's previous value: the client's `PrevKv`'s value, which `prevKvOk` ties to `kPrevAt`). -/
def eventAt (p : Loc) (r : KRaw) : IProp GF :=
  iprop(∃ ev : k8s_io.apiserver.pkg.storage.etcd3.event, p ↦□ ev ∗
    match r with
    | .kv v => iprop(⌜ev.key' = v.key ∧ ev.rev' = v.modRev ∧ ev.isCreated' = true ∧
        ev.isDeleted' = false ∧ ev.isProgressNotify' = false ∧ ev.isInitialEvent' = true⌝ ∗
        ev.value' ↦*□ v.value ∗ ⌜ev.prevValue' = slice.nil⌝)
    | .ev e => iprop(⌜ev.key' = e.kv.key ∧ ev.rev' = e.kv.modRev ∧ ev.isDeleted' = e.del ∧
        ev.isCreated' = decide (e.del = false ∧ e.kv.createRev = e.kv.modRev) ∧
        ev.isProgressNotify' = false⌝ ∗ ev.value' ↦*□ e.kv.value ∗
        ∃ pv : GoString, ev.prevValue' ↦*□ pv)
    | .bm r a => iprop(⌜ev.rev' = W64 (r : Int) ∧ ev.isProgressNotify' = true ∧
        ev.isInitialEventsEndBookmark' = a⌝))

/-- **The `i`-th element of `incomingEventChan`** (an SPSC: producer `startWatching`, consumer the
processing goroutine): an `*event` holding the raw event `r`, the first `i + 1` raw events are
`raws ++ [r]` (at their indices of `γ.raws`), and they are `kRawStreamOk` at a state the read update
fired at; an etcd event's previous value is the record `kPrevAt` gives, when there is one. -/
def kInElem (γ : KWatchNames) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) [Pos.Countable KRaw] (i : Int) (p : Loc) : IProp GF :=
  iprop(∃ (r : KRaw) (raws : List KRaw) (lb : Nat) (σ : KVState),
    eventAt p r ∗ ⌜raws.length = i.toNat⌝ ∗
    ([∗list] j ↦ r' ∈ raws ++ [r], monoListIdxOwn γ.raws j r') ∗
    □ Q lb σ ∗ ⌜kRawStreamOk inS m σ (raws ++ [r])⌝)

/-- **`resultChan`'s producers' invariant** (two producers: `sendEvent` from the processing
goroutine, in order, and `sendError` from either goroutine, an Error event): the SPSC's producer
token with the sent events' models, whose non-error part is the transform of the first `k` raw
events the processing goroutine has taken (`procd`, its exclusive half). `run` closes the channel
after both producers have exited (`resultChanWG`), taking the token from here. -/
def kResInv [Pos.Countable Obj] [Pos.Countable KRaw] (c : StoreCfg GF Obj) (γ : KWatchNames)
    (sel : Obj → Bool) (emp : Bool) (procd : GName) : IProp GF :=
  iprop(∃ (sent : List k8s_io.apimachinery.pkg.watch.Event) (evs : List (KWEv Obj))
      (raws : List KRaw) (σ : KVState),
    spscProducer γ.res sent ∗ monoListAuthOwn γ.evs (1 : Qp) evs ∗ ⌜sent.length = evs.length⌝ ∗
    dghostVar procd (DFrac.own (1 : Qp).half) raws.length ∗ monoListLbOwn γ.raws raws ∗
    ⌜kNonErr evs = raws.filterMap (kRawToEv c.S.dec sel emp c.S.zero σ)⌝)

end defs

/-! ## 3. The triple -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- **`(*store).Watch(ctx, key, opts)`** (`store.go:1142-1152`; see `notes/k8s-7f5a-draft.md` §3):
a watch of the prepared key's scope from the parsed resource version `n`, with `WatchList` on,
`EtcdRangeStream` off and (temporarily, Q6) `ConcurrentWatchObjectDecode` off, under the caller's
context (an `isContext` with grpc's outgoing metadata, client errors and the Kubernetes keys), with
three thread tokens (`run`, `startWatching`, `serialProcessEvents`) and the caller's read updates
`Q lb` (`Q lb σ`: a state of one history at revision at least `lb`; `Q σ.rev` handed out after a
firing at `σ`), returns an error, or `nil` and the consumer's view (`k8sWatch`). -/
abbrev store.Watch.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec Obj) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (opts : k8s_io.apiserver.pkg.storage.ListOptions) (k : GoString) (n : w64)
    (sie : Option Bool) (sel : Obj → Bool) (emp : Bool) (Q : Nat → KVState → IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      storeWatchOk sp c W γk ∗
      ⌜prepareKeyM c.resourcePrefix key opts.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV opts.ResourceVersion' = some n ∧
        uint.Z n < 2 ^ 63 ∧ opts.ProgressNotify' = false ∧ opts.RecordTimestamps' = false⌝ ∗
      sendInitIs opts.SendInitialEvents' sie ∗ selPredOk c.S opts.Predicate' sel emp ∗
      watchListOn ∗ rangeStreamOff ∗ concurrentDecodeOff ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗
      k8sctx.k8sCtxOk ci ∗
      threadTok ∗ threadTok ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (|==> readAus c γk (Q 0)) ∗
      (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) }}
    (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"Watch")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #opts))
  {{ (wi err : GoInterface), RET (PairV #wi #err);
      ⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γ : KWatchNames,
        k8sWatch c W wi γ sel emp (kScopeOf c k opts.Recursive')
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q) }}

end spec

end Draft
end k8s
end EtcdGrove
end Perennial
