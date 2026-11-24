/-
Lean-first (no Rocq counterpart).

# The etcd3 store's watch: the ideal stream (k8s 7f-5a-P, pure)

The pure vocabulary of the store watch's spec (`notes/k8s-7f5a-draft.md` §1, §4; moved from the
Draft): a watch event as the consumer sees it (`KWEv`), an etcd event's watch event (`kEvOfL`), a
watch-list's initial events (`kInitialL`), a watch's events from a cursor (`KTail`), the request's
mode (`kModeOf`), the ideal stream (`kIdealL`), the prefix and subsequence relations to it
(`kStreamOk`, `kStreamSub`), the start point (`kStartOk`); the raw events the producer queues
(`KRaw`, `KRawTail`, `kRawIdealL`, `kRawStreamOk`, `kRawStreamSub`) and what the processing
goroutine makes of them (`kRawToEv`).

Laws: the raw stream's relations give the cooked stream's (`kStreamOk_of_raw`, `kStreamSub_of_raw`:
`transform` maps `KRawTail` to `KTail` and the raw ideal stream to the ideal stream).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

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

/-- **The ideal stream from the start point `st`** (at the history `σ`, for the tail `full`): with
initial events, the initial events at `st`, then the annotated bookmark at `st` if asked, then
`full`; without, `full`. -/
def kIdealL (dec : Dec Obj) (sel : Obj → Bool) (inS : GoString → Bool) (z : Obj) (m : KWatchMode)
    (σ : KVState) (st : Nat) (full : List (KWEv Obj)) : List (KWEv Obj) :=
  if m.forceInit then
    kInitialL dec sel inS (σ.at st) ++ ((if m.bmReq then [⟨3, z, st, true⟩] else []) ++ full)
  else full

/-- **The events received, Error events removed wherever they are, stand in the relation `R` to the
ideal stream from the start point `st`** (at the history `σ`; Error events:
`nonissues/k8s-etcd3-watcher-events-after-error.md`): every event's type is at most 4, the start
point of a watch with initial events is a revision of `σ`, and some tail `full` from `st` gives the
ideal stream. `R` is the prefix relation (`kStreamOk`: no gap) or the subsequence relation
(`kStreamSub`: in order, none invented, none repeated, but some may be missing). Where `st` comes
from is `kStartOk`'s. -/
def kStreamRel (R : List (KWEv Obj) → List (KWEv Obj) → Prop) (dec : Dec Obj) (sel : Obj → Bool)
    (emp : Bool) (z : Obj) (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (evs : List (KWEv Obj)) : Prop :=
  (∀ e ∈ evs, e.t ≤ 4) ∧ (m.forceInit = true → st ≤ σ.rev) ∧
  ∃ full, KTail dec sel emp z σ inS st full ∧ R (kNonErr evs) (kIdealL dec sel inS z m σ st full)

/-- **The events received are a prefix of the ideal stream**: none missing, none repeated, in
order (`kStreamRel` with the prefix relation). What the watch guarantees while it is live. -/
def kStreamOk (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (inS : GoString → Bool)
    (m : KWatchMode) (σ : KVState) (st : Nat) (evs : List (KWEv Obj)) : Prop :=
  kStreamRel (· <+: ·) dec sel emp z inS m σ st evs

/-- **The events received are a subsequence of the ideal stream**: in order, none invented, none
repeated, some possibly missing (`kStreamRel` with the subsequence relation). What the watch
guarantees once it is stopped or its context is done (`nonissues/k8s-etcd3-watcher-gap-after-cancel.md`:
`queueEvent` drops an event on the done context and the producer goes on with the next). -/
def kStreamSub (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (inS : GoString → Bool)
    (m : KWatchMode) (σ : KVState) (st : Nat) (evs : List (KWEv Obj)) : Prop :=
  kStreamRel List.Sublist dec sel emp z inS m σ st evs

/-- **The start point `st` of a watch of mode `m`, at the state `σ0` the read update fired at**:
- with initial events, the revision of the first page's linearizable `Get` (`syncPaginated`'s
  `wc.initialRev = getResp.Header.Revision`, which overwrites a requested revision), so
  `st = σ0.rev`, at least the requested revision (`startWatching` checked it against
  `getCurrentStorageRV` before; a caller whose `Q` gives `1 ≤ σ.rev` reads `1 ≤ st` from `σ0`);
- without, the requested revision when positive, else the revision of `getCurrentStorageRV`'s quorum
  `Get` (`getStartWatchResourceVersion`), `st = σ0.rev`.

So a watch from "now" starts at a state the caller's read update fired at during the call, and the
caller's `Q` gives its freshness. -/
def kStartOk (m : KWatchMode) (σ0 : KVState) (st : Nat) : Prop :=
  if m.forceInit then st = σ0.rev ∧ m.req ≤ st
  else if 0 < m.req then st = m.req else st = σ0.rev

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

/-- **`prepareObjs`' current object** of a raw event (decoded, before the resource version is
set): an initial key-value's and a non-delete event's value; none for a delete or a bookmark. -/
def kCurObj (dec : Dec Obj) : KRaw → Option Obj
  | .kv v => kDecObj dec v.value
  | .ev e => if e.del then none else kDecObj dec e.kv.value
  | .bm _ _ => none

/-- **`prepareObjs`' old object** of a raw event, for a predicate empty iff `emp`: the key's record
before a non-create event, decoded when it is a delete or the predicate is not empty; none
otherwise (a create's previous value is `nil`; an initial key-value's and a bookmark's too). -/
def kOldObj (dec : Dec Obj) (emp : Bool) (σ : KVState) : KRaw → Option Obj
  | .ev e => if e.del = false ∧ e.kv.createRev = e.kv.modRev then none
      else if e.del = true ∨ emp = false then (kPrevAt σ e).bind fun p => kDecObj dec p.value
      else none
  | _ => none

/-- **A raw event's values decode** (what `kvWfHist` gives under the store's prefix): the value
`prepareObjs` decodes, and the previous value of a non-create event. -/
def kRawDecOk (dec : Dec Obj) (σ : KVState) : KRaw → Prop
  | .kv v => dec v.value ≠ none
  | .ev e => (e.del = false → dec e.kv.value ≠ none) ∧
      (¬ (e.del = false ∧ e.kv.createRev = e.kv.modRev) →
        ∀ pr, kPrevAt σ e = some pr → dec pr.value ≠ none)
  | .bm _ _ => True

/-- A stored value that decodes: the transformer reads data that the codec decodes, to the object
`kDecObj` gives. -/
theorem kDec_some {C : ObjCodec Obj} {v : GoString} (h : C.dec v ≠ none) :
    ∃ d st o, C.fromS v = some (d, st) ∧ C.decode d = some o ∧ kDecObj C.dec v = some o := by
  unfold ObjCodec.dec at h
  cases hf : C.fromS v with
  | none => rw [hf] at h; exact absurd rfl h
  | some p =>
    rw [hf] at h
    cases hd : C.decode p.1 with
    | none => simp [hd] at h
    | some o =>
      refine ⟨p.1, p.2, o, by simp, hd, ?_⟩
      simp [kDecObj, ObjCodec.dec, hf, hd]

/-- A raw event's revision (the `event`'s `rev`). -/
def kRawRev : KRaw → w64
  | .kv v => v.modRev
  | .ev e => e.kv.modRev
  | .bm r _ => W64 (r : Int)

/-- A tail of raw events from the cursor `c` (`KTail` before `transform`). -/
inductive KRawTail (σ : KVState) (inS : GoString → Bool) : Nat → List KRaw → Prop
  | nil (c : Nat) : KRawTail σ inS c []
  | chg (c r : Nat) (rest : List KRaw) : c < r → r ≤ σ.rev → KRawTail σ inS r rest →
      KRawTail σ inS c ((kRangeEvsL σ inS (c + 1) (r + 1)).map KRaw.ev ++ rest)
  | bm (c p : Nat) (rest : List KRaw) : c ≤ p → p ≤ σ.rev → kRangeEvsL σ inS (c + 1) (p + 1) = [] →
      KRawTail σ inS p rest → KRawTail σ inS c (KRaw.bm p false :: rest)

/-- The ideal raw stream from the start point `st` (`kIdealL` before `transform`). -/
def kRawIdealL (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (full : List KRaw) : List KRaw :=
  if m.forceInit then
    ((σ.at st).kvs.filter fun v => inS v.key).map KRaw.kv ++
      ((if m.bmReq then [KRaw.bm st true] else []) ++ full)
  else full

/-- **The raw events queued stand in the relation `R` to the ideal raw stream** (`kStreamRel`'s
shape before `transform`). -/
def kRawStreamRel (R : List KRaw → List KRaw → Prop) (inS : GoString → Bool) (m : KWatchMode)
    (σ : KVState) (st : Nat) (raws : List KRaw) : Prop :=
  (m.forceInit = true → st ≤ σ.rev) ∧
  ∃ full, KRawTail σ inS st full ∧ R raws (kRawIdealL inS m σ st full)

/-- The raw events queued so far are a prefix of the ideal raw stream (the producer's invariant
while the watch is live). -/
def kRawStreamOk (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (raws : List KRaw) : Prop :=
  kRawStreamRel (· <+: ·) inS m σ st raws

/-- The raw events queued so far are a subsequence of the ideal raw stream (always: a
`queueEvent` that gives up on the done context drops one raw event, and the producer goes on). -/
def kRawStreamSub (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (raws : List KRaw) : Prop :=
  kRawStreamRel List.Sublist inS m σ st raws

end pure


/-! ## From the raw stream to the cooked stream -/

section laws
variable [GooseExts]
variable {Obj : Type}

/-- `transform` never makes an Error event. -/
theorem kRawToEv_t (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ : KVState)
    (r : KRaw) (e : KWEv Obj) (h : kRawToEv dec sel emp z σ r = some e) : e.t ≤ 3 := by
  cases r with
  | bm r a => simp only [kRawToEv, Option.some.injEq] at h; subst h; simp
  | kv v =>
    simp only [kRawToEv, Option.bind_eq_some_iff] at h
    obtain ⟨o, -, h⟩ := h
    split at h
    · cases h; simp
    · cases h
  | ev ev =>
    simp only [kRawToEv, kEvOfL] at h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨o, -, h⟩ := h
      split at h
      · cases h; simp
      · cases h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨o, -, h⟩ := h
      split at h
      · split at h
        · cases h; simp
        · cases h
      · split at h
        · cases h; simp
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨o', -, h⟩ := h
          split at h
          · cases h; simp
          · split at h
            · cases h; simp
            · split at h
              · cases h; simp
              · cases h

/-- **`transform` maps a raw tail to a tail.** -/
theorem kTail_of_raw (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ : KVState)
    (inS : GoString → Bool) (c : Nat) (full : List KRaw) (h : KRawTail σ inS c full) :
    KTail dec sel emp z σ inS c (full.filterMap (kRawToEv dec sel emp z σ)) := by
  induction h with
  | nil c => exact KTail.nil c
  | chg c r rest hcr hr _ ih =>
    rw [List.filterMap_append]
    have : ((kRangeEvsL σ inS (c + 1) (r + 1)).map KRaw.ev).filterMap (kRawToEv dec sel emp z σ) =
        kEventsInL dec sel emp σ inS (c + 1) (r + 1) := by
      rw [List.filterMap_map]; rfl
    rw [this]
    exact KTail.chg c r _ hcr hr ih
  | bm c p rest hcp hp hnone _ ih =>
    simp only [List.filterMap_cons, kRawToEv]
    exact KTail.bm c p _ hcp hp hnone ih

/-- **`transform` maps the raw ideal stream to the ideal stream.** -/
theorem kRawIdealL_filterMap (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj)
    (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat) (full : List KRaw) :
    (kRawIdealL inS m σ st full).filterMap (kRawToEv dec sel emp z σ) =
      kIdealL dec sel inS z m σ st (full.filterMap (kRawToEv dec sel emp z σ)) := by
  unfold kRawIdealL kIdealL
  split
  · rw [List.filterMap_append, List.filterMap_append, List.filterMap_map]
    congr 1
    split <;> simp [kRawToEv]
  · rfl

/-- The cooked events of raw events have no Error event. -/
theorem kNonErr_filterMap (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ : KVState)
    (raws : List KRaw) :
    kNonErr (raws.filterMap (kRawToEv dec sel emp z σ)) = raws.filterMap (kRawToEv dec sel emp z σ) := by
  unfold kNonErr
  rw [List.filter_eq_self]
  intro e he
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.1 he
  have := kRawToEv_t dec sel emp z σ r e hr
  simp only [ne_eq, decide_eq_true_eq]; omega

/-- **The raw events' prefix gives the events' prefix** (`evs` the events sent, whose non-error part
is the raw events' transform). -/
theorem kStreamOk_of_raw (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj)
    (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat) (raws : List KRaw)
    (evs : List (KWEv Obj)) (h : kRawStreamOk inS m σ st raws)
    (he : kNonErr evs = raws.filterMap (kRawToEv dec sel emp z σ)) (ht : ∀ e ∈ evs, e.t ≤ 4) :
    kStreamOk dec sel emp z inS m σ st evs := by
  obtain ⟨hst, full, htail, hpre⟩ := h
  refine ⟨ht, hst, full.filterMap (kRawToEv dec sel emp z σ), kTail_of_raw dec sel emp z σ inS st full htail, ?_⟩
  rw [he, ← kRawIdealL_filterMap]
  exact hpre.filterMap _

/-- **The raw events' subsequence gives the events' subsequence.** -/
theorem kStreamSub_of_raw (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj)
    (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat) (raws : List KRaw)
    (evs : List (KWEv Obj)) (h : kRawStreamSub inS m σ st raws)
    (he : kNonErr evs = raws.filterMap (kRawToEv dec sel emp z σ)) (ht : ∀ e ∈ evs, e.t ≤ 4) :
    kStreamSub dec sel emp z inS m σ st evs := by
  obtain ⟨hst, full, htail, hsub⟩ := h
  refine ⟨ht, hst, full.filterMap (kRawToEv dec sel emp z σ), kTail_of_raw dec sel emp z σ inS st full htail, ?_⟩
  rw [he, ← kRawIdealL_filterMap]
  exact hsub.filterMap _

end laws

/-! ## Along one history, prefixes, segments and the client's range (step 2) -/

section hist
variable [GooseExts]
variable {Obj : Type}

theorem kvSameHist_symm {σ σ' : KVState} (h : kvSameHist σ σ') : kvSameHist σ' σ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') (i : Nat) (hi : i < l.length) :
    l[i]? = l'[i]? := by
  have h1 := List.getElem?_take_of_lt (l := l) (Nat.lt_succ_self i)
  have h2 := List.getElem?_take_of_lt (l := l') (Nat.lt_succ_self i)
  rw [← h1, ← h2, take_of_prefix h (i + 1) (by omega)]

/-- Two states of one history have the same changes at every revision both keep. -/
theorem kvSameHist_changesAt (σ σ' : KVState) (r : Nat) (h : kvSameHist σ σ') (hr : r ≤ σ.rev)
    (hr' : r ≤ σ'.rev) : σ.changesAt r = σ'.changesAt r := by
  obtain ⟨hc, -, hp⟩ := h
  unfold KVState.changesAt
  rw [hc]
  unfold KVState.rev at hr hr'
  split
  · rfl
  · congr 1
    rcases hp with hp | hp
    · exact getElem?_of_prefix hp _ (by omega)
    · exact (getElem?_of_prefix hp _ (by omega)).symm

/-- ... and the same events. -/
theorem kvSameHist_revEvents (σ σ' : KVState) (r : Nat) (h : kvSameHist σ σ') (hr : r ≤ σ.rev)
    (hr' : r ≤ σ'.rev) : σ.revEvents r = σ'.revEvents r := by
  unfold KVState.revEvents
  rw [kvSameHist_at σ σ' (r - 1) h (by omega) (by omega), kvSameHist_changesAt σ σ' r h hr hr']

/-- ... and the same events in a range of revisions both keep. -/
theorem kRangeEvsL_hist (σ σ' : KVState) (inS : GoString → Bool) (lo hi : Nat)
    (h : kvSameHist σ σ') (hh : hi ≤ σ.rev + 1) (hh' : hi ≤ σ'.rev + 1) :
    kRangeEvsL σ inS lo hi = kRangeEvsL σ' inS lo hi := by
  unfold kRangeEvsL
  congr 2
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range'_1] at hm
  exact kvSameHist_revEvents σ σ' m h (by omega) (by omega)

/-- An event of a range of revisions is in scope, of one of them, at its mod revision. -/
theorem kRangeEvsL_mem {σ : KVState} {inS : GoString → Bool} {lo hi : Nat} {ev : mvcc.EvM}
    (h : ev ∈ kRangeEvsL σ inS lo hi) :
    inS ev.kv.key = true ∧ ∃ r, lo ≤ r ∧ r < hi ∧ ev.kv.modRev = W64 (r : Int) := by
  unfold kRangeEvsL at h
  rw [List.mem_filter] at h
  obtain ⟨h, hs⟩ := h
  refine ⟨hs, ?_⟩
  simp only [List.mem_flatten, List.mem_map, List.mem_range'_1] at h
  obtain ⟨l, ⟨r, hr, rfl⟩, hev⟩ := h
  exact ⟨r, hr.1, by omega, mvcc.evsOfRevM_modRev_sm r _ (KVStore.kvs_sorted _) _ ev hev⟩

theorem sint_nat_W64_le (r : Nat) : sint.nat (W64 (r : Int)) ≤ r := by
  have h2 : sint.nat (W64 (r : Int)) = (sint.Z (W64 (r : Int))).toNat := rfl
  rw [h2]
  by_cases hr : r < 2 ^ 63
  · have : sint.Z (W64 (r : Int)) = r := by word
    omega
  · have : sint.Z (W64 (r : Int)) < 2 ^ 63 := by word
    omega

/-- **A raw event's revision is kept by the state** (an etcd event's mod revision at most the
state's revision, so the key's record before it is the same in every longer state of the history). -/
def kRawRevOk (σ : KVState) : KRaw → Prop
  | .ev e => sint.nat e.kv.modRev ≤ σ.rev
  | _ => True

theorem kRawRevOk_mono {σ σ' : KVState} (hle : σ.rev ≤ σ'.rev) {x : KRaw} (h : kRawRevOk σ x) :
    kRawRevOk σ' x := by
  cases x with
  | ev e => simp only [kRawRevOk] at h ⊢; omega
  | _ => trivial

/-- **`transform` reads the same at a longer state of the history.** -/
theorem kRawToEv_hist (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj) (σ σ' : KVState)
    (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) (x : KRaw) (hx : kRawRevOk σ x) :
    kRawToEv dec sel emp z σ x = kRawToEv dec sel emp z σ' x := by
  cases x with
  | ev e =>
    simp only [kRawRevOk] at hx
    simp only [kRawToEv, kEvOfL, kPrevAt]
    rw [kvSameHist_at σ σ' _ h (by omega) (by omega)]
  | kv v => rfl
  | bm r a => rfl

theorem kRawToEv_filterMap_hist (dec : Dec Obj) (sel : Obj → Bool) (emp : Bool) (z : Obj)
    (σ σ' : KVState) (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) (raws : List KRaw)
    (hx : ∀ x ∈ raws, kRawRevOk σ x) :
    raws.filterMap (kRawToEv dec sel emp z σ) = raws.filterMap (kRawToEv dec sel emp z σ') := by
  induction raws with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.filterMap_cons,
      kRawToEv_hist dec sel emp z σ σ' h hle x (hx x List.mem_cons_self),
      ih fun y hy => hx y (List.mem_cons_of_mem _ hy)]

theorem kRawEvs_revOk {σ : KVState} {inS : GoString → Bool} {lo hi : Nat} (hh : hi ≤ σ.rev + 1) :
    ∀ x ∈ (kRangeEvsL σ inS lo hi).map KRaw.ev, kRawRevOk σ x := by
  intro x hx
  obtain ⟨ev, hev, rfl⟩ := List.mem_map.1 hx
  obtain ⟨-, r, -, hr, hm⟩ := kRangeEvsL_mem hev
  simp only [kRawRevOk, hm]
  have := sint_nat_W64_le r
  omega

/-- A raw tail's events are kept by its state. -/
theorem kRawTail_revOk {σ : KVState} {inS : GoString → Bool} {c : Nat} {full : List KRaw}
    (h : KRawTail σ inS c full) : ∀ x ∈ full, kRawRevOk σ x := by
  induction h with
  | nil c => intro x hx; cases hx
  | chg c r rest hcr hr _ ih =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact kRawEvs_revOk (by omega) x hx
    · exact ih x hx
  | bm c p rest _ _ _ _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · trivial
    · exact ih x hx

/-- **A raw tail is one at a longer state of the history.** -/
theorem kRawTail_hist {σ σ' : KVState} (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev)
    {inS : GoString → Bool} {c : Nat} {full : List KRaw} (ht : KRawTail σ inS c full) :
    KRawTail σ' inS c full := by
  induction ht with
  | nil c => exact KRawTail.nil c
  | chg c r rest hcr hr _ ih =>
    rw [kRangeEvsL_hist σ σ' inS (c + 1) (r + 1) h (by omega) (by omega)]
    exact KRawTail.chg c r rest hcr (by omega) ih
  | bm c p rest hcp hp hnone _ ih =>
    rw [kRangeEvsL_hist σ σ' inS (c + 1) (p + 1) h (by omega) (by omega)] at hnone
    exact KRawTail.bm c p rest hcp (by omega) hnone ih

theorem kRawIdealL_hist {σ σ' : KVState} (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev)
    (inS : GoString → Bool) (m : KWatchMode) (st : Nat) (hst : m.forceInit = true → st ≤ σ.rev)
    (full : List KRaw) : kRawIdealL inS m σ st full = kRawIdealL inS m σ' st full := by
  unfold kRawIdealL
  split
  · rename_i hf
    rw [kvSameHist_at σ σ' st h (hst hf) (by have := hst hf; omega)]
  · rfl

theorem kRawIdealL_revOk {σ : KVState} {inS : GoString → Bool} (m : KWatchMode) {st : Nat}
    {full : List KRaw} (ht : KRawTail σ inS st full) :
    ∀ x ∈ kRawIdealL inS m σ st full, kRawRevOk σ x := by
  intro x hx
  unfold kRawIdealL at hx
  split at hx
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx; trivial
    · rcases List.mem_append.1 hx with hx | hx
      · split at hx
        · rcases List.mem_singleton.1 hx with rfl; trivial
        · cases hx
      · exact kRawTail_revOk ht x hx
  · exact kRawTail_revOk ht x hx

/-- **The raw stream's relation holds at a longer state of the history** (any relation). -/
theorem kRawStreamRel_hist {R : List KRaw → List KRaw → Prop} {inS : GoString → Bool}
    {m : KWatchMode} {σ σ' : KVState} (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) {st : Nat}
    {raws : List KRaw} (hr : kRawStreamRel R inS m σ st raws) : kRawStreamRel R inS m σ' st raws := by
  obtain ⟨hst, full, ht, hR⟩ := hr
  refine ⟨fun hf => by have := hst hf; omega, full, kRawTail_hist h hle ht, ?_⟩
  rw [← kRawIdealL_hist h hle inS m st hst full]
  exact hR

/-- The raw events of a subsequence are kept by its state. -/
theorem kRawStreamSub_revOk {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {raws : List KRaw} (h : kRawStreamSub inS m σ st raws) : ∀ x ∈ raws, kRawRevOk σ x := by
  obtain ⟨-, full, ht, hs⟩ := h
  exact fun x hx => kRawIdealL_revOk m ht x (hs.subset hx)

theorem kRawStreamOk_sub {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {raws : List KRaw} (h : kRawStreamOk inS m σ st raws) : kRawStreamSub inS m σ st raws := by
  obtain ⟨hst, full, ht, hp⟩ := h
  exact ⟨hst, full, ht, hp.sublist⟩

/-- **Prefix closure**, for a relation closed under taking a prefix of its left side. -/
theorem kRawStreamRel_prefix {R : List KRaw → List KRaw → Prop}
    (hR : ∀ a b c : List KRaw, R (a ++ b) c → R a c) {inS : GoString → Bool} {m : KWatchMode}
    {σ : KVState} {st : Nat} {raws rs : List KRaw} (h : kRawStreamRel R inS m σ st (raws ++ rs)) :
    kRawStreamRel R inS m σ st raws := by
  obtain ⟨hst, full, ht, hr⟩ := h
  exact ⟨hst, full, ht, hR _ _ _ hr⟩

theorem kRawStreamOk_prefix {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {raws rs : List KRaw} (h : kRawStreamOk inS m σ st (raws ++ rs)) :
    kRawStreamOk inS m σ st raws :=
  kRawStreamRel_prefix (R := (· <+: ·)) (fun a b _ hr => (List.prefix_append a b).trans hr) h

theorem kRawStreamSub_prefix {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {raws rs : List KRaw} (h : kRawStreamSub inS m σ st (raws ++ rs)) :
    kRawStreamSub inS m σ st raws :=
  kRawStreamRel_prefix (R := List.Sublist) (fun a b _ hr => (List.sublist_append_left a b).trans hr) h

/-- A subsequence of a subsequence. -/
theorem kRawStreamSub_sublist {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {raws raws' : List KRaw} (hs : List.Sublist raws raws') (h : kRawStreamSub inS m σ st raws') :
    kRawStreamSub inS m σ st raws := by
  obtain ⟨hst, full, ht, hr⟩ := h
  exact ⟨hst, full, ht, hs.trans hr⟩

/-! ### Segments: the raw events between two cursors -/

/-- **The raw events of a watch between the cursors `c` and `c'`** (`KRawTail`, ending exactly at
`c'`): the producer's queue between two client responses. -/
inductive KRawSeg (σ : KVState) (inS : GoString → Bool) : Nat → Nat → List KRaw → Prop
  | nil (c : Nat) : KRawSeg σ inS c c []
  | chg (c r c' : Nat) (rest : List KRaw) : c < r → r ≤ σ.rev → KRawSeg σ inS r c' rest →
      KRawSeg σ inS c c' ((kRangeEvsL σ inS (c + 1) (r + 1)).map KRaw.ev ++ rest)
  | bm (c p c' : Nat) (rest : List KRaw) : c ≤ p → p ≤ σ.rev →
      kRangeEvsL σ inS (c + 1) (p + 1) = [] → KRawSeg σ inS p c' rest →
      KRawSeg σ inS c c' (KRaw.bm p false :: rest)

theorem kRawSeg_le {σ : KVState} {inS : GoString → Bool} {c c' : Nat} {s : List KRaw}
    (h : KRawSeg σ inS c c' s) : c ≤ c' := by
  induction h with
  | nil => exact Nat.le_refl _
  | chg _ _ _ _ h1 _ _ ih => omega
  | bm _ _ _ _ h1 _ _ _ ih => omega

/-- A segment followed by a tail from its end is a tail. -/
theorem kRawSeg_tail {σ : KVState} {inS : GoString → Bool} {c c' : Nat} {s t : List KRaw}
    (h : KRawSeg σ inS c c' s) (ht : KRawTail σ inS c' t) : KRawTail σ inS c (s ++ t) := by
  induction h with
  | nil => exact ht
  | chg c r c' rest hcr hr _ ih => rw [List.append_assoc]; exact KRawTail.chg c r _ hcr hr (ih ht)
  | bm c p c' rest hcp hp hn _ ih => exact KRawTail.bm c p _ hcp hp hn (ih ht)

theorem kRawSeg_append {σ : KVState} {inS : GoString → Bool} {c m c' : Nat} {s t : List KRaw}
    (h : KRawSeg σ inS c m s) (ht : KRawSeg σ inS m c' t) : KRawSeg σ inS c c' (s ++ t) := by
  induction h with
  | nil => exact ht
  | chg c r m rest hcr hr _ ih => rw [List.append_assoc]; exact KRawSeg.chg c r c' _ hcr hr (ih ht)
  | bm c p m rest hcp hp hn _ ih => exact KRawSeg.bm c p c' _ hcp hp hn (ih ht)

/-- A response's events, the whole revisions `(c, r]`. -/
theorem kRawSeg_chg1 {σ : KVState} {inS : GoString → Bool} {c r : Nat} (hcr : c < r)
    (hr : r ≤ σ.rev) : KRawSeg σ inS c r ((kRangeEvsL σ inS (c + 1) (r + 1)).map KRaw.ev) := by
  have := KRawSeg.chg c r r [] hcr hr (KRawSeg.nil (σ := σ) (inS := inS) r)
  rwa [List.append_nil] at this

/-- A progress notification at `p`. -/
theorem kRawSeg_bm1 {σ : KVState} {inS : GoString → Bool} {c p : Nat} (hcp : c ≤ p)
    (hp : p ≤ σ.rev) (hn : kRangeEvsL σ inS (c + 1) (p + 1) = []) :
    KRawSeg σ inS c p [KRaw.bm p false] :=
  KRawSeg.bm c p p [] hcp hp hn (KRawSeg.nil p)

theorem kRawSeg_hist {σ σ' : KVState} (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev)
    {inS : GoString → Bool} {c c' : Nat} {s : List KRaw} (hs : KRawSeg σ inS c c' s) :
    KRawSeg σ' inS c c' s := by
  induction hs with
  | nil c => exact KRawSeg.nil c
  | chg c r c' rest hcr hr _ ih =>
    rw [kRangeEvsL_hist σ σ' inS (c + 1) (r + 1) h (by omega) (by omega)]
    exact KRawSeg.chg c r c' rest hcr (by omega) ih
  | bm c p c' rest hcp hp hnone _ ih =>
    rw [kRangeEvsL_hist σ σ' inS (c + 1) (p + 1) h (by omega) (by omega)] at hnone
    exact KRawSeg.bm c p c' rest hcp (by omega) hnone ih

/-! ### The client watch's range is the scope -/

/-- **The client watch's range is the watch's scope**: `WithPrefix` of a non-empty prepared key
(`GetPrefixRangeEnd`) for a recursive watch, the key alone otherwise. -/
theorem inRange_scope (kp : GoString) (recur : Bool) (hp : recur = true → kp ≠ []) (k : GoString) :
    EtcdGrove.inRange kp (if recur then prefixRangeEnd kp else []) k =
      kInScope kp recur k := by
  cases recur
  · simp [EtcdGrove.inRange, kInScope]
  · simp only [ite_true, kInScope]
    have := concurrency.inRange_prefix kp k (hp rfl)
    cases hb : EtcdGrove.inRange kp (prefixRangeEnd kp) k
    · rw [hb] at this; simp only [Bool.false_eq_true, false_iff] at this; simp [this]
    · rw [hb] at this; simp only [true_iff] at this; simp [this]

/-- The client watch's events of a range of revisions are the scope's. -/
theorem rangeEvents_scope (σ : KVState) (o : OpFull) (inS : GoString → Bool)
    (h : ∀ k, EtcdGrove.inRange o.key o.base.rangeEnd k = inS k) (lo hi : Nat) :
    σ.rangeEvents o lo hi = kRangeEvsL σ inS lo hi := by
  unfold KVState.rangeEvents kRangeEvsL
  apply List.filter_congr
  intro ev _
  exact h _

end hist

/-! ## The consumer's view and the protocol's ghost state (moved from the Draft) -/

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

/-- `KRaw` is countable (the producer's raw-event ghost list `γ.raws`), through
`EtcdKv ⊕ (mvcc.EvM ⊕ (Nat × Bool))`. -/
instance kraw_countable : Pos.Countable KRaw :=
  .ofInjective
    (fun r => Pos.Countable.encode (match r with
      | .kv v => (Sum.inl v : EtcdKv ⊕ (mvcc.EvM ⊕ (Nat × Bool)))
      | .ev e => Sum.inr (Sum.inl e)
      | .bm r a => Sum.inr (Sum.inr (r, a))))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a <;> cases b <;> simp_all)

/-- **The watch path's additions to the store's object contract** (proved for the driver's codec in
7f-5a-P; not trusted): an object annotated as the initial-events-end bookmark (`annAt x o rv`: `x`
holds the body `o`, annotated, at the resource version string `rv`). An ownership predicate, not a
function on bodies: a body type need not record the annotation (the driver's `DObj` does not; its
Go object's `Annotated` field does; ledger 2026-11-16, "the watch's annotated object is not
expressible for the driver"). -/
structure WatchSpec (GF : BundledGFunctors) (Obj : Type) where
  annAt : GoInterface → Obj → GoString → IProp GF

/-- **The watch path's object contract** (persistent): `runtime.Decode(codec, data)` (no target,
`decodeObj`) gives a fresh object of the data's body (some resource version string) or an error;
`storage.AnnotateInitialEventsEndBookmark(x)` annotates the object (`W.annAt`) and returns `nil`. -/
def watchContractOk (S : ObjSpec GF Obj) (W : WatchSpec GF Obj) (codec : GoInterface) : IProp GF :=
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
      ▷ (∀ err : GoInterface, ⌜err = GoInterface.nil⌝ ∗ W.annAt x o rv -∗ Φ #err) -∗
      WP (App (Val (@! k8s_io.apiserver.pkg.storage.AnnotateInitialEventsEndBookmark)) (Val #x))
        {{ Φ }}))

instance watchContractOk_persistent (S : ObjSpec GF Obj) (W : WatchSpec GF Obj) (codec : GoInterface) :
    Persistent (watchContractOk S W codec) := by
  unfold watchContractOk; infer_instance

/-- `SendInitialEvents` (a `*bool`) is `sie`: `nil` for none, a read-only cell for some. -/
def sendInitIs (p : Loc) : Option Bool → IProp GF
  | none => iprop(⌜p = null⌝)
  | some b => iprop(p ↦□ b)

instance sendInitIs_persistent (p : Loc) (sie : Option Bool) : Persistent (sendInitIs (GF := GF) p sie) := by
  unfold sendInitIs; split <;> infer_instance

/-- **The store's watcher** (persistent; the store invariant's growth, produced by `New`): the
store's `watcher` field holds a `*watcher` whose fields are the store's (client, codec, versioner,
transformer, group-resource), a `newFunc` making the zero object, `getCurrentStorageRV` calling the
store's `GetCurrentResourceVersion` (whose result is a pair), `getResourceSizeEstimator` calling the store's (which answers
`nil`: `storeListOk`'s `rseNilR`); the client's watcher over the cluster's KV `γk`; the watch path's
object contract; the object type's name (`objectType`, the block loggers'; `createWatchChan`). -/
def storeWatchOk (sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γk : KVNames) : IProp GF :=
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
        go!"GetCurrentResourceVersion")) (Val #ctx))
        {{ v, ∃ (n : w64) (err : GoInterface), ⌜v = PairV #n #err⌝ ∗ Φ v }} -∗
      WP (App (Val #crv) (Val #ctx)) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
      WP (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
        go!"getResourceSizeEstimator")) (Val #())) {{ Φ }} -∗
      WP (App (Val #rse) (Val #())) {{ Φ }}) ∗
    clientWatchOk c.cl γk ∗
    watchContractOk c.S W c.codec ∗
    ∃ ot : GoString, structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"objectType" wp ↦□ ot)

instance storeWatchOk_persistent (sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γk : KVNames) :
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

/-- **An optional object** (`prepareObjs`' results): `nil` for none, else the object at the
resource version `rev`. -/
def kObjOpt (S : ObjSpec GF Obj) (x : GoInterface) (oo : Option Obj) (rev : w64) : IProp GF :=
  match oo with
  | none => iprop(⌜x = GoInterface.nil⌝)
  | some o => S.objAt x o (S.fmtRV rev)

/-- **The received `watch.Event` `v` is the event `e`**: an Error event's object a failure status;
any other event's type, and its object owned, holding the body (annotated if `e.ann`) at the
resource version `e.rv`. -/
def wevAt (S : ObjSpec GF Obj) (W : WatchSpec GF Obj) (v : k8s_io.apimachinery.pkg.watch.Event)
    (e : KWEv Obj) : IProp GF :=
  if e.t = 4 then iprop(⌜v.Type' = go!"ERROR"⌝ ∗ statusFailureAt v.Object')
  else iprop(⌜e.t < 4 ∧ v.Type' = kEvTypeStr e.t⌝ ∗
    if e.ann then W.annAt v.Object' e.o (S.fmtRV (W64 (e.rv : Int)))
    else S.objAt v.Object' e.o (S.fmtRV (W64 (e.rv : Int))))

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
  /-- whether the consumer stopped the watch (`kLive`, `kStopped`) -/
  stop : GName
  /-- whether the producer has exited (`startWatching` closed `watchClosedCh`; internal) -/
  prodEx : GName
  /-- whether the processing goroutine has exited (set before its `sendError`; internal) -/
  procEx : GName
  /-- the Done name of `wc.ctx` (`WithCancel`'s child; `kCdw`; internal) -/
  wcDone : context.ContextNames

/-- **The consumer has not stopped the watch** (exclusive; `k8sWatch` gives it): `Stop` takes it
(or `kStopped`). Excludes `kStopped` (`dghostVar`'s full fraction against a discarded one). -/
def kLive (γ : KWatchNames) : IProp GF := dghostVar γ.stop (DFrac.own 1) false

/-- **The consumer has stopped the watch** (persistent; `Stop`'s post). -/
def kStopped (γ : KWatchNames) : IProp GF := dghostVar γ.stop DFrac.discard true

instance kStopped_persistent (γ : KWatchNames) : Persistent (kStopped (GF := GF) γ) := by
  unfold kStopped; infer_instance

/-- **The watch is no longer live** (persistent): the consumer stopped it, or the caller's context
(`cd`) is done (`□ cd.PDone`: what Perennial's context model gives of a done context, by its Done
channel or a non-`nil` `Err()`). A consumer refutes the first with its `kLive`, and the second when
its context's `PDone` is something it can refute (`WithCancel(Background())` with its own
`PDone'`; for `WithTimeout`'s `PDone := True` it cannot: a watch past its deadline gets only the
subsequence). -/
def kCancelled (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(kStopped γ ∨ □ cd.PDone)

instance kCancelled_persistent (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) :
    Persistent (kCancelled (GF := GF) γ cd) := by
  unfold kCancelled; infer_instance

/-- **The `i`-th element of `resultChan`** (see the file header): the event `v` is `e`, and the
models of the first `i + 1` events are `evs ++ [e]` (each at its index of the ghost list `γ.evs`).
Unless they are all Error events, they come from the ideal stream from a start point `st` that
`kStartOk` ties to a state `σ0` the caller's read update fired at, read at a later state `σ` it
fired at: always a subsequence (`kStreamSub`), and a prefix (`kStreamOk`) unless the watch is no
longer live (`kCancelled`). A consumer that holds `kLive` (has not called `Stop`) and can refute
`□ cd.PDone` reads the prefix. -/
def kResElem [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (i : Int)
    (v : k8s_io.apimachinery.pkg.watch.Event) : IProp GF :=
  iprop(∃ (e : KWEv Obj) (evs : List (KWEv Obj)),
    wevAt c.S W v e ∗ ⌜evs.length = i.toNat⌝ ∗
    ([∗list] j ↦ e' ∈ evs ++ [e], monoListIdxOwn γ.evs j e') ∗
    (⌜kNonErr (evs ++ [e]) = []⌝ ∨
      ∃ (lb lb0 st : Nat) (σ σ0 : KVState), □ Q lb σ ∗ □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st⌝ ∗
        ⌜kStreamSub c.S.dec sel emp c.S.zero inS m σ st (evs ++ [e])⌝ ∗
        (⌜kStreamOk c.S.dec sel emp c.S.zero inS m σ st (evs ++ [e])⌝ ∨ kCancelled γ cd)))

/-- **The consumer's view of a store watch** (see the file header): `wi`'s `ResultChan()` returns
the channel `ch`, callable at any time from anywhere; `Stop()` returns, given `kLive` (the first
call) or `kStopped` (a later one), and gives `kStopped`; `ch` is an SPSC channel of `kResElem`
elements, and the caller holds its consumer's half (nothing received yet) and `kLive`. The
channel's closing carries nothing: the watch's goroutines get their thread tokens at their `go`
statements and give them back when they exit (`wp_fork_tok`, `wp_ThreadExit`). -/
def k8sWatch [Pos.Countable Obj] (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (wi : GoInterface)
    (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool)
    (inS : GoString → Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF) : IProp GF :=
  iprop(∃ (wo : GoInterfaceOk) (ch : Loc), ⌜wi = GoInterface.ok wo⌝ ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #ch -∗
      WP (App (Val #(methods wo.ty go!"ResultChan" wo.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, (kLive γ ∨ kStopped γ) -∗ ▷ (kStopped γ -∗ Φ #()) -∗
      WP (App (Val #(methods wo.ty go!"Stop" wo.v)) (Val #())) {{ Φ }}) ∗
    isSpsc γ.res ch (kResElem c W γ cd sel emp inS m Q) (fun _ => iprop(True)) ∗
    spscConsumer γ.res ([] : List k8s_io.apimachinery.pkg.watch.Event) ∗ kLive γ)

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

/-- **The `event` value `ev` is the raw event `r`**, at the history `σ`: its key,
value and previous value slices, revision and flags as `parseKV`/`parseEvent`/`progressNotifyEvent`
set them. An etcd event's previous value: `nil` for a create (the server sends no `PrevKv` for one);
for any other event (it passed `parseEvent`, so its `PrevKv` is not `nil`), the value of the key's
record at the revision before, `kPrevAt σ e` (the client's `prevKvOk`). -/
def kEvIs (σ : KVState) (ev : k8s_io.apiserver.pkg.storage.etcd3.event) (r : KRaw) : IProp GF :=
  match r with
    | .kv v => iprop(⌜ev.key' = v.key ∧ ev.rev' = v.modRev ∧ ev.isCreated' = true ∧
        ev.isDeleted' = false ∧ ev.isProgressNotify' = false ∧ ev.isInitialEvent' = true⌝ ∗
        ev.value' ↦*□ v.value ∗ ⌜ev.prevValue' = slice.nil⌝)
    | .ev e => iprop(⌜ev.key' = e.kv.key ∧ ev.rev' = e.kv.modRev ∧ ev.isDeleted' = e.del ∧
        ev.isCreated' = decide (e.del = false ∧ e.kv.createRev = e.kv.modRev) ∧
        ev.isProgressNotify' = false⌝ ∗ ev.value' ↦*□ e.kv.value ∗
        (if e.del = false ∧ e.kv.createRev = e.kv.modRev then iprop(⌜ev.prevValue' = slice.nil⌝)
         else iprop(∃ pr : KVRec, ⌜kPrevAt σ e = some pr⌝ ∗ ev.prevValue' ↦*□ pr.value)))
    | .bm r a => iprop(⌜ev.rev' = W64 (r : Int) ∧ ev.isProgressNotify' = true ∧
        ev.isInitialEventsEndBookmark' = a⌝)

instance kEvIs_persistent (σ : KVState) (ev : k8s_io.apiserver.pkg.storage.etcd3.event) (r : KRaw) :
    Persistent (kEvIs (GF := GF) σ ev r) := by
  unfold kEvIs; split
  · infer_instance
  · rename_i e; by_cases h : e.del = false ∧ e.kv.createRev = e.kv.modRev <;> simp only [h] <;>
      infer_instance
  · infer_instance

/-- **An error `fmt.Errorf` made** (persistent): its `Error()` method returns (`fmt.stringMethodSpec`),
it has no `Format` method, and it is a pointer error (what `fmt.Errorf.spec` gives; the watcher's
errors of its own, `parseEvent`'s and `syncPaginated`'s, are these). -/
def kFmtErr (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ fmt.stringMethodSpec e go!"Error" ∗
    ⌜methodSet e.ty !! go!"Format" = none ∧
      methodSet e.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])⌝ ∗
    ⌜_root_.Perennial.errors.IsPointerError e⌝)

instance kFmtErr_persistent (err : GoInterface) : Persistent (kFmtErr (GF := GF) err) := by
  unfold kFmtErr; infer_instance

/-- **An `*event` holds the raw event `r`**, read-only once queued (`kEvIs`). -/
def eventAt (σ : KVState) (p : Loc) (r : KRaw) : IProp GF :=
  iprop(∃ ev : k8s_io.apiserver.pkg.storage.etcd3.event, p ↦□ ev ∗ kEvIs σ ev r)

/-- **The producer has exited** (persistent): `startWatching` set it before closing
`watchClosedCh`, after its last `queueEvent`. -/
def kProdExited (γ : KWatchNames) : IProp GF := dghostVar γ.prodEx DFrac.discard true

instance kProdExited_persistent (γ : KWatchNames) : Persistent (kProdExited (GF := GF) γ) := by
  unfold kProdExited; infer_instance

/-- **The processing goroutine has exited** (persistent): `serialProcessEvents` sets it before its
`sendError` (a `transform` error; `sendError`'s deferred `wc.cancel()` follows, and the goroutine
returns), the only place it cancels. -/
def kProcExited (γ : KWatchNames) : IProp GF := dghostVar γ.procEx DFrac.discard true

instance kProcExited_persistent (γ : KWatchNames) : Persistent (kProcExited (GF := GF) γ) := by
  unfold kProcExited; infer_instance

/-- **The Done proposition of `wc.cancel`** (`WithCancel`'s `PDone'`, persistent): one for each
call of `wc.cancel()`: the consumer stopped the watch (`Stop`), or the producer has exited (`run`'s
cancel after `watchClosedCh`; the producer's own `sendError` cancels too, so it sets `kProdExited`
before it), or the processing goroutine has exited (its `sendError`, `watcher.go:559-562, 796`), or
the caller's context is done (`run`'s cancel after `wc.ctx.Done()` when the parent's closing is what
closed it). An observer of `wc.ctx`'s closed Done channel gets `□ (cd.PDone ∨ kCancelPD γ cd)`; the
producer (still running, so not `kProdExited`) turns it at a dropped event into `kCancelled γ cd ∨
kProcExited γ`, which `kInElem` carries. That needs `WithCancel` over an `isContext` parent to keep
the parent's `PDone`, a Perennial change proposed on its own (`notes/perennial-changes.md`, option
(a)); until then 7f-5a-P's steps 4-5 take `isContext wc.ctx { cd with PDone := cd.PDone ∨
kCancelPD γ cd }` as a premise. -/
def kCancelPD (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(kStopped γ ∨ kProdExited γ ∨ kProcExited γ ∨ □ cd.PDone)

/-- **The `i`-th element of `incomingEventChan`** (an SPSC: producer `startWatching`, consumer the
processing goroutine): an `*event` holding the raw event `r` at the fired state `σ` (with its
previous value), the first `i + 1` raw events are `raws ++ [r]` (at their indices of `γ.raws`),
from the start point `st` (`kStartOk` at a fired `σ0`): a subsequence of the ideal raw stream, and a
prefix of it unless the watch is no longer live or the processing goroutine has exited (which the
processing goroutine refutes at each receipt: it has not). -/
def kInElem (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (i : Int) (p : Loc) :
    IProp GF :=
  iprop(∃ (r : KRaw) (raws : List KRaw) (lb lb0 st : Nat) (σ σ0 : KVState),
    eventAt σ p r ∗ ⌜raws.length = i.toNat⌝ ∗
    ([∗list] j ↦ r' ∈ raws ++ [r], monoListIdxOwn γ.raws j r') ∗
    □ Q lb σ ∗ □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st⌝ ∗ ⌜kRawStreamSub inS m σ st (raws ++ [r])⌝ ∗
    (⌜kRawStreamOk inS m σ st (raws ++ [r])⌝ ∨ kCancelled γ cd ∨ kProcExited γ))

/-- **`resultChan`'s producers' invariant** (two producers: `sendEvent` from the processing
goroutine, in order, and `sendError` from either goroutine, an Error event): the SPSC's producer
token with the sent events' models, whose non-error part is the transform of the raw events
`raws` the processing goroutine has taken and sent (or filtered out; `procd`, its exclusive half:
a `sendEvent` that gives up on the done context makes the goroutine return, and that raw event is
not counted). The facts of `raws` are kept here (unless empty), so that a `sendError` from the
producer can state the element's: `kRawStreamSub`, and `kRawStreamOk` unless the watch is no longer
live. `run` closes the channel after both producers have exited (`resultChanWG`), taking the token
from here. -/
def kResInv [Pos.Countable Obj] (c : StoreCfg GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd : GName) : IProp GF :=
  iprop(∃ (sent : List k8s_io.apimachinery.pkg.watch.Event) (evs : List (KWEv Obj))
      (raws : List KRaw) (σ : KVState),
    spscProducer γ.res sent ∗ monoListAuthOwn γ.evs (1 : Qp) evs ∗ ⌜sent.length = evs.length⌝ ∗
    dghostVar procd (DFrac.own (1 : Qp).half) raws.length ∗ monoListLbOwn γ.raws raws ∗
    ⌜kNonErr evs = raws.filterMap (kRawToEv c.S.dec sel emp c.S.zero σ)⌝ ∗
    (⌜raws = []⌝ ∨
      ∃ (lb lb0 st : Nat) (σ0 : KVState), □ Q lb σ ∗ □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st⌝ ∗
        ⌜kRawStreamSub inS m σ st raws⌝ ∗ (⌜kRawStreamOk inS m σ st raws⌝ ∨ kCancelled γ cd)))

/-! ## The block loggers (`block_logger.go`) -/

/-- **A clock whose `Now()` returns** (persistent; `clock.RealClock`'s, `RealClock.Now.spec`). -/
def clockNowOk (ck : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ t : time.Time, Φ #t) -∗
    WP (App (Val #(methods ck.ty go!"Now" ck.v)) (Val #())) {{ Φ }})

instance clockNowOk_persistent (ck : GoInterfaceOk) : Persistent (clockNowOk (GF := GF) ck) := by
  unfold clockNowOk; infer_instance

/-- The fields of a `*blockLogger` its mutex protects. -/
def blockLoggerInv (l : Loc) : IProp GF :=
  iprop(∃ (lt : time.Time) (ec : w64) (tw : time.Duration),
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"lastLogTime" l ↦ lt ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"eventCount" l ↦ ec ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"timeWaiting" l ↦ tw)

/-- **A block logger** (persistent; `newBlockLogger`'s result): its configuration read-only, a clock
whose `Now()` returns, and its mutex guarding the counters (`blockLoggerInv`). -/
def blockLoggerOk (l : Loc) : IProp GF :=
  iprop(□ ∃ (iv th : w64) (msg ot : GoString)
      (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ck : GoInterfaceOk),
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"interval" l ↦□ iv ∗
    ⌜(msg.length : Int) ≤ maxAddr⌝ ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"threshold" l ↦□ th ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"msg" l ↦□ msg ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"objectType" l ↦□ ot ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"groupResource" l ↦□ gr ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"clock" l ↦□
      GoInterface.ok ck ∗ clockNowOk ck ∗
    sync.isMutex (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.blockLogger go!"mu" l)
      (blockLoggerInv l))

instance blockLoggerOk_persistent (l : Loc) : Persistent (blockLoggerOk (GF := GF) l) := by
  unfold blockLoggerOk; infer_instance

end defs

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An error the watcher's error paths accept** (persistent; internal, decided by etcd-grove-81,
2026-11-15): a non-`nil` error whose calls on the watcher's error paths (`isCancelError`,
`interpretWatchError`, `transformErrorToEvent`, `logWatchChannelErr`) behave: the dynamic-type checks
and the methods they find. Stated over the error's own dynamic type and methods; its producers
(`startWatching`, `syncPaginated`, `transform`; step 5) prove it of each error they hand over
(`notes/k8s-7f5a-draft.md` §11 lists the texts that may need, E1-E6). Each conjunct:
- its comparisons with `context.Canceled` (a `*errors.errorString`) and `rpctypes.ErrCompacted` (an
  `EtcdError`) return: of either dynamic type, its value is one of that type (`go_eq_interface`
  compares at the dynamic type, which has a step for a pointer and for `EtcdError`'s struct only on
  values of that shape; 7f-5a-P step 5: it was a comparison with any value, which no pointer
  error meets);
- `Error()` returns, and there is no `Format` method (`fmt.argOk`: the `Error()` call and klog's
  `%v`);
- an `etcdError` (`Code()`, `Error()`): its `Code()` returns;
- a `grpcError` (`GRPCStatus()`): `GRPCStatus()` returns some status `s`, and `s.Code()` returns;
- `errors.As(err, &(*corruptObjectDeletedError)(nil))` returns `false`, the target unchanged (no
  corrupt-object error reaches the watcher's error paths: its decode never fails under `kvWfHist`);
- an `APIStatus`: its `Status()` returns a status whose `Status` is `Failure` (`statusFailureAt`). -/
def kErrOk (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ □ (
    ⌜(e.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty → ∃ x : Loc, e.v = #x) ∧
      (e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
        ∃ y : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, e.v = #y)⌝ ∗
    fmt.stringMethodSpec e go!"Error" ∗ ⌜methodSet e.ty !! go!"Format" = none ∧
      methodSet e.ty !! go!"Error" = some noArgStringSig⌝ ∗
    (⌜go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.etcdError.ty = true⌝ -∗
      ∀ Φ : val → IProp GF, ▷ (∀ c : google_golang_org.grpc.codes.Code, Φ #c) -∗
        WP (App (Val #(methods e.ty go!"Code" e.v)) (Val #())) {{ Φ }}) ∗
    (⌜go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.grpcError.ty = true⌝ -∗
      ∃ s : Loc,
        (∀ Φ : val → IProp GF, ▷ Φ #s -∗
          WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }}) ∗
        (∀ Φ : val → IProp GF, ▷ (∀ c : google_golang_org.grpc.codes.Code, Φ #c) -∗
          WP (App (Val #(methods (go.GoType.PointerType google_golang_org.grpc.status.Status.ty)
            go!"Code" #s)) (Val #())) {{ Φ }})) ∗
    (∀ (l v : Loc) (Φ : val → IProp GF), l ↦ v -∗ ▷ (l ↦ v -∗ Φ #false) -∗
      WP (App (App (Val (@! _root_.Perennial.errors.As)) (Val #err))
        (Val #(interface.mkOk (go.GoType.PointerType (go.GoType.PointerType
          k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty)) #l))) {{ Φ }}) ∗
    (⌜go.typeSetContains e.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = true⌝ -∗
      ∀ Φ : val → IProp GF,
        ▷ (∀ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, ⌜st.Status' = go!"Failure"⌝ -∗
          Φ #st) -∗
        WP (App (Val #(methods e.ty go!"Status" e.v)) (Val #())) {{ Φ }})))

instance kErrOk_persistent (err : GoInterface) : Persistent (kErrOk (GF := GF) err) := by
  unfold kErrOk; infer_instance

/-- `kErrOk`'s comparison with `context.Canceled`'s `*errors.errorString` where `go_eq_interface`
leaves it: the dynamic types equal, two pointers, or `false`. -/
theorem wp_kErrOk_eq_ptr (e : GoInterfaceOk) (l : Loc) (Φ : val → IProp GF)
    (h : e.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty → ∃ x : Loc, e.v = #x) :
    ⊢ (∀ b : Bool, Φ #b) -∗
      WP (if e.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty then
        gl(CheckComparable e.ty ;; GoOp GoEquals e.ty glv((e.v, #l))) else Val #false) {{ Φ }} := by
  iintro HΦ
  obtain ⟨t, v⟩ := e
  split
  · rename_i ht
    simp only [] at ht h
    subst ht
    obtain ⟨x, rfl⟩ := h rfl
    wp_auto
    iapply HΦ
  · (try wp_auto)
    iapply HΦ

/-- `kErrOk`'s comparison with `rpctypes.ErrCompacted`'s `EtcdError` where `go_eq_interface` leaves
it: the dynamic types equal, two `EtcdError` structs, or `false`. -/
theorem wp_kErrOk_eq_etcd [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] (e : GoInterfaceOk) (y : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError)
    (Φ : val → IProp GF)
    (h : e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
      ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, e.v = #x) :
    ⊢ (∀ b : Bool, Φ #b) -∗
      WP (if e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty then
        gl(CheckComparable e.ty ;; GoOp GoEquals e.ty glv((e.v, #y))) else Val #false) {{ Φ }} := by
  iintro HΦ
  obtain ⟨t, v⟩ := e
  split
  · rename_i ht
    simp only [] at ht h
    subst ht
    obtain ⟨x, rfl⟩ := h rfl
    dsimp only
    wp_auto
    by_cases hc : x.code' = y.code' <;> simp only [hc, decide_true, decide_false] <;> wp_auto <;>
      iapply HΦ
  · (try wp_auto)
    iapply HΦ

end errs

end k8s
end EtcdGrove
end Perennial
