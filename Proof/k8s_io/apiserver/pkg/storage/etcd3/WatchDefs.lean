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

end k8s
end EtcdGrove
end Perennial
