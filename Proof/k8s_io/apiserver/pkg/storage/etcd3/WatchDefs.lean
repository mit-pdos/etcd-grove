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

end k8s
end EtcdGrove
end Perennial
