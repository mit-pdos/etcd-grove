/-
etcd's cache `store` (`cache/store.go`, `cache/snapshot.go`): the shared vocabulary of
`Spec/newStore.lean`, `Spec/store__*.lean`, `Spec/snapshot__Range.lean` and the helpers'
specs. Lean-first (no Rocq counterpart).

**Keys and maps.** A key-value map is a list of entries `(key, kv)`, the key a Go string
and `kv` a `*mvccpb.KeyValue` (`KvMap`), strictly sorted by key (`kvLess`: Go's `<` on
strings, bytewise lexicographic, `go.GoStringLt`). It is exactly the item list of the
store's btrees of `*kvItem` (`InvBtree.lean`): `kvItemIs p (k, l)` says `p` points (for
good) to `kvItem{key: k, kv: l}`, and the btree's `less` is `kvLess`. The `KeyValue`s
themselves are read-only: `kvAt (k, l)` says `l` points for good to a `KeyValue` whose
`Key` bytes are `k`, and `kvsAt m` says so of every entry of `m`.

**The state.** `StoreState`: the latest revision, the latest map and the history of
snapshots `(rev, map)`, oldest first; `StoreInv` is what the code maintains. The
physical history is the `history` ring buffer of `*snapshot`s (`InvRingBuffer.lean`),
item `p` modelling `(rev, m)` when `p` points for good to `snapshot{rev, tree}` and `tree`
is a read-only (`DFrac.discard`) btree holding `m` (`snapIs`).

**Concurrency.** `mu` is a `sync.RWMutex`, specified with Perennial's guarded spec
(`sync.ownRWMutex rw P`, `P` fractional: `RLock` gives `P rfrac`, `Lock` gives `P 1`).
`storeLockInv s γ cap q` is `P q`: a `q`-fraction of the fields readers read (`latest.rev`,
the history ring), of a monotone counter on `latest.rev` (`γ.rev`), of a ghost variable holding
the abstract state (`γ.state`), of a monotone counter on the newest snapshot (`γ.snap`,
`storeSnapKey`) and of the latest tree's lending flag (`γ.tree`); that the newest snapshot is the
latest map (`Synced`); and `□ R` of the latest revision. **The store has any number of writers**
(the cache's watch loop restores it, and every iteration's `applyStorage` goroutine applies its
watcher's responses, possibly after its iteration ended): a writer needs only the persistent
`isStoreWriter` (Perennial's `isRWMutexGuard`, no reader slot), finds the state under the lock,
and `Restore`/`Apply` are specified for whatever state they find (`Restore` by a dominance
premise, `Apply` by the caller's certificate for any state at or above its lower bound,
`storeApplyCert`). The latest tree is not fractional: it lives in an invariant of its own
(`storeTreeInv`, in `isStore`), from which the holder of the write lock borrows it
(`storeTree_borrow`/`storeTree_return`). `storeRevLb γ r` and `storeSnapLb γ r` are persistent
lower bounds on `latest.rev` and on the newest snapshot. `RWMutex` admits a bounded number of
readers, so every reader holds a token (`storeReader`, an `ownRWMutex`): `newStore` hands out
all but one.

**Certificates.** The lock-protected predicates (`storeLockInv`, `storeReader`,
`isStoreWriter`, `storeLockedPhys`) take a parameter `E : w64 → KvMap → IProp GF` that the
store's user picks at `newStore`: every history snapshot `(r, m)` carries `□ E r m` (the
ring's item predicate is `snapCert E`), `Restore` and `Apply` ask for it of the snapshots they
append (`applyEventsSnaps`, `applyRespSnaps`, `snapCerts`), and `getSnapshot`/`Get` return it of
the snapshot they read. The cache's `E` says that the map is etcd's state at that revision
(`isEtcdKvs`, `InvEtcd.lean`). A second parameter `R : w64 → IProp GF` certifies the latest
revision: the lock invariant holds `□ R latestRev`, `newStore` asks for `R 0`, `Restore` and
`Apply` for the revision they move it to (`applyRespRevs`), and `Get`/`LatestRev` return it of
the state seen. The cache's `R` (`cacheRev`, `InvCache.lean`) says that etcd has reached the
revision (`etcdReached`, `InvEtcd.lean`), so that its linearizable `Get` returns at least it,
and that it is at most the cache's revision bound, so that a `Restore` from such a `Get` is at
or above every revision the store can reach.

Models of the methods: `snapModel` (`getSnapshot`), `kvRange` (`snapshot.Range`),
`applyEvents`/`applyResp` (`Apply`), `restoreState` (`Restore`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Proof.go_etcd_io.etcd.cache.v3.InvRingBuffer
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3
  k8s_io.utils.third_party.forked.golang

/-! ## Keys -/

theorem goStringLt_irrefl (a : GoString) : ¬ go.GoStringLt a a := by
  induction a with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | cons h => exact ih h
    | rel h => exact Int.lt_irrefl _ h

theorem goStringLt_trans {a b c : GoString} (h1 : go.GoStringLt a b) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  induction h1 generalizing c with
  | nil => cases h2 <;> exact List.Lex.nil
  | cons h ih =>
    cases h2 with
    | cons h' => exact List.Lex.cons (ih h')
    | rel h' => exact List.Lex.rel h'
  | rel h =>
    cases h2 with
    | cons _ => exact List.Lex.rel h
    | rel h' => exact List.Lex.rel (Int.lt_trans h h')

/-- Go's `<` on strings is total: two strings neither less than the other are equal. -/
theorem goStringLt_eq_of_not_lt {a b : GoString} (h1 : ¬ go.GoStringLt a b)
    (h2 : ¬ go.GoStringLt b a) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => exact absurd List.Lex.nil h1
  | cons x xs ih =>
    cases b with
    | nil => exact absurd List.Lex.nil h2
    | cons y ys =>
      have hxy : x = y := by
        apply BitVec.eq_of_toNat_eq
        have a1 : ¬ (uint.Z x < uint.Z y) := fun h => h1 (List.Lex.rel h)
        have a2 : ¬ (uint.Z y < uint.Z x) := fun h => h2 (List.Lex.rel h)
        simp only [uint.Z] at a1 a2
        omega
      subst hxy
      rw [ih (fun h => h1 (List.Lex.cons h)) (fun h => h2 (List.Lex.cons h))]

/-- A map entry: a key and a `*mvccpb.KeyValue`. -/
abbrev KvEntry := GoString × Loc

/-- A key-value map: entries strictly sorted by key (`StoreInv`), as in the btree. -/
abbrev KvMap := List KvEntry

/-- Key order (Go's `kvItemLess`: `a.key < b.key`). -/
def kvLess (a b : KvEntry) : Prop := go.GoStringLt a.1 b.1

instance kvLess_dec : DecidableRel kvLess := fun a b => go.goStringLt_dec a.1 b.1

theorem kvLess_swo : StrictWeakOrder kvLess where
  irrefl a := goStringLt_irrefl a.1
  trans _ _ _ h1 h2 := goStringLt_trans h1 h2
  incomp_trans a b c h1 h2 h3 h4 := by
    have e1 := goStringLt_eq_of_not_lt h1 h2
    have e2 := goStringLt_eq_of_not_lt h3 h4
    unfold kvLess
    rw [e1, e2]
    exact ⟨goStringLt_irrefl _, goStringLt_irrefl _⟩

/-- Entries equivalent under `kvLess` have the same key. -/
theorem kvLess_equiv {a b : KvEntry} (h1 : ¬ kvLess a b) (h2 : ¬ kvLess b a) : a.1 = b.1 :=
  goStringLt_eq_of_not_lt h1 h2

/-! ## The model -/

/-- What `snapshot.Range(startKey, endKey)` returns, in key order: the entry with key
`startKey` if `endKey` is empty; those with key `≥ startKey` if `endKey` is `"\x00"` (a
prefix scan: "from key"); those with `startKey ≤ key < endKey` otherwise. -/
def kvRange (startKey endKey : GoString) (m : KvMap) : KvMap :=
  if endKey = [] then m.filter (fun e => decide (e.1 = startKey))
  else if endKey = [W8 0] then m.filter (fun e => !decide (go.GoStringLt e.1 startKey))
  else m.filter (fun e => !decide (go.GoStringLt e.1 startKey) && decide (go.GoStringLt e.1 endKey))

/-- The abstract state of a store. -/
structure StoreState where
  /-- `latest.rev` -/
  latestRev : w64
  /-- the contents of `latest.tree` -/
  latest : KvMap
  /-- the snapshots in the `history` ring, oldest first -/
  history : List (w64 × KvMap)

instance StoreState.countable : Pos.Countable StoreState :=
  .ofInjective (fun st => Pos.Countable.encode (st.latestRev, st.latest, st.history))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

/-- A new store's state. -/
def StoreState.init : StoreState := { latestRev := W64 0, latest := [], history := [] }

/-- What the store maintains, for a history of capacity `cap`: the latest revision is
not negative; the maps are sorted by key; the history has at most `cap` snapshots, with
strictly increasing revisions none above the latest revision. -/
structure StoreInv (cap : Nat) (st : StoreState) : Prop where
  cap_pos : 0 < cap
  cap_le : cap ≤ 2 ^ 61
  rev_nonneg : 0 ≤ sint.Z st.latestRev
  latest_sorted : st.latest.Pairwise kvLess
  hist_len : st.history.length ≤ cap
  hist_sorted : RevSorted Prod.fst st.history
  hist_le : ∀ h ∈ st.history, sint.Z h.1 ≤ sint.Z st.latestRev
  hist_maps_sorted : ∀ h ∈ st.history, h.2.Pairwise kvLess

/-- The newest snapshot is the latest map, when there is one: what `Restore` and a
successful `Apply` leave (a failed `Apply` can leave the latest map ahead of the history:
see `applyEvents`). Not part of `StoreInv`. -/
def StoreState.Synced (st : StoreState) : Prop :=
  ∀ h, st.history.getLast? = some h → h.2 = st.latest

/-- What `getSnapshot(rev)` finds. -/
inductive SnapResult where
  /-- `ErrNotReady`: nothing restored yet (`latest.rev = 0`) -/
  | notReady
  /-- `rev < 0`: "invalid revision" -/
  | invalid
  /-- `rpctypes.ErrFutureRev`: `rev` above the latest revision -/
  | future
  /-- `rpctypes.ErrCompacted`: no snapshot at or below `rev` in the history -/
  | compacted
  /-- the snapshot at revision `r` with map `m` -/
  | ok (r : w64) (m : KvMap)

/-- `getSnapshot(rev)` on state `st`: `rev = 0` means the latest revision; the result is
the snapshot with the greatest history revision at most `rev`. -/
def snapModel (st : StoreState) (rev : w64) : SnapResult :=
  if st.latestRev = W64 0 then .notReady
  else if sint.Z rev < 0 then .invalid
  else
    let rev' := if rev = W64 0 then st.latestRev else rev
    if sint.Z st.latestRev < sint.Z rev' then .future
    else match (st.history.filter (fun h => decide (sint.Z h.1 ≤ sint.Z rev'))).getLast? with
      | some h => .ok h.1 h.2
      | none => .compacted

/-- A watch event, as the store reads it: its type (`mvccpb.Event_EventType`: `0` put,
`1` delete), its key (`string(ev.Kv.Key)`), its `*KeyValue` and that one's
`ModRevision`. -/
structure EvModel where
  typ : w32
  key : GoString
  kv : Loc
  rev : w64

/-- The events' revisions do not decrease (etcd's watch stream; `Apply` needs it so that
the history's revisions increase). -/
def EvRevSorted (evs : List EvModel) : Prop :=
  evs.Pairwise (fun a b => sint.Z a.rev ≤ sint.Z b.rev)

/-- One event applied to a map (the `switch` in `applyEventsLocked`): a delete of a
missing key fails (`none`); a type other than put or delete changes nothing. -/
def applyEv (m : KvMap) (e : EvModel) : Option KvMap :=
  if e.typ = W32 1 then
    if (btFind kvLess (e.key, null) m).isSome then some (btDelete kvLess (e.key, null) m)
    else none
  else if e.typ = W32 0 then some (btInsert kvLess (e.key, e.kv) m)
  else some m

/-- A batch of events applied in order: the map, and `false` if some event failed, the
map then being the one the failing event found. -/
def applyBatch : KvMap → List EvModel → KvMap × Bool
  | m, [] => (m, true)
  | m, e :: es => match applyEv m e with
    | some m' => applyBatch m' es
    | none => (m, false)

theorem dropWhile_length_lt (e : EvModel) (es : List EvModel) :
    ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))).length < (e :: es).length := by
  simp only [List.dropWhile_cons, decide_true]
  exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le

/-- `applyEventsLocked(events)` on state `st`, for a history of capacity `cap`: the events
are taken in batches of equal revision; each batch is applied to the latest map, then the
latest revision becomes the batch's and a snapshot of the map is appended to the history
(`ringAppend`). If an event of a batch fails (a delete of a missing key), the result is
`false` and the state is the one the code leaves: the earlier batches applied (with their
snapshots and revision), and the failing batch's events before the failing one applied to
the latest map, with no snapshot and the revision of the previous batch. -/
def applyEvents (cap : Nat) : StoreState → List EvModel → StoreState × Bool
  | st, [] => (st, true)
  | st, e :: es =>
    match applyBatch st.latest ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))) with
    | (m, true) => applyEvents cap
        { latestRev := e.rev, latest := m, history := ringAppend cap st.history (e.rev, m) }
        ((e :: es).dropWhile (fun x => decide (x.rev = e.rev)))
    | (m, false) => ({ st with latest := m }, false)
termination_by _ evs => evs.length
decreasing_by exact dropWhile_length_lt e es

/-- The snapshots `applyEvents` appends to the history, in order, whether or not the ring keeps
them: `(rev, map)` for each batch that applies (`applyEvents` stops at a failing one). Depends
on the latest map only. `Apply`'s caller certifies each of them (`snapCerts`). -/
def applyEventsSnaps : KvMap → List EvModel → List (w64 × KvMap)
  | _, [] => []
  | m, e :: es =>
    match applyBatch m ((e :: es).takeWhile (fun x => decide (x.rev = e.rev))) with
    | (m', true) => (e.rev, m') ::
        applyEventsSnaps m' ((e :: es).dropWhile (fun x => decide (x.rev = e.rev)))
    | (_, false) => []
termination_by _ evs => evs.length
decreasing_by exact dropWhile_length_lt e es

/-- A `go_etcd_io.etcd.client.v3.WatchResponse` as `Apply` reads it. `hdrRev` is the header's revision
(`0` for a nil header, as `Header.GetRevision()`). -/
structure RespModel where
  events : List EvModel
  compactRev : w64
  canceled : Bool
  created : Bool
  hdrRev : w64

/-- `resp.IsProgressNotify()`. -/
def RespModel.isProgressNotify (r : RespModel) : Bool :=
  r.events.isEmpty && !r.canceled && !r.created && decide (r.compactRev = W64 0) &&
    !decide (r.hdrRev = W64 0)

/-- `validateRevisions(resp, latestRev) == nil`: a progress notification not behind the
latest revision, or events all above it. -/
def validRevisions (r : RespModel) (latestRev : w64) : Bool :=
  if r.isProgressNotify then !decide (sint.Z r.hdrRev < sint.Z latestRev)
  else r.events.all (fun e => decide (sint.Z latestRev < sint.Z e.rev))

/-- `Apply(resp)` on state `st`: the new state, and whether it returned `nil`. A canceled
response or one failing `validateRevisions` changes nothing; a progress notification sets
the latest revision to the header's once the store has one (`latest.rev ≠ 0`); events are
applied by `applyEvents`; anything else changes nothing. -/
def applyResp (cap : Nat) (st : StoreState) (r : RespModel) : StoreState × Bool :=
  if r.canceled then (st, false)
  else if !validRevisions r st.latestRev then (st, false)
  else if r.isProgressNotify then
    (if st.latestRev = W64 0 then st else { st with latestRev := r.hdrRev }, true)
  else if !r.events.isEmpty then applyEvents cap st r.events
  else (st, true)

/-- The snapshots `Apply(r)` appends to the history (those of `applyEvents`, when it runs). -/
def applyRespSnaps (st : StoreState) (r : RespModel) : List (w64 × KvMap) :=
  if r.canceled then []
  else if !validRevisions r st.latestRev then []
  else if r.isProgressNotify then []
  else if !r.events.isEmpty then applyEventsSnaps st.latest r.events
  else []

/-- The revisions `Apply(r)` may move the latest revision to: a progress notification's header
revision, or the revision of a snapshot it appends (`applyRespSnaps`). `Apply`'s caller certifies
each of them (the store's `R`). -/
def applyRespRevs (st : StoreState) (r : RespModel) : List w64 :=
  if r.canceled then []
  else if !validRevisions r st.latestRev then []
  else if r.isProgressNotify then [r.hdrRev]
  else if !r.events.isEmpty then (applyEventsSnaps st.latest r.events).map Prod.fst
  else []

/-- The map `Restore` builds: the key-values `ReplaceOrInsert`ed in order into an empty
tree (a later duplicate key replaces an earlier one). -/
def restoreMap (kvs : KvMap) : KvMap :=
  kvs.foldl (fun m e => btInsert kvLess e m) []

/-- What `Restore(kvs, rev)` leaves: `rev`, the map, and a history of that one snapshot. -/
def restoreState (rev : w64) (kvs : KvMap) : StoreState :=
  { latestRev := rev, latest := restoreMap kvs, history := [(rev, restoreMap kvs)] }

theorem qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

/-! ## `Synced` -/

theorem ringAppend_getLast {V : Type} (cap : Nat) (items : List V) (v : V) :
    (ringAppend cap items v).getLast? = some v := by
  unfold ringAppend; split <;> simp

theorem restoreState_synced (rev : w64) (kvs : KvMap) : (restoreState rev kvs).Synced := by
  intro h hh; simp [restoreState] at hh; subst hh; rfl

theorem applyEvents_synced (cap : Nat) :
    ∀ (evs : List EvModel) (st : StoreState), st.Synced → (applyEvents cap st evs).2 = true →
      (applyEvents cap st evs).1.Synced := by
  intro evs
  induction h : evs.length using Nat.strongRecOn generalizing evs with
  | ind n ih =>
    intro st hs hok
    match evs with
    | [] => simpa [applyEvents] using hs
    | e :: es =>
      rw [applyEvents] at hok ⊢
      split at hok
      · rename_i m hb
        refine ih _ (h ▸ dropWhile_length_lt e es) _ rfl _ ?_ hok
        intro x hx
        rw [ringAppend_getLast cap] at hx
        cases hx; rfl
      · simp at hok

theorem applyResp_synced (cap : Nat) (st : StoreState) (r : RespModel)
    (hs : st.Synced) (hok : (applyResp cap st r).2 = true) : (applyResp cap st r).1.Synced := by
  unfold applyResp at *
  split
  · exact hs
  split
  · exact hs
  split
  · split
    · exact hs
    · intro h hh; exact hs h hh
  split
  · rename_i h1 h2 h3 h4
    simp only [h1, h2, h3, h4, ite_false, ite_true, Bool.false_eq_true] at hok
    exact applyEvents_synced cap _ _ hs hok
  · exact hs

/-- `applyEvents` leaves the latest revision, or moves it to a snapshot's it appends. -/
theorem applyEvents_latestRev_mem (cap : Nat) :
    ∀ (evs : List EvModel) (st : StoreState),
      (applyEvents cap st evs).1.latestRev = st.latestRev ∨
        (applyEvents cap st evs).1.latestRev ∈ (applyEventsSnaps st.latest evs).map Prod.fst := by
  intro evs
  induction h : evs.length using Nat.strongRecOn generalizing evs with
  | ind n ih =>
    intro st
    match evs with
    | [] => left; simp [applyEvents]
    | e :: es =>
      rw [applyEvents, applyEventsSnaps]
      split
      · rename_i m hb
        simp only [hb, List.map_cons, List.mem_cons]
        rcases ih _ (h ▸ dropWhile_length_lt e es) _ rfl
          { latestRev := e.rev, latest := m, history := ringAppend cap st.history (e.rev, m) }
          with h1 | h1
        · right; left; exact h1
        · right; right; exact h1
      · rename_i m hb
        left; rfl

/-- `Apply` leaves the latest revision, or moves it to one of `applyRespRevs`. -/
theorem applyResp_latestRev_mem (cap : Nat) (st : StoreState) (r : RespModel) :
    (applyResp cap st r).1.latestRev = st.latestRev ∨
      (applyResp cap st r).1.latestRev ∈ applyRespRevs st r := by
  unfold applyResp applyRespRevs
  split
  · left; rfl
  split
  · left; rfl
  split
  · split
    · left; rfl
    · right; simp
  split
  · exact applyEvents_latestRev_mem cap _ _
  · left; rfl

/-- The revisions of the snapshots `applyEvents` appends are revisions of its events. -/
theorem applyEventsSnaps_rev_mem :
    ∀ (evs : List EvModel) (m : KvMap) (h : w64 × KvMap), h ∈ applyEventsSnaps m evs →
      ∃ e ∈ evs, e.rev = h.1 := by
  intro evs
  induction hn : evs.length using Nat.strongRecOn generalizing evs with
  | ind n ih =>
    intro m h hh
    match evs with
    | [] => simp [applyEventsSnaps] at hh
    | e :: es =>
      rw [applyEventsSnaps] at hh
      split at hh
      · rename_i m' hb
        rcases List.mem_cons.1 hh with rfl | hh
        · exact ⟨e, List.mem_cons_self, rfl⟩
        · obtain ⟨x, hx, hxr⟩ := ih _ (hn ▸ dropWhile_length_lt e es) _ rfl _ _ hh
          exact ⟨x, (List.dropWhile_suffix _).subset hx, hxr⟩
      · simp at hh

/-- A revision `Apply` may move the latest revision to is a progress notification's (a response
without events) or one of its events'. -/
theorem applyRespRevs_mem (st : StoreState) (r : RespModel) (x : w64)
    (h : x ∈ applyRespRevs st r) : (r.events = [] ∧ x = r.hdrRev) ∨ ∃ e ∈ r.events, e.rev = x := by
  unfold applyRespRevs at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i hp
    left
    refine ⟨?_, by simpa using h⟩
    unfold RespModel.isProgressNotify at hp
    simp only [Bool.and_eq_true] at hp
    exact List.isEmpty_iff.1 hp.1.1.1.1
  split at h
  · right
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact applyEventsSnaps_rev_mem _ _ _ hy
  · simp at h

/-! ## The newest snapshot (`storeSnapKey`) -/

/-- The newest snapshot's revision plus one, `0` with no history (or a negative newest revision,
which the store never has): what `γ.snap` counts. -/
def storeSnapKey (st : StoreState) : Nat :=
  match st.history.getLast? with
  | some h => if 0 ≤ sint.Z h.1 then sint.nat h.1 + 1 else 0
  | none => 0


theorem evs_dropWhile_gt (e : EvModel) (es : List EvModel) (hs : EvRevSorted (e :: es)) :
    ∀ x ∈ (e :: es).dropWhile (fun x => decide (x.rev = e.rev)), sint.Z e.rev < sint.Z x.rev := by
  intro x hx
  have hsuf : ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))).IsSuffix (e :: es) :=
    List.dropWhile_suffix _
  cases hd : (e :: es).dropWhile (fun x => decide (x.rev = e.rev)) with
  | nil => rw [hd] at hx; cases hx
  | cons h t =>
    rw [hd] at hx hsuf
    have hh : ¬ (h.rev = e.rev) := by
      have := List.head?_dropWhile_not (fun x => decide (x.rev = e.rev)) (e :: es)
      rw [hd] at this
      simpa using this
    have hsorted : EvRevSorted (h :: t) := List.Pairwise.sublist hsuf.sublist hs
    have hmem : h ∈ e :: es := hsuf.subset List.mem_cons_self
    have heh : sint.Z e.rev ≤ sint.Z h.rev := by
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact Int.le_refl _
      · exact (List.pairwise_cons.1 hs).1 h hmem
    have hlt : sint.Z e.rev < sint.Z h.rev := by
      rcases Int.lt_or_eq_of_le heh with h1 | h1
      · exact h1
      · exfalso; apply hh; exact (BitVec.eq_of_toInt_eq (by simpa [sint.Z] using h1)).symm
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hlt
    · exact Int.lt_of_lt_of_le hlt ((List.pairwise_cons.1 hsorted).1 x hx)

theorem storeSnapKey_of_last (st : StoreState) (Y : w64) (m : KvMap)
    (h : st.history.getLast? = some (Y, m)) (hY : 0 ≤ sint.Z Y) :
    storeSnapKey st = sint.nat Y + 1 := by
  simp [storeSnapKey, h, hY]

theorem storeSnapKey_le (cap : Nat) (st : StoreState) (hinv : StoreInv cap st) :
    storeSnapKey st ≤ sint.nat st.latestRev + 1 := by
  unfold storeSnapKey
  cases h : st.history.getLast? with
  | none => simp
  | some x =>
    have h1 := hinv.hist_le x (List.mem_of_getLast? h)
    have h2 : sint.nat x.1 ≤ sint.nat st.latestRev := Int.toNat_le_toNat h1
    simp only
    split <;> omega

theorem storeSnapKey_restore (rev : w64) (kvs : KvMap) (h : 0 ≤ sint.Z rev) :
    storeSnapKey (restoreState rev kvs) = sint.nat rev + 1 := by
  simp [storeSnapKey, restoreState, h]

/-- A synced state whose newest snapshot's key is at least `lo + 1` has a newest snapshot, the
latest map, at a revision at least `lo`. -/
theorem storeSnapKey_last (st : StoreState) (lo : w64) (hsync : st.Synced) (hlo : 0 ≤ sint.Z lo)
    (hk : sint.nat lo + 1 ≤ storeSnapKey st) :
    ∃ Y, st.history.getLast? = some (Y, st.latest) ∧ sint.Z lo ≤ sint.Z Y := by
  unfold storeSnapKey at hk
  cases h : st.history.getLast? with
  | none => rw [h] at hk; simp at hk
  | some x =>
    rw [h] at hk
    simp only at hk
    split at hk
    · rename_i hx
      refine ⟨x.1, ?_, ?_⟩
      · rw [← hsync x h]
      · have h1 : ((sint.nat lo : Nat) : Int) = sint.Z lo := Int.toNat_of_nonneg hlo
        have h2 : ((sint.nat x.1 : Nat) : Int) = sint.Z x.1 := Int.toNat_of_nonneg hx
        omega
    · omega

/-- `applyEvents` does not lower the newest snapshot's revision. -/
theorem applyEvents_snapKey (cap : Nat) :
    ∀ (evs : List EvModel) (st : StoreState), EvRevSorted evs →
      (∀ e ∈ evs, sint.Z st.latestRev < sint.Z e.rev) → 0 ≤ sint.Z st.latestRev →
      storeSnapKey st ≤ sint.nat st.latestRev + 1 →
      storeSnapKey st ≤ storeSnapKey (applyEvents cap st evs).1 := by
  intro evs
  induction h : evs.length using Nat.strongRecOn generalizing evs with
  | ind n ih =>
    intro st hs habove hnn hkey
    match evs with
    | [] => simp [applyEvents]
    | e :: es =>
      rw [applyEvents]
      split
      · rename_i m hb
        have hlen : ((e :: es).dropWhile (fun x => decide (x.rev = e.rev))).length < n := by
          rw [← h]; exact dropWhile_length_lt e es
        have he := habove e List.mem_cons_self
        have hk1 : storeSnapKey
            { latestRev := e.rev, latest := m, history := ringAppend cap st.history (e.rev, m) } =
            sint.nat e.rev + 1 := by
          have : 0 ≤ sint.Z e.rev := by omega
          simp [storeSnapKey, ringAppend_getLast, this]
        have hle : sint.nat st.latestRev ≤ sint.nat e.rev := by
          simp only [sint.nat]; exact Int.toNat_le_toNat (Int.le_of_lt he)
        have := ih _ hlen _ rfl
          { latestRev := e.rev, latest := m, history := ringAppend cap st.history (e.rev, m) }
          (List.Pairwise.sublist (List.dropWhile_suffix _).sublist hs)
          (evs_dropWhile_gt e es hs) (by simp only; omega) (by rw [hk1]; exact Nat.le_refl _)
        omega
      · simp [storeSnapKey]

/-- `Apply` does not lower the newest snapshot's revision. -/
theorem applyResp_snapKey (cap : Nat) (st : StoreState) (r : RespModel) (hinv : StoreInv cap st)
    (hs : EvRevSorted r.events) :
    storeSnapKey st ≤ storeSnapKey (applyResp cap st r).1 := by
  unfold applyResp
  split
  · exact Nat.le_refl _
  split
  · exact Nat.le_refl _
  rename_i h2
  split
  · split
    · exact Nat.le_refl _
    · simp [storeSnapKey]
  rename_i h3
  split
  · apply applyEvents_snapKey cap r.events st hs _ hinv.rev_nonneg (storeSnapKey_le cap st hinv)
    have hv : validRevisions r st.latestRev = true := by simpa using h2
    simp only [validRevisions, h3, Bool.false_eq_true, ↓reduceIte, List.all_eq_true,
      decide_eq_true_eq] at hv
    exact hv
  · exact Nat.le_refl _

/-! ## Predicates -/

/-- The ghost names of a store. -/
structure StoreNames where
  /-- the abstract state (`ghostVar`, in the lock: its fractions agree) -/
  state : GName
  /-- `latest.rev`, monotone (`monoNat`, in the lock) -/
  rev : GName
  /-- the newest snapshot's revision plus one, `0` before the first (`storeSnapKey`;
  `monoNat`, in the lock) -/
  snap : GName
  /-- where the latest tree is (`ghostVar` of an `Option KvMap`): `some m` while it is in the
  store's tree invariant (`storeTreeInv`, holding `m`), `none` while the write lock's holder has
  it -/
  tree : GName

/-- The Go type of the store's btree items, `*kvItem`. -/
abbrev kvItemPtrT [FfiSyntax] [GoGlobalContext] : go.GoType := go.GoType.PointerType kvItem.ty

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `s.latest.rev`. -/
abbrev storeLatestRevAddr (s : Loc) : Loc :=
  structFieldRef snapshot go!"rev" (structFieldRef store go!"latest" s)

/-- The address of `s.latest.tree`. -/
abbrev storeLatestTreeAddr (s : Loc) : Loc :=
  structFieldRef snapshot go!"tree" (structFieldRef store go!"latest" s)

/-- The address of `s.history`. -/
abbrev storeHistAddr (s : Loc) : Loc := structFieldRef store go!"history" s

/-- The address of `s.mu`. -/
abbrev storeMuAddr (s : Loc) : Loc := structFieldRef store go!"mu" s

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `TypeRepr` of the protobuf messages the store reads fields of (named and underlying
types), straight from their
`TypeAssumptions` (`type_repr_underlying`). Without these, the `StructFieldRef` step finds
`TypeRepr` through the struct's `IntoValTyped` instance, which is built from the opaque
`impl.MessageState`'s `sorry` instances ("axiomatized type"), putting them in the trust
base for nothing. -/
instance (priority := high) keyValue_typeRepr : TypeRepr mvccpb.KeyValue.ty mvccpb.KeyValue :=
  go.type_repr_underlying (u := mvccpb.KeyValue.underlying)

instance (priority := high) event_typeRepr : TypeRepr mvccpb.Event.ty mvccpb.Event :=
  go.type_repr_underlying (u := mvccpb.Event.underlying)

instance (priority := high) responseHeader_typeRepr :
    TypeRepr etcdserverpb.ResponseHeader.ty etcdserverpb.ResponseHeader :=
  go.type_repr_underlying (u := etcdserverpb.ResponseHeader.underlying)

instance (priority := high) keyValue_typeRepr_u :
    TypeRepr mvccpb.KeyValue.underlying mvccpb.KeyValue :=
  go.type_repr_underlying (u := mvccpb.KeyValue.underlying)

instance (priority := high) event_typeRepr_u : TypeRepr mvccpb.Event.underlying mvccpb.Event :=
  go.type_repr_underlying (u := mvccpb.Event.underlying)

instance (priority := high) responseHeader_typeRepr_u :
    TypeRepr etcdserverpb.ResponseHeader.underlying etcdserverpb.ResponseHeader :=
  go.type_repr_underlying (u := etcdserverpb.ResponseHeader.underlying)

/-- `p` points for good to `kvItem{key: e.1, kv: e.2}` (a btree item, or a probe with
`kv = nil`). -/
def kvItemIs (p : Loc) (e : KvEntry) : IProp GF :=
  typedPointsto p (kvItem.mk e.1 e.2) DFrac.discard

instance kvItemIs_persistent (p : Loc) (e : KvEntry) : Persistent (kvItemIs (GF := GF) p e) := by
  unfold kvItemIs; infer_instance

/-- `e.2` is a `*KeyValue` whose `Key` field holds, for good, a slice of the bytes `e.1`.
Stated on the field, not the struct: a protobuf message's struct points-to includes its
opaque `state` (`impl.MessageState`, an axiomatized type whose generated instances are
`sorry`), which the store never reads. -/
def kvAt (e : KvEntry) : IProp GF :=
  iprop(∃ keySl : GoSlice, structFieldRef mvccpb.KeyValue go!"Key" e.2 ↦□ keySl ∗
    keySl ↦*□ e.1)

instance kvAt_persistent (e : KvEntry) : Persistent (kvAt (GF := GF) e) := by
  unfold kvAt; infer_instance

/-- Every entry of `m` is `kvAt`. -/
def kvsAt (m : KvMap) : IProp GF := iprop(□ ∀ e, ⌜e ∈ m⌝ -∗ kvAt e)

instance kvsAt_persistent (m : KvMap) : Persistent (kvsAt (GF := GF) m) := by
  unfold kvsAt; infer_instance

/-- `p` is a `*snapshot` at revision `h.1` (read-only) whose tree holds the map `h.2`
(read-only), sorted, of `kvAt` entries: an item of the history ring. -/
def snapIs (p : Loc) (h : w64 × KvMap) : IProp GF :=
  iprop(∃ t : Loc, p ↦□ snapshot.mk h.1 t ∗
    ownBTree kvItemPtrT t (kvItemIs (hG := hG)) kvLess h.2 DFrac.discard ∗ kvsAt h.2 ∗
    ⌜h.2.Pairwise kvLess⌝)

instance snapIs_persistent (p : Loc) (h : w64 × KvMap) : Persistent (snapIs (GF := GF) p h) := by
  unfold snapIs; infer_instance

/-- A history item with its certificate: `snapIs p h` and `□ E h.1 h.2`. `E` is the store's
certificate parameter: what its user knows of every snapshot (the cache: that the map is etcd's
state at that revision, `InvEtcd.lean`); the store only carries it, from `Restore`/`Apply`'s
callers to `getSnapshot`/`Get`'s. Under `□`, so any `E` will do (the cache's is persistent). -/
def snapCert (E : w64 → KvMap → IProp GF) (p : Loc) (h : w64 × KvMap) : IProp GF :=
  iprop(snapIs p h ∗ □ E h.1 h.2)

instance snapCert_persistent (E : w64 → KvMap → IProp GF) (p : Loc) (h : w64 × KvMap) :
    Persistent (snapCert E p h) := by
  unfold snapCert; infer_instance

/-- Every snapshot of `hs` is certified by `E`. -/
def snapCerts (E : w64 → KvMap → IProp GF) (hs : List (w64 × KvMap)) : IProp GF :=
  iprop(□ ∀ h, ⌜h ∈ hs⌝ -∗ E h.1 h.2)

instance snapCerts_persistent (E : w64 → KvMap → IProp GF) (hs : List (w64 × KvMap)) :
    Persistent (snapCerts E hs) := by
  unfold snapCerts; infer_instance

/-- Every revision of `rs` is certified by `R`. -/
def revCerts (R : w64 → IProp GF) (rs : List w64) : IProp GF :=
  iprop(□ ∀ r, ⌜r ∈ rs⌝ -∗ R r)

instance revCerts_persistent (R : w64 → IProp GF) (rs : List w64) :
    Persistent (revCerts R rs) := by
  unfold revCerts; infer_instance

theorem snapCerts_cons (E : w64 → KvMap → IProp GF) (h : w64 × KvMap) (hs : List (w64 × KvMap)) :
    snapCerts E (h :: hs) ⊢ □ E h.1 h.2 ∗ snapCerts E hs := by
  unfold snapCerts
  iintro #H
  isplitl []
  · imodintro; iapply H; ipureintro; exact List.mem_cons_self
  · imodintro; iintro %x %hx; iapply H; ipureintro; exact List.mem_cons_of_mem _ hx

/-- The latest tree, owned by the writer: `s.latest.tree` is a tree holding `m`. -/
def storeLatestTree (s : Loc) (m : KvMap) : IProp GF :=
  iprop(∃ t : Loc, storeLatestTreeAddr s ↦ t ∗
    ownBTree kvItemPtrT t (kvItemIs (hG := hG)) kvLess m (DFrac.own 1) ∗ kvsAt m)

/-- What the writer holds while it holds the write lock (`applyEventsLocked`,
`applyProgressNotifyLocked`): the latest revision, the history ring and the latest
tree. -/
def storeLockedPhys (s : Loc) (cap : Nat) (E : w64 → KvMap → IProp GF) (st : StoreState) :
    IProp GF :=
  iprop(storeLatestRevAddr s ↦ st.latestRev ∗
    ownRingBuffer (storeHistAddr s) cap (snapCert E) Prod.fst st.history ∗
    storeLatestTree s st.latest)

/-- The namespace of a store's tree invariant (`storeTreeInv`). -/
def storeTreeN : Namespace := nroot.@"cacheStoreTree"

/-- **The latest tree**, in an invariant of its own: the tree holding `m` while `γ.tree` is
`some m`, or nothing while it is lent (`none`) to the holder of the write lock (who holds the lock's
half of `γ.tree`: `storeLockRest` at fraction `1`). The tree is not fractional, so it cannot be
part of the lock's fractional invariant itself; any number of writers (`Restore`, `Apply`) take it
in turn, under the write lock. -/
def storeTreeInv (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ o : Option KvMap, ghostVar γ.tree (1 : Qp).half o ∗
    match o with
    | some m => storeLatestTree s m
    | none => True)

/-- The lock invariant's ghost rest at fraction `q`, for state `st`: `q/2` of `γ.tree` at
`some st.latest` (the tree invariant holds the other half), `q` of the newest snapshot's
counter, and that the newest snapshot is the latest map (`Synced`: every `Apply` that changes
the store succeeds). -/
def storeLockRest (γ : StoreNames) (q : Qp) (st : StoreState) : IProp GF :=
  iprop(ghostVar γ.tree (q.half) (some st.latest) ∗ monoNatAuthOwn γ.snap q (storeSnapKey st) ∗
    ⌜st.Synced⌝)

instance storeLockRest_fractional (γ : StoreNames) (st : StoreState) :
    Fractional (fun q => storeLockRest (GF := GF) γ q st) where
  fractional q1 q2 := by
    have hgv := (ghostVar_fractional (GF := GF) γ.tree (some st.latest)).fractional q1.half q2.half
    have hmono := (monoNatAuthOwn_fractional (GF := GF) γ.snap (storeSnapKey st)).fractional q1 q2
    unfold storeLockRest
    rw [qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro ⟨Ht, Hs, %Hsy⟩
      icases hgv.1 $$ Ht with ⟨Ht1, Ht2⟩
      icases hmono.1 $$ Hs with ⟨Hs1, Hs2⟩
      isplitl [Ht1 Hs1]
      · iframe; ipureintro; exact Hsy
      · iframe; ipureintro; exact Hsy
    · iintro ⟨⟨Ht1, Hs1, %Hsy⟩, ⟨Ht2, Hs2, -⟩⟩
      isplitl [Ht1 Ht2]
      · iapply hgv.2; iframe
      isplitl [Hs1 Hs2]
      · iapply hmono.2; iframe
      ipureintro; exact Hsy

/-- The lock invariant `P q` of `s.mu` (see the module docstring). -/
def storeLockInv (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF)
    (R : w64 → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ st : StoreState,
    "Hst" ∷ ghostVar γ.state q st ∗
    "Hrev" ∷ monoNatAuthOwn γ.rev q (sint.nat st.latestRev) ∗
    "HlatestRev" ∷ storeLatestRevAddr s ↦{DFrac.own q} st.latestRev ∗
    "Hhist" ∷ ownRingBuffer (storeHistAddr s) cap (snapCert E) Prod.fst st.history (DFrac.own q) ∗
    "Hrest" ∷ storeLockRest γ q st ∗
    "#HR" ∷ □ R st.latestRev ∗
    "%Hinv" ∷ ⌜StoreInv cap st⌝)

instance storeLockInv_fractional (s : Loc) (γ : StoreNames) (cap : Nat)
    (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF) :
    Fractional (storeLockInv (GF := GF) s γ cap E R) where
  fractional q1 q2 := by
    have hrev : ∀ r : w64, (storeLatestRevAddr s ↦{DFrac.own (q1 + q2)} r : IProp GF) ⊣⊢
        storeLatestRevAddr s ↦{DFrac.own q1} r ∗ storeLatestRevAddr s ↦{DFrac.own q2} r :=
      fun r => (typedPointsto_dfractional (GF := GF) _ r).dfractional (DFrac.own q1) (DFrac.own q2)
    have hring := fun (hs : List (w64 × KvMap)) =>
      (ownRingBuffer_fractional (GF := GF) (storeHistAddr s) cap (snapCert E) Prod.fst hs).fractional q1 q2
    have hmono := fun (n : Nat) => (monoNatAuthOwn_fractional (GF := GF) γ.rev n).fractional q1 q2
    have hgv := fun (st : StoreState) =>
      (ghostVar_fractional (GF := GF) γ.state st).fractional q1 q2
    have hrest := fun (st : StoreState) => (storeLockRest_fractional (GF := GF) γ st).fractional q1 q2
    refine ⟨?_, ?_⟩
    · iintro H
      unfold storeLockInv
      iNamed H
      icases (hgv st).1 $$ Hst with ⟨Hst1, Hst2⟩
      icases (hmono _).1 $$ Hrev with ⟨Hrev1, Hrev2⟩
      icases (hrev _).1 $$ HlatestRev with ⟨Hl1, Hl2⟩
      icases (hring _).1 $$ Hhist with ⟨Hh1, Hh2⟩
      icases (hrest st).1 $$ Hrest with ⟨Hr1, Hr2⟩
      isplitl [Hst1 Hrev1 Hl1 Hh1 Hr1]
      · iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
      · iexists st; simp only [named]; iframe; iframe #; ipureintro; exact Hinv
    · iintro ⟨H1, H2⟩
      unfold storeLockInv
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hst1 Hst2 gives % ⟨_, Heq⟩
      subst Heq
      iexists st
      simp only [named]
      isplitl [Hst1 Hst2]
      · iapply (hgv st).2; iframe
      isplitl [Hrev1 Hrev2]
      · iapply (hmono _).2; iframe
      isplitl [HlatestRev1 HlatestRev2]
      · iapply (hrev _).2; iframe
      isplitl [Hhist1 Hhist2]
      · iapply (hring _).2; iframe
      isplitl [Hrest1 Hrest2]
      · iapply (hrest st).2; iframe
      iframe #
      ipureintro; exact Hinv1

/-- `s` is a store with a history of capacity `cap` (persistent): `s.revCond` is a
condition variable on `s.mu.RLocker()` (`sync.rlockerOf`: its `Lock`/`Unlock` are `s.mu`'s
`RLock`/`RUnlock`, `sync.rlocker_isLockerWith`), `s.degree` the btrees' degree, and the latest
tree is in its invariant (`storeTreeInv`). `γ` names the store's ghost state (held by
`storeReader`, `isStoreWriter`, `storeRevLb`, `storeSnapLb`). -/
def isStore (s : Loc) (γ : StoreNames) (cap : Nat) : IProp GF :=
  iprop(∃ (c : Loc) (deg : w64),
    "#HrevCond" ∷ structFieldRef store go!"revCond" s ↦□ c ∗
    "#Hcond" ∷ sync.isCond c (sync.rlockerOf (storeMuAddr s)) ∗
    "#Hdeg" ∷ structFieldRef store go!"degree" s ↦□ deg ∗
    "#Htree" ∷ inv storeTreeN (storeTreeInv s γ) ∗
    "%Hdeg" ∷ ⌜1 < sint.Z deg ∧ sint.Z deg ≤ 2 ^ 62⌝ ∗
    "%Hcap" ∷ ⌜0 < cap ∧ cap ≤ 2 ^ 61⌝)

instance isStore_persistent (s : Loc) (γ : StoreNames) (cap : Nat) :
    Persistent (isStore (GF := GF) s γ cap) := by
  unfold isStore named; infer_instance

/-- A lower bound on the store's latest revision (persistent). -/
def storeRevLb (γ : StoreNames) (r : w64) : IProp GF := monoNatLbOwn γ.rev (sint.nat r)

instance storeRevLb_persistent (γ : StoreNames) (r : w64) :
    Persistent (storeRevLb (GF := GF) γ r) := by
  unfold storeRevLb; infer_instance

/-- A reader's token: one of the `RWMutex`'s bounded reader slots (`RLock` needs one). -/
def storeReader (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF)
    (R : w64 → IProp GF) : IProp GF :=
  sync.ownRWMutex (storeMuAddr s) (storeLockInv (hG := hG) s γ cap E R)

/-- The writers' handle on the store (persistent): `Restore` and `Apply` take the write lock with
it (`sync.isRWMutexGuard`: a writer needs none of the `RWMutex`'s bounded reader slots), so any
number of goroutines may write, in turn. Everything a writer needs to know of the state is in
the lock invariant: `Restore` and `Apply` are specified for the state they find there. -/
def isStoreWriter (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF)
    (R : w64 → IProp GF) : IProp GF :=
  sync.isRWMutexGuard (storeMuAddr s) (storeLockInv (hG := hG) s γ cap E R)

instance isStoreWriter_persistent (s : Loc) (γ : StoreNames) (cap : Nat)
    (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF) :
    Persistent (isStoreWriter (GF := GF) s γ cap E R) := by
  unfold isStoreWriter; infer_instance

/-- A lower bound on the store's newest snapshot's revision (persistent): the store has a
snapshot, the newest at revision at least `r`, and, the store being synced, it is the latest map. -/
def storeSnapLb (γ : StoreNames) (r : w64) : IProp GF := monoNatLbOwn γ.snap (sint.nat r + 1)

instance storeSnapLb_persistent (γ : StoreNames) (r : w64) :
    Persistent (storeSnapLb (GF := GF) γ r) := by
  unfold storeSnapLb; infer_instance

theorem storeSnapLb_mono (γ : StoreNames) (r r' : w64) (h : sint.Z r' ≤ sint.Z r) :
    storeSnapLb (GF := GF) γ r ⊢ storeSnapLb γ r' := by
  unfold storeSnapLb
  iintro H
  iapply monoNatLbOwn_le _ (Nat.add_le_add_right (Int.toNat_le_toNat h) 1) $$ H

/-- **What `Apply(r)`'s caller certifies** (persistent), for every state `st` the store may be in
whose newest snapshot `(Y, st.latest)` is at or above the caller's lower bound `lo` (the caller
holds `storeSnapLb γ lo`), with that snapshot's certificate `□ E Y st.latest`: `Apply` either
changes nothing or succeeds, and the snapshots it appends and the revisions it may move the
latest revision to are certified (`snapCerts E`, `revCerts R`). Several writers may apply
responses in any interleaving: each certifies its response relative to whatever state it finds
(a stale response, which `validateRevisions` rejects, changes nothing). -/
def storeApplyCert (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF) (lo : w64)
    (r : RespModel) : IProp GF :=
  iprop(□ ∀ (st : StoreState) (Y : w64),
    ⌜StoreInv cap st ∧ st.history.getLast? = some (Y, st.latest) ∧ sint.Z lo ≤ sint.Z Y⌝ -∗
    □ E Y st.latest -∗
    ⌜(applyResp cap st r).2 = true ∨ (applyResp cap st r).1 = st⌝ ∗
      snapCerts E (applyRespSnaps st r) ∗ revCerts R (applyRespRevs st r))

instance storeApplyCert_persistent (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF)
    (lo : w64) (r : RespModel) : Persistent (storeApplyCert (GF := GF) cap E R lo r) := by
  unfold storeApplyCert; infer_instance

/-- Keep a resource while learning a pure fact from it. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (BI.and_intro .rfl h).trans BI.persistent_and_sep_mp

/-- **Borrow the latest tree** from the tree invariant, with the write lock's half of `γ.tree`
(`some m`, the lock invariant's latest map): the tree holding `m` (under a later, stripped by the
next program step), and the half at `none` (the tree is lent). -/
theorem storeTree_borrow (s : Loc) (γ : StoreNames) (m : KvMap) :
    inv storeTreeN (storeTreeInv (hG := hG) s γ) ∗ ghostVar γ.tree (1 : Qp).half (some m) ⊢
      |={⊤}=> ▷ storeLatestTree s m ∗ ghostVar γ.tree (1 : Qp).half (none : Option KvMap) := by
  iintro ⟨#Hinv, Hgv⟩
  iinv Hinv with Hi Hclose
  unfold storeTreeInv
  icases Hi with ⟨%o, >Hgv', Ho⟩
  icombine Hgv Hgv' gives % ⟨-, Heq⟩
  subst Heq
  imod ghostVar_update_halves (none : Option KvMap) γ.tree (some m) (some m) $$ Hgv Hgv'
    with ⟨Hgv, Hgv'⟩
  imod Hclose $$ [Hgv'] with -
  · inext
    iexists none
    iframe Hgv'
  imodintro
  iframe Hgv
  iexact Ho

/-- **Give the latest tree back**, now holding `m`: the write lock's half of `γ.tree` is again
`some m`. -/
theorem storeTree_return (s : Loc) (γ : StoreNames) (m : KvMap) :
    inv storeTreeN (storeTreeInv (hG := hG) s γ) ∗ ghostVar γ.tree (1 : Qp).half (none : Option KvMap) ∗
      storeLatestTree s m ⊢
      |={⊤}=> ghostVar γ.tree (1 : Qp).half (some m) := by
  iintro ⟨#Hinv, Hgv, Ht⟩
  iinv Hinv with Hi Hclose
  unfold storeTreeInv
  icases Hi with ⟨%o, >Hgv', -⟩
  icombine Hgv Hgv' gives % ⟨-, Heq⟩
  subst Heq
  imod ghostVar_update_halves (some m) γ.tree none none $$ Hgv Hgv' with ⟨Hgv, Hgv'⟩
  imod Hclose $$ [Hgv' Ht] with -
  · inext
    iexists some m
    iframe Hgv' Ht
  imodintro
  iexact Hgv

/-- A watch event `ev` (a `*mvccpb.Event`) modelled by `e`: the fields the store reads,
read-only (`Type`, `Kv`, and the `KeyValue`'s `Key` and `ModRevision`; on the fields, as
`kvAt`). -/
def eventAt (ev : Loc) (e : EvModel) : IProp GF :=
  iprop(∃ keySl : GoSlice,
    structFieldRef mvccpb.Event go!"Type" ev ↦□ e.typ ∗
    structFieldRef mvccpb.Event go!"Kv" ev ↦□ e.kv ∗
    structFieldRef mvccpb.KeyValue go!"Key" e.kv ↦□ keySl ∗ keySl ↦*□ e.key ∗
    structFieldRef mvccpb.KeyValue go!"ModRevision" e.kv ↦□ e.rev)

instance eventAt_persistent (ev : Loc) (e : EvModel) : Persistent (eventAt (GF := GF) ev e) := by
  unfold eventAt; infer_instance

/-- The slice `sl` of `*mvccpb.Event` (read-only) holds events modelled by `evs`. -/
def eventsAt (sl : GoSlice) (evs : List EvModel) : IProp GF :=
  iprop(∃ ls : List Loc, sl ↦*□ ls ∗ ⌜ls.length = evs.length⌝ ∗
    □ (∀ (i : Nat) (ev : Loc) (e : EvModel), ⌜ls[i]? = some ev⌝ -∗ ⌜evs[i]? = some e⌝ -∗
      eventAt ev e))

instance eventsAt_persistent (sl : GoSlice) (evs : List EvModel) :
    Persistent (eventsAt (GF := GF) sl evs) := by
  unfold eventsAt; infer_instance

/-- A response header pointer `h` with revision `rev` (`h.GetRevision()`): nil with
`rev = 0`, or a non-nil `*ResponseHeader` whose `Revision` field is `rev`, read-only (on
the field, as `kvAt`). -/
def hdrAt (h : Loc) (rev : w64) : IProp GF :=
  iprop(⌜h = null ∧ rev = W64 0⌝ ∨
    (⌜h ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev))

instance hdrAt_persistent (h : Loc) (rev : w64) : Persistent (hdrAt (GF := GF) h rev) := by
  unfold hdrAt; infer_instance

/-- The `go_etcd_io.etcd.client.v3.WatchResponse` value `resp` is modelled by `r` (read-only). -/
def respAt (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop(eventsAt resp.Events' r.events ∗ hdrAt resp.Header' r.hdrRev ∗
    ⌜resp.CompactRevision' = r.compactRev ∧ resp.Canceled' = r.canceled ∧
      resp.Created' = r.created⌝)

instance respAt_persistent (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (respAt (GF := GF) resp r) := by
  unfold respAt; infer_instance

/-- The error `getSnapshot` (and `Get`) returns for result `res`: `nil` for a snapshot,
the value of the package variable `ErrNotReady`, `rpctypes.ErrFutureRev` or
`rpctypes.ErrCompacted` (`Base.lean`), or some non-nil error (`fmt.Errorf`) for an invalid
revision. -/
def snapErr (res : SnapResult) (err : GoInterface) : IProp GF :=
  match res with
  | .ok _ _ => iprop(⌜err = GoInterface.nil⌝)
  | .notReady => iprop(globalAddr ErrNotReady ↦□ err)
  | .invalid => iprop(⌜∃ e, err = GoInterface.ok e⌝)
  | .future => iprop(globalAddr v3rpc.rpctypes.ErrFutureRev ↦□ err)
  | .compacted => iprop(globalAddr v3rpc.rpctypes.ErrCompacted ↦□ err)

instance snapErr_persistent (res : SnapResult) (err : GoInterface) :
    Persistent (snapErr (GF := GF) res err) := by
  cases res <;> unfold snapErr <;> infer_instance

/-- What a reader learns about the store: some state `st` it was in, satisfying
`StoreInv`, whose latest revision is at least the reader's lower bound `r0`, with a lower
bound for it. -/
def storeSeen (γ : StoreNames) (cap : Nat) (r0 : w64) (st : StoreState) : IProp GF :=
  iprop(⌜StoreInv cap st ∧ sint.Z r0 ≤ sint.Z st.latestRev⌝ ∗ storeRevLb γ st.latestRev)

instance storeSeen_persistent (γ : StoreNames) (cap : Nat) (r0 : w64) (st : StoreState) :
    Persistent (storeSeen (GF := GF) γ cap r0 st) := by
  unfold storeSeen; infer_instance

/-- The package-level error variables (the cache's `ErrNotReady`, `rpctypes`'
`ErrFutureRev`, `ErrCompacted`) hold fixed non-nil errors: `Base.lean`'s package facts. -/
theorem errNotReady_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ⊢
      ∃ e : GoInterfaceOk, globalAddr ErrNotReady ↦□ GoInterface.ok e := by
  iintro #H
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ H
  icases Hci with ⟨H, -, -, -⟩
  iexact H

end defs

end EtcdGrove
end Perennial
