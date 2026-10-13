/-
The watchable store (`watchable_store.go`, `watchable_store_txn.go`): its lock invariant, the
stream channels' protocol and the watchers' ghost state. Lean-first; `notes/decisions.md`, "The
watchable store's concurrency (unit 3)".

**The model** (pure). The events the watchers see of a revision `r` (`evsOfRevM`) are the
key-values its changes wrote (`changeKv`), made events as `End` does (`evOfKv`: a create
revision `0`, the key alone of a delete, is a `DELETE` at mod revision `r`); `watchEvents log r lo
hi` are the events of the revisions `[lo, hi)` of `log` whose key the range `r` holds, in
revision order; `filtered fs evs` keeps the events no filter predicate of `fs` drops.

**The history determines what a watcher was sent.** A watcher's events are stated over a log
`L` known by a lower bound of the index's history (`monoListLbOwn γ.idx.hist (histOf L)`,
`evsWf`): `histOf` determines the log (`histOf_prefix_log`), and two lower bounds are
comparable, so every such statement is about the one log, without any lock. The writer seals
its pending revision before it notifies (`idxWriter_seal`), so a revision's events go on the
channels with the lower bound of the log that commits it.

**Per watcher** (`WatcherNames`, tied to its pointer by `watcherMeta`, a persistent element of
the store's ghost map `γ.wmeta`): `evs`, a monotone list of the events delivered (the batches,
unfiltered); `live`, a `dghostVar` `true` while the watcher is registered and not cancelled (half
the channel invariant's, the rest the lock invariant's: a sender proves the channel open with
it); the channel's names and the first revision `lo` the watcher watches from.

**Per channel** (`watchChanInv`, `inv watchN`, the cache's `InvWatcher` as template): the channel,
the log of every response sent (`RespM`, with the watcher sent for as ghost data), the consumer's
received prefix (half of `recv`, the other half the consumer's: `watchConsumer`), the values in
flight, the list of registered watchers (half of `regl`, the other half the stream's close right
`CR`, which the close deposits; every response sent is for one of them) and, per registered watcher, its deliveries: the segments of its delivered events, each
filtered by some predicate its filters implement (sent unless all its events were filtered
out), and whether it is live (an open channel) or cancelled (a closed channel has no live
watcher).

**The lock invariant** (`watchStoreInv s st γ q`, the resource of `s.mu`, at the fraction `q`
of the read side): the notified log `Lmu` (its certificate; half of `γ.wlog`, whose other half
is the sole writer's, `watchWriter`), the two groups, the victim batches, every watcher's state
(the cancelled ones included: `cancelWatcher` reads `wa.ch`) and half of the states of the
victims out with the mover, the meta map's authority with the watcher budget (`watchBudget`:
the watchers with names and the unspent watch tokens below `2 ^ 63 - 3`), and per live watcher
its ghosts and the facts of its population (`memberRes`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The watchers' events of the log (pure) -/

/-- The event `End` makes of a change's key-value at revision `r`: a create revision `0` (the
key alone, a delete's `changeKv`) is a `DELETE` with `ModRevision := r`, else a `PUT`; no
previous key-value. -/
def evOfKv (r : Nat) (kv : EtcdKv) : EvM :=
  if kv.createRev = W64 0 then ⟨true, { kv with modRev := W64 r }, none⟩ else ⟨false, kv, none⟩

/-- The events of revision `r` (changes `cs`, the state `before` before them), in order. -/
def evsOfRevM (r : Nat) (before : List EtcdKv) (cs : List Change) : List EvM :=
  (List.range cs.length).filterMap fun i => (changeKv (W64 r) before cs i).map (evOfKv r)

/-- The events of the revisions `[lo, hi)` of `log`, in revision order. -/
def logEvents (log : Log) (lo hi : Nat) : List EvM :=
  ((List.range' lo (hi - lo)).map fun m =>
    evsOfRevM m (stateAt log (m - 1)) (log.getD m [])).flatten

/-- The range's events of `log` at the revisions `[lo, hi)`, in revision order. -/
def watchEvents (log : Log) (r : WatchRange) (lo hi : Nat) : List EvM :=
  (logEvents log lo hi).filter fun ev => r.covers ev.kv.key

/-- The events no filter predicate of `fs` drops (`watcher.send`'s loop). -/
def filtered (fs : List (EvM → Bool)) (evs : List EvM) : List EvM :=
  evs.filter fun ev => fs.all fun p => !(p ev)

theorem filtered_nil (fs : List (EvM → Bool)) : filtered fs [] = [] := rfl

theorem filtered_append (fs : List (EvM → Bool)) (a b : List EvM) :
    filtered fs (a ++ b) = filtered fs a ++ filtered fs b := by
  unfold filtered; rw [List.filter_append]

theorem logEvents_empty (log : Log) {lo hi : Nat} (h : hi ≤ lo) : logEvents log lo hi = [] := by
  unfold logEvents; rw [show hi - lo = 0 by omega]; rfl

theorem watchEvents_empty (log : Log) (r : WatchRange) {lo hi : Nat} (h : hi ≤ lo) :
    watchEvents log r lo hi = [] := by
  unfold watchEvents; rw [logEvents_empty log h]; rfl

theorem logEvents_append (log : Log) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    logEvents log lo hi = logEvents log lo mid ++ logEvents log mid hi := by
  unfold logEvents
  rw [← List.flatten_append, ← List.map_append]
  congr 2
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, ← List.range'_append_1,
    show lo + (mid - lo) = mid by omega]

theorem watchEvents_append (log : Log) (r : WatchRange) {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    watchEvents log r lo hi = watchEvents log r lo mid ++ watchEvents log r mid hi := by
  unfold watchEvents; rw [logEvents_append log h1 h2, List.filter_append]

theorem logEvents_succ (log : Log) (m : Nat) :
    logEvents log m (m + 1) = evsOfRevM m (stateAt log (m - 1)) (log.getD m []) := by
  unfold logEvents
  rw [show m + 1 - m = 1 by omega]
  simp

/-- The events of a log at revisions below a prefix's length are the prefix's. -/
theorem logEvents_prefix {L L' : Log} (hp : L <+: L') {lo hi : Nat} (hhi : hi ≤ L.length) :
    logEvents L lo hi = logEvents L' lo hi := by
  unfold logEvents
  congr 1
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range'] at hm
  have hm' : m < L.length := by omega
  obtain ⟨T, rfl⟩ := hp
  have hs : stateAt (L ++ T) (m - 1) = stateAt L (m - 1) := by
    unfold stateAt
    rw [List.take_append_of_le_length (by omega)]
  rw [hs]
  congr 1
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hm']

theorem watchEvents_prefix {L L' : Log} (hp : L <+: L') (r : WatchRange) {lo hi : Nat}
    (hhi : hi ≤ L.length) : watchEvents L r lo hi = watchEvents L' r lo hi := by
  unfold watchEvents; rw [logEvents_prefix hp hhi]

/-- Two comparable logs agree on the events of the revisions both have. -/
theorem watchEvents_cmp {L L' : Log} (hc : L <+: L' ∨ L' <+: L) (r : WatchRange) {lo hi : Nat}
    (h : hi ≤ L.length ∨ hi ≤ lo) (h' : hi ≤ L'.length ∨ hi ≤ lo) :
    watchEvents L r lo hi = watchEvents L' r lo hi := by
  by_cases hlo : hi ≤ lo
  · rw [watchEvents_empty _ _ hlo, watchEvents_empty _ _ hlo]
  · have h1 : hi ≤ L.length := h.resolve_right hlo
    have h2 : hi ≤ L'.length := h'.resolve_right hlo
    rcases hc with hc | hc
    · exact watchEvents_prefix hc r h1
    · exact (watchEvents_prefix hc r h2).symm

/-! ## Countability (for the ghost state) -/

instance etcdKvCountableW : Pos.Countable EtcdKv :=
  .ofInjective (fun k => Pos.Countable.encode (k.key, k.createRev, k.modRev, k.version, k.value, k.lease))
    (by rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h; have h := Pos.encode_inj h; simp_all)

instance EvM.countable : Pos.Countable EvM :=
  .ofInjective (fun e => Pos.Countable.encode (e.del, e.kv, e.prevKv))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- A response the store sent on a stream's channel: the watcher it was sent for (ghost), its
`WatchID`, events and `Revision`. -/
structure RespM where
  w : Loc
  id : w64
  evs : List EvM
  rev : w64

instance RespM.countable : Pos.Countable RespM :=
  .ofInjective (fun r => Pos.Countable.encode (r.w, r.id, r.evs, r.rev))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

instance watchResponseCountable [FfiSyntax] : Pos.Countable WatchResponse :=
  .ofInjective (fun r => Pos.Countable.encode (r.WatchID', r.Events', r.Revision', r.CompactRevision'))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The ghost names of a stream's channel: the channel's, the consumer's received responses
(`ghostVar (List RespM)`), the registered watchers (`ghostVar (List Loc)`, half the close
right's) and their set (a ghost map with persistent elements: `chanReg`). -/
structure WatchChanNames where
  ch : ChanNames
  recv : GName
  regl : GName
  reg : GName

/-- A watcher's ghost names (see the module docstring); `lo` is the first revision it watches. -/
structure WatcherNames where
  evs : GName
  live : GName
  wc : WatchChanNames
  lo : Nat

instance WatcherNames.countable : Pos.Countable WatcherNames :=
  .ofInjective (fun g => Pos.Countable.encode (g.evs, g.live, g.wc.ch.stateName, g.wc.ch.offerLockName,
      g.wc.ch.offerParkedPropName, g.wc.ch.offerParkedPredName, g.wc.ch.offerContinuationName,
      g.wc.ch.chanCap, g.wc.recv, g.wc.regl, g.wc.reg, g.lo))
    (by
      rintro ⟨a, b, ⟨⟨c1, c2, c3, c4, c5, c6⟩, d, e, f⟩, g⟩ ⟨a', b', ⟨⟨c1', c2', c3', c4', c5', c6'⟩, d', e', f'⟩, g'⟩ h
      have h := Pos.encode_inj h
      simp_all)

/-- The watchable store's ghost names: the store's, the watchers' names (`wmeta`: a ghost map
from a watcher to its names, persistent elements), the notified log (`wlog`: half the lock
invariant's, half the sole writer's), and the lock invariant's state (`wst`: `ghostVar
WsState`, at the lock's fraction, so that two parts of the invariant agree on it). -/
structure WsNames where
  st : StoreNames
  wmeta : GName
  wlog : GName
  wst : GName
  /-- the watcher budget (`watchBudget`): a registration costs one token (`watchTok`) -/
  wt : GName

/-! ## Channel states (as the cache's `InvWatcher`) -/

/-- The values a channel in state `s` holds in flight (none for a blocking send's states, which
the store never does). -/
def chanInflight {V : Type} : ChanState V → Option (List V)
  | .Buffered b => some b
  | .Closed b => some b
  | .Idle => some []
  | .RcvPending => some []
  | .SndCommit v => some [v]
  | .SndPending _ => none
  | .RcvCommit => none

/-- The channel state `s` is closed. -/
def chanIsClosed {V : Type} : ChanState V → Bool
  | .Closed _ => true
  | _ => false

/-- A delivery of a watcher's events: the events it covers (unfiltered) and those kept. -/
abbrev Deliv := List EvM × List EvM

/-- A delivery is sent (as a response) unless all its events, not none, were filtered out
(`watcher.send`'s `!progressEvent && len(wr.Events) == 0`). -/
def Deliv.sent (d : Deliv) : Bool := d.1.isEmpty || !d.2.isEmpty

/-- The set of a list's elements, as a ghost map. -/
def regMap (L : List Loc) : GMap Loc Unit := L.foldr (fun w m => <[w := ()]> m) ∅

theorem regMap_lookup (L : List Loc) (w : Loc) : (regMap L !! w).isSome ↔ w ∈ L := by
  induction L with
  | nil => simp [regMap, GMap.lookup_empty]
  | cons x xs ih =>
    show ((<[x := ()]> (regMap xs)) !! w).isSome ↔ w ∈ x :: xs
    by_cases h : w = x
    · subst h; simp [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), ih]; simp [h]

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the watchable store's own `mu`. -/
abbrev wsMuAddr (s : Loc) : Loc := structFieldRef watchableStore go!"mu" s
/-- The address of the synced group. -/
abbrev syncedAddr (s : Loc) : Loc := structFieldRef watchableStore go!"synced" s
/-- The address of the unsynced group. -/
abbrev unsyncedAddr (s : Loc) : Loc := structFieldRef watchableStore go!"unsynced" s
/-- The address of the victims slice. -/
abbrev victimsAddr (s : Loc) : Loc := structFieldRef watchableStore go!"victims" s

end addrs

/-- The channel invariants' namespace. -/
def watchN : Namespace := nroot.@"mvccwatch"

/-! ## The store's state record -/

/-- The lock invariant's abstract state: the notified log; the synced and unsynced members
(with their ranges); the states of the watchers under the lock (live and cancelled) and of the
victims out with the mover; every watcher's names; per live watcher, its delivered events and
delivery bound; the victims slice, its batch maps and their models. -/
structure WsState where
  Lmu : Log
  Ws : GMap Loc WatchRange
  Wu : GMap Loc WatchRange
  ST : GMap Loc WatcherSt
  Wo : GMap Loc WatcherSt
  M : GMap Loc WatcherNames
  E : GMap Loc (List EvM × Nat)
  vs : GoSlice
  vbs : List GoMap
  VB : List (GMap Loc EventBatch)

instance WatchRange.countable : Pos.Countable WatchRange :=
  .ofInjective (fun r => Pos.Countable.encode (r.key, r.end?, r.startRev, r.id))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

instance WatcherSt.countable : Pos.Countable WatcherSt :=
  .ofInjective (fun r => Pos.Countable.encode (r.minRev, r.victim, r.compacted, r.restore, r.ch))
    (by rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h; have h := Pos.encode_inj h; simp_all)

instance EventBatch.countable : Pos.Countable EventBatch :=
  .ofInjective (fun r => Pos.Countable.encode (r.evs, r.revs, r.moreRev))
    (by rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h; have h := Pos.encode_inj h; simp_all)

instance WsState.countable : Pos.Countable WsState :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.Lmu, σ.Ws, σ.Wu, σ.ST, σ.Wo, σ.M, σ.E, σ.vs, σ.vbs, σ.VB))
    (by
      rintro ⟨a, b, c, d, e, f, g, h, i, j⟩ ⟨a', b', c', d', e', f', g', h', i', j'⟩ hh
      have hh := Pos.encode_inj hh
      simp_all)

/-- The victim batch of `w`, if any. -/
def WsState.victimOf (σ : WsState) (w : Loc) : Option EventBatch := σ.VB.findSome? (· !! w)

/-- `w` is a live watcher under the lock: synced, unsynced or a victim. -/
def WsState.live (σ : WsState) (w : Loc) : Prop :=
  (σ.Ws !! w).isSome ∨ (σ.Wu !! w).isSome ∨ (σ.victimOf w).isSome

instance (σ : WsState) (w : Loc) : Decidable (σ.live w) := by unfold WsState.live; infer_instance

/-- The pure facts of the state: the populations are disjoint (a victim in one batch), the
live watchers have states, events and names, every watcher with names has a state (under the
lock or out), the states' flags are what the populations say, the victims out are flagged
victims with a channel, and a synced watcher is delivered at least up to the notified log and
its first revision. -/
structure WsOk (σ : WsState) : Prop where
  ws_wu : ∀ w, (σ.Ws !! w).isSome → σ.Wu !! w = none
  ws_v : ∀ w, (σ.Ws !! w).isSome → σ.victimOf w = none
  wu_v : ∀ w, (σ.Wu !! w).isSome → σ.victimOf w = none
  v_one : ∀ (i j : Nat) (B B' : GMap Loc EventBatch) (w : Loc), σ.VB[i]? = some B →
    σ.VB[j]? = some B' → (B !! w).isSome → (B' !! w).isSome → i = j
  live_st : ∀ w, σ.live w → (σ.ST !! w).isSome
  live_e : ∀ w, (σ.E !! w).isSome ↔ σ.live w
  st_m : ∀ w, (σ.ST !! w).isSome → (σ.M !! w).isSome
  wo_m : ∀ w, (σ.Wo !! w).isSome → (σ.M !! w).isSome
  m_st : ∀ w, (σ.M !! w).isSome → (σ.ST !! w).isSome ∨ (σ.Wo !! w).isSome
  wo_st : ∀ w, (σ.Wo !! w).isSome → σ.ST !! w = none
  wo_live : ∀ w, (σ.Wo !! w).isSome → ¬ σ.live w
  st_flags : ∀ w st, σ.ST !! w = some st →
    st.compacted = false ∧ st.restore = false ∧
    (σ.live w → (st.victim = true ↔ (σ.victimOf w).isSome)) ∧ (st.ch = null ↔ ¬ σ.live w)
  wo_flags : ∀ w st, σ.Wo !! w = some st →
    st.compacted = false ∧ st.restore = false ∧ st.victim = true ∧ st.ch ≠ null
  synced_d : ∀ w γw ed, (σ.Ws !! w).isSome → σ.M !! w = some γw → σ.E !! w = some ed →
    max γw.lo σ.Lmu.length ≤ ed.2

/-- Every synced watcher is delivered at most up to `N`, or to its first revision (what the
sole writer's history says, before it seals: `End`). -/
def WsState.syncedBelow (σ : WsState) (N : Nat) : Prop :=
  ∀ w γw ed, (σ.Ws !! w).isSome → σ.M !! w = some γw → σ.E !! w = some ed →
    ed.2 ≤ N ∨ ed.2 ≤ γw.lo

/-- Every synced watcher is delivered at least up to `N` and its first revision. -/
def WsState.syncedAbove (σ : WsState) (N : Nat) : Prop :=
  ∀ w γw ed, (σ.Ws !! w).isSome → σ.M !! w = some γw → σ.E !! w = some ed → max γw.lo N ≤ ed.2

/-- A map whose keys are another's has at most as many entries. -/
theorem gmap_size_le_of_dom {V V' : Type} (m1 : GMap Loc V) (m2 : GMap Loc V')
    (h : ∀ k, (m1 !! k).isSome → (m2 !! k).isSome) : GMap.size m1 ≤ GMap.size m2 := by
  rw [GMap.size_eq_dom_list_length, GMap.size_eq_dom_list_length]
  refine (List.subperm_of_subset (GMap.nodup_dom_list m1) (fun k hk => ?_)).length_le
  rw [GMap.mem_dom_list] at hk ⊢
  exact h k hk

/-- The synced watchers have names. -/
theorem WsOk.ws_size {σ : WsState} (h : WsOk σ) : GMap.size σ.Ws ≤ GMap.size σ.M :=
  gmap_size_le_of_dom _ _ fun w hw => h.st_m w (h.live_st w (Or.inl hw))

/-- The unsynced watchers have names. -/
theorem WsOk.wu_size {σ : WsState} (h : WsOk σ) : GMap.size σ.Wu ≤ GMap.size σ.M :=
  gmap_size_le_of_dom _ _ fun w hw => h.st_m w (h.live_st w (Or.inr (Or.inl hw)))

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## Filters -/

/-- The filter `f` (a `FilterFunc`) decides the predicate `p` on events. -/
def filterSpec (f : GoFunc) (p : EvM → Bool) : IProp GF :=
  iprop(□ ∀ (e : Loc) (ev : EvM),
    {{ evIs e ev }} (App (Val #f) (Val #e)) {{ (b : Bool), RET #b; ⌜b = p ev⌝ }})

instance filterSpec_persistent (f : GoFunc) (p : EvM → Bool) :
    Persistent (filterSpec (GF := GF) f p) := by
  unfold filterSpec; infer_instance

/-- The filters `fcs` (a slice, read-only for good) implement the predicates `fs`. -/
def filtersImpl (fcs : GoSlice) (fs : List (EvM → Bool)) : IProp GF :=
  iprop(∃ fps : List GoFunc, fcs ↦*□ fps ∗ ⌜fps.length = fs.length⌝ ∗
    [∗list] x ∈ fps.zip fs, filterSpec x.1 x.2)

instance filtersImpl_persistent (fcs : GoSlice) (fs : List (EvM → Bool)) :
    Persistent (filtersImpl (GF := GF) fcs fs) := by
  unfold filtersImpl; infer_instance

/-- The filters `fcs` implement some predicates. -/
def filtersOk (fcs : GoSlice) : IProp GF := iprop(∃ fs, filtersImpl fcs fs)

instance filtersOk_persistent (fcs : GoSlice) : Persistent (filtersOk (GF := GF) fcs) := by
  unfold filtersOk; infer_instance

/-! ## Responses -/

/-- The `WatchResponse` value `v` is the response `r`: its id and revision, no compaction, its
events a read-only slice of `r`'s events (`evIs` each). -/
def respIs (v : WatchResponse) (r : RespM) : IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = W64 0⌝ ∗
    ∃ ps : List Loc, v.Events' ↦*□ ps ∗ ⌜ps.length = r.evs.length⌝ ∗
      [∗list] x ∈ ps.zip r.evs, evIs x.1 x.2)

instance respIs_persistent (v : WatchResponse) (r : RespM) : Persistent (respIs (GF := GF) v r) := by
  unfold respIs; infer_instance

/-- The values `vs` are the responses `rs`, pointwise. -/
def respsIs (vs : List WatchResponse) (rs : List RespM) : IProp GF :=
  iprop(⌜vs.length = rs.length⌝ ∗
    □ (∀ (i : Nat) (v : WatchResponse) (r : RespM), ⌜vs[i]? = some v⌝ -∗ ⌜rs[i]? = some r⌝ -∗
      respIs v r))

instance respsIs_persistent (vs : List WatchResponse) (rs : List RespM) :
    Persistent (respsIs (GF := GF) vs rs) := by
  unfold respsIs; infer_instance

/-- What a response says, for good: its revision is at or above its events', and a response
with events carries its watcher's id. -/
def respOk (r : RespM) : IProp GF :=
  iprop(⌜∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev⌝ ∗
    ∃ (rr : WatchRange) (fcs : GoSlice), watcherFixed r.w rr fcs ∗ ⌜r.evs ≠ [] → r.id = rr.id⌝)

instance respOk_persistent (r : RespM) : Persistent (respOk (GF := GF) r) := by
  unfold respOk; infer_instance

/-! ## Per watcher -/

/-- The watcher `w`'s ghost names (persistent). -/
def watcherMeta (γ : WsNames) (w : Loc) (γw : WatcherNames) : IProp GF :=
  ghostMapElem γ.wmeta w DFrac.discard γw

instance watcherMeta_persistent (γ : WsNames) (w : Loc) (γw : WatcherNames) :
    Persistent (watcherMeta (GF := GF) γ w γw) := by
  unfold watcherMeta; infer_instance

/-- The watcher was cancelled (persistent). -/
def cancelled (γw : WatcherNames) : IProp GF := dghostVar γw.live DFrac.discard false

instance cancelled_persistent (γw : WatcherNames) : Persistent (cancelled (GF := GF) γw) := by
  unfold cancelled; infer_instance

/-- The events `evs` are the range's of the revisions `[lo, d)` of a log the index's history
has (persistent; `d` past the log only for an empty range). -/
def evsWf (γ : WsNames) (r : WatchRange) (lo : Nat) (evs : List EvM) (d : Nat) : IProp GF :=
  iprop(∃ L : Log, monoListLbOwn γ.st.idx.hist (histOf L) ∗
    ⌜evs = watchEvents L r lo d ∧ (d ≤ L.length ∨ d ≤ lo)⌝)

instance evsWf_persistent (γ : WsNames) (r : WatchRange) (lo : Nat) (evs : List EvM) (d : Nat) :
    Persistent (evsWf (GF := GF) γ r lo evs d) := by
  unfold evsWf; infer_instance

/-- Every prefix of the deliveries `D` ends at a revision (persistent): its events, concatenated,
are the range's of the revisions `[lo, d')` of a log the index's history has, for some `d'` (a
delivery is the events of whole revisions: `notify` sends one revision's, `syncWatchers` those
of `[minRev, maxRev)` or up to `moreRev`), so a client that received a prefix of the deliveries
knows up to which revision it has every event. -/
def delivsCut (γ : WsNames) (r : WatchRange) (lo : Nat) (D : List Deliv) : IProp GF :=
  iprop(□ ∀ k : Nat, ⌜k ≤ D.length⌝ -∗
    ∃ d' : Nat, evsWf γ r lo ((D.take k).map Prod.fst).flatten d')

instance delivsCut_persistent (γ : WsNames) (r : WatchRange) (lo : Nat) (D : List Deliv) :
    Persistent (delivsCut (GF := GF) γ r lo D) := by
  unfold delivsCut; infer_instance

/-- A registered watcher's part of its channel's invariant (`closed`: the channel's state is
closed; `sent`: the responses sent on it): half its delivered events, its deliveries (their
events, in order, are the delivered ones; the sent ones are the responses sent for it, in
order; each filtered by predicates its filters implement; each prefix of them ending at a
revision, `delivsCut`), what they are of the log, and its live half, or cancelled (a closed
channel has no live watcher). -/
def chanWatcher (γ : WsNames) (γc : WatchChanNames) (closed : Bool) (sent : List RespM)
    (w : Loc) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (evsw : List EvM)
      (D : List Deliv) (d : Nat),
    watcherMeta γ w γw ∗ ⌜γw.wc = γc⌝ ∗ watcherFixed w r fcs ∗
    monoListAuthOwn γw.evs (1 : Qp).half evsw ∗
    ⌜(D.map Prod.fst).flatten = evsw ∧
      (sent.filter (fun x => decide (x.w = w))).map RespM.evs = (D.filter Deliv.sent).map Prod.snd⌝ ∗
    □ (([∗list] dl ∈ D, ∃ fs, filtersImpl fcs fs ∗ ⌜dl.2 = filtered fs dl.1⌝) ∗
      delivsCut γ r γw.lo D) ∗
    evsWf γ r γw.lo evsw d ∗
    ((⌜closed = false⌝ ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true) ∨ cancelled γw))

/-- **The stream channel `ch`'s invariant** (see the module docstring). -/
def watchChanInv (γ : WsNames) (ch : Loc) (γc : WatchChanNames) : IProp GF :=
  iprop(∃ (s : ChanState WatchResponse) (sent recv : List RespM) (vs : List WatchResponse)
      (L : List Loc),
    "Hch" ∷ ownChan γc.ch WatchResponse s ∗
    "Hrecv" ∷ ghostVar γc.recv (1 : Qp).half recv ∗
    "%Hpre" ∷ ⌜recv <+: sent⌝ ∗
    "%Hinfl" ∷ ⌜chanInflight s = some vs⌝ ∗
    "#Hvs" ∷ respsIs vs (sent.drop recv.length) ∗
    "#Hok" ∷ □ ([∗list] r ∈ sent, respOk r) ∗
    "Hregl" ∷ ghostVar γc.regl (1 : Qp).half L ∗
    "Hcl" ∷ (if chanIsClosed s then ghostVar γc.regl (1 : Qp).half L else iprop(True)) ∗
    "Hreg" ∷ ghostMapAuth γc.reg 1 (regMap L) ∗
    "%Hnd" ∷ ⌜L.Nodup ∧ ∀ x ∈ sent, x.w ∈ L⌝ ∗
    "Hws" ∷ [∗list] w ∈ L, chanWatcher γ γc (chanIsClosed s) sent w)

/-- The consumer's view: it has received `received`. -/
def watchConsumer (γc : WatchChanNames) (received : List RespM) : IProp GF :=
  ghostVar γc.recv (1 : Qp).half received

/-- The watcher `w` (names `γw`) is registered on the channel `ch` (persistent): the channel, its
invariant, and `w` in its set of registered watchers. -/
def watcherChan (γ : WsNames) (w : Loc) (γw : WatcherNames) (ch : Loc) : IProp GF :=
  iprop(isChan ch γw.wc.ch WatchResponse ∗ inv watchN (watchChanInv γ ch γw.wc) ∗
    ghostMapElem γw.wc.reg w DFrac.discard ())

instance watcherChan_persistent (γ : WsNames) (w : Loc) (γw : WatcherNames) (ch : Loc) :
    Persistent (watcherChan (GF := GF) γ w γw ch) := by
  unfold watcherChan; infer_instance

/-! ## The lock invariant -/

/-- What the lock knows of a victim's batch `B` (the watcher's first revision `lo`, its state
`st`): the first revision the batch left out, if any, is the watcher's `minRev` (`syncWatchers`
sets it so), and its events are at or above `lo` and below `minRev` (the victims' loop resends
them as of `minRev - 1`). -/
def victimBatchOk (lo : Nat) (st : WatcherSt) (B : EventBatch) : Prop :=
  (B.moreRev ≠ W64 0 → B.moreRev = st.minRev) ∧
  ∀ ev ∈ B.evs, (lo : Int) ≤ sint.Z ev.kv.modRev ∧ sint.Z ev.kv.modRev < sint.Z st.minRev

/-- What the lock knows of a live watcher's population: a synced one is delivered up to `d`, at
or past its `minRev` (and the notified log: `WsOk.synced_d`); an unsynced one up to its
`minRev`, at most the last revision of a committed log; a victim's batch completes its delivered
events up to its `minRev` (`victimBatchOk`). -/
def popFacts (γ : WsNames) (σ : WsState) (w : Loc) (r : WatchRange) (lo : Nat) (st : WatcherSt)
    (evsw : List EvM) (d : Nat) : IProp GF :=
  if (σ.Ws !! w).isSome then
    iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ d⌝ ∗ evsWf γ r lo evsw d)
  else if (σ.Wu !! w).isSome then
    iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev⌝ ∗ evsWf γ r lo evsw d ∗
      ∃ Lc : Log, idxCert γ.st.idx Lc ∗ ⌜sint.Z st.minRev < Lc.length⌝)
  else match σ.victimOf w with
    | some B => iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev ∧
          victimBatchOk lo st B⌝ ∗
        evsWf γ r lo (evsw ++ B.evs) d)
    | none => iprop(True)

instance popFacts_persistent (γ : WsNames) (σ : WsState) (w : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) :
    Persistent (popFacts (GF := GF) γ σ w r lo st evsw d) := by
  unfold popFacts
  split
  · infer_instance
  · split
    · infer_instance
    · split <;> infer_instance

/-- A watcher under the lock (at its fraction `q`): its names and fixed fields; live, its
channel, filters, its start revision at or below its first revision `lo`, the lock's parts of its ghosts and its population's facts; else cancelled. -/
def memberRes (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
    if σ.live w then
      watcherChan γ w γw st.ch ∗ filtersOk fcs ∗ ⌜sint.Z r.startRev ≤ (γw.lo : Int)⌝ ∗
      ∃ (evsw : List EvM) (d : Nat), ⌜σ.E !! w = some (evsw, d)⌝ ∗
        monoListAuthOwn γw.evs q.half evsw ∗ dghostVar γw.live (DFrac.own q.half) true ∗
        popFacts γ σ w r γw.lo st evsw d
    else cancelled γw)

/-- A victim out with the mover (the lock's half of its state; persistent facts). -/
def outRes (γ : WsNames) (σ : WsState) (w : Loc) (st : WatcherSt) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs)

instance outRes_persistent (γ : WsNames) (σ : WsState) (w : Loc) (st : WatcherSt) :
    Persistent (outRes (GF := GF) γ σ w st) := by
  unfold outRes; infer_instance

/-- A watch token: the right to register one watcher (`watch`, the stream's `Watch`). `New` hands
out `2 ^ 63 - 3` of them: with the budget the lock keeps (`watchBudget`), the watchers with
names stay below `2 ^ 63 - 3`, so a watcher group's interval tree never reaches `2 ^ 63 - 1`
entries (`intervalTree.Insert`'s bound: the tree's count must not wrap). -/
def watchTok (γ : WsNames) : IProp GF := ownToks γ.wt 1

/-- `k` watch tokens. -/
def watchToks (γ : WsNames) (k : Nat) : IProp GF := ownToks γ.wt k

/-- The watcher budget at the fraction `q`, for the watchers with names `M` (every registered
watcher, cancelled or not: `M` only grows): the unspent tokens `n` (the authority's count), with
`M.size + n + 3 ≤ 2 ^ 63`. A registration spends a token and names a watcher; a cancel refunds
nothing. -/
def watchBudget (γ : WsNames) (q : Qp) (M : GMap Loc WatcherNames) : IProp GF :=
  iprop(∃ n : Nat, ownTokAuthDfrac γ.wt (DFrac.own q) n ∗ ⌜GMap.size M + n + 3 ≤ 2 ^ 63⌝)

/-- The budget's bound on the watchers with names. -/
theorem watchBudget_bound (γ : WsNames) (q : Qp) (M : GMap Loc WatcherNames) :
    watchBudget (GF := GF) γ q M ⊢ watchBudget γ q M ∗ ⌜GMap.size M + 3 ≤ 2 ^ 63⌝ := by
  unfold watchBudget
  iintro ⟨%n, Ha, %hb⟩
  isplitl [Ha]
  · iexists n; iframe Ha; ipureintro; exact hb
  ipureintro; omega

/-- **A registration spends a token**: the budget of the watchers with names `M` and a watch
token make the budget of `M` with one more watcher named. -/
theorem watchBudget_spend (γ : WsNames) (M : GMap Loc WatcherNames) (w : Loc)
    (γw : WatcherNames) (hM : M !! w = none) :
    watchBudget (GF := GF) γ 1 M ∗ watchTok γ ⊢ |==> watchBudget γ 1 (<[w := γw]> M) := by
  unfold watchBudget
  iintro ⟨⟨%n, Ha, %hb⟩, Ht⟩
  iunfold watchTok at Ht
  icombine Ha Ht gives %hn
  imod (ownTokAuth_sub 1 γ.wt n) $$ Ha Ht with Ha
  imodintro
  iexists n - 1
  iframe Ha
  ipureintro
  rw [GMap.map_size_insert_None _ _ _ hM]; omega

/-- The lock invariant at the state `σ` and the fraction `q`. -/
def watchStoreBody (s : Loc) (γ : WsNames) (q : Qp) (σ : WsState) : IProp GF :=
  iprop("Hσ" ∷ ghostVar γ.wst q σ ∗
    "Hwlog" ∷ ghostVar γ.wlog q.half σ.Lmu ∗
    "#Hcert" ∷ idxCert γ.st.idx σ.Lmu ∗
    "Hsynced" ∷ ownWatcherGroup (syncedAddr s) σ.Ws q ∗
    "Hunsynced" ∷ ownWatcherGroup (unsyncedAddr s) σ.Wu q ∗
    "Hvf" ∷ typedPointsto (victimsAddr s) σ.vs (DFrac.own q) ∗
    "Hvs" ∷ ownSlice σ.vs σ.vbs (DFrac.own q) ∗
    "Hvcap" ∷ ownSliceCap GoMap σ.vs (DFrac.own q) ∗
    "%Hvlen" ∷ ⌜σ.vbs.length = σ.VB.length⌝ ∗
    "Hvbs" ∷ ([∗list] x ∈ σ.vbs.zip σ.VB, ownWatcherBatch x.1 x.2 q) ∗
    "Hst" ∷ ([∗map] w ↦ st ∈ σ.ST, watcherOwn w st q) ∗
    "Hwo" ∷ ([∗map] w ↦ st ∈ σ.Wo, watcherOwn w st q.half) ∗
    "Hmeta" ∷ ghostMapAuth γ.wmeta q σ.M ∗
    "Hwt" ∷ watchBudget γ q σ.M ∗
    "#Hmfix" ∷ ([∗map] w ↦ _γw ∈ σ.M, ∃ (r : WatchRange) (fcs : GoSlice), watcherFixed w r fcs) ∗
    "Hmem" ∷ ([∗map] w ↦ st ∈ σ.ST, memberRes γ q σ w st) ∗
    "#Hout" ∷ ([∗map] w ↦ st ∈ σ.Wo, outRes γ σ w st) ∗
    "%Hok" ∷ ⌜WsOk σ⌝)

/-- **The lock invariant** of `s.mu` (see the module docstring). -/
def watchStoreInv (s : Loc) (γ : WsNames) (q : Qp) : IProp GF :=
  iprop(∃ σ : WsState, watchStoreBody s γ q σ)

/-! ## The store -/

/-- The reader slots a caller lends to the store's calls: the inner store's (`storeReader`) and
one of `s.mu`'s. -/
def watchReader (s st : Loc) (γ : WsNames) : IProp GF :=
  iprop(storeReader st γ.st ∗ sync.ownRWMutex (wsMuAddr s) (watchStoreInv s γ))

-- `isStopChan`: `InvStore.lean` (2026-10-13: the store's stop channel uses it too).

/-- **The watchable store** `s` over the store `st` (persistent): the inner store and its read
view (`newWatchableStore` points it at `s`: unit 3b; `rev()` reads through it), the lock's guard, the victims' wake-up
channel (a bag channel, never closed), the stop channel, and the meta map's facts. -/
def isWatchableStore (s st : Loc) (γ : WsNames) : IProp GF :=
  iprop(∃ (vc stc rv : Loc) (γv : ChanNames),
    "#Hst" ∷ s.[watchableStore, go!"store"] ↦□ st ∗
    "#Hs" ∷ isStore st γ.st ∗
    "#Hrv" ∷ st.[store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    "#Hrvkv" ∷ rv.[readView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s : GoInterface) ∗
    "#Hmu" ∷ sync.isRWMutexGuard (wsMuAddr s) (watchStoreInv s γ) ∗
    "#Hvc" ∷ s.[watchableStore, go!"victimc"] ↦□ vc ∗
    "#Hvcb" ∷ isChanBag (V := Unit) γv vc (fun _ => iprop(True)) ∗
    "#Hstopc" ∷ s.[watchableStore, go!"stopc"] ↦□ stc ∗
    "#Hstop" ∷ isStopChan stc)

instance isWatchableStore_persistent (s st : Loc) (γ : WsNames) :
    Persistent (isWatchableStore (GF := GF) s st γ) := by
  unfold isWatchableStore; simp only [named]; infer_instance

/-- The store's choices for the stream's contract (`isWatchable`): a watcher of the store
(`IW`), cancelled (`WC`), nothing of the channel (`C`: the close right has its invariant),
filters deciding predicates (`F`), the close right (`CR`: the channel, its invariant, the
stream's half of the registered watchers), the reader slots (`R`) and a watch token (`T`: a
registration's cost, `watchTok`). -/
def storeWatchParams (s st : Loc) (γ : WsNames) : WatchParams GF where
  IW w := iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ ⌜0 ≤ sint.Z r.startRev⌝)
  WC w := iprop(∃ γw : WatcherNames, watcherMeta γ w γw ∗ cancelled γw)
  C _ := iprop(True)
  F f := iprop(∃ p : EvM → Bool, filterSpec f p)
  CR ch L := iprop(∃ γc : WatchChanNames, isChan ch γc.ch WatchResponse ∗
    inv watchN (watchChanInv γ ch γc) ∗ ghostVar γc.regl (1 : Qp).half L)
  R := watchReader s st γ
  T := watchTok γ
  IW_pers _ := by infer_instance
  WC_pers _ := by infer_instance
  C_pers _ := by infer_instance
  F_pers _ := by infer_instance

/-! ## The write transaction -/

/-- The revision tokens the sole writer at the committed log `L` holds (every one not spent). -/
def wBudget (L : Log) : Nat := 2 ^ 63 - 3 - L.length

/-- **The sole writer** of the watchable store at the committed (and notified) log `L`: its
certificate, every revision token not spent, and its half of the notified log. -/
def watchWriter (γ : WsNames) (L : Log) : IProp GF :=
  iprop(idxCert γ.st.idx L ∗ ownToks γ.st.revs (wBudget L) ∗ ghostVar γ.wlog (1 : Qp).half L)

/-- The write transaction `s.Write` returns (`tw`, a `watchableStoreTxnWrite`): its fields, the
inner transaction (`isTxnWrite` of `metricsTxnWrite` `mw`) over the inner store `st`, and the
sole writer's certificate, tokens but the transaction's and notified-log half. -/
def isWatchTxnWrite (tw s st : Loc) (γ : WsNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) : IProp GF :=
  iprop(∃ mw : Loc,
    "Htw" ∷ tw ↦ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                    s' := s } : watchableStoreTxnWrite) ∗
    "#Hws" ∷ isWatchableStore s st γ ∗
    "Htx" ∷ isTxnWrite mw st γ.st ilog pend puts deletes putSize ∗
    "#Hcert" ∷ idxCert γ.st.idx ilog ∗
    "Htoks" ∷ ownToks γ.st.revs (wBudget ilog - 1) ∗
    "Hwlog" ∷ ghostVar γ.wlog (1 : Qp).half ilog)

end reprs

end mvcc
end EtcdGrove
end Perennial
