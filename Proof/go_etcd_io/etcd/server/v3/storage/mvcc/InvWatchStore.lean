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
`L` that is sealed (`idxSealed γ.idx L`, `evsWf`: a lower bound of the index's history, and
well formed): `histOf` determines the log (`histOf_prefix_log`), and two lower bounds are
comparable (`idxSealed_prefix`), so every such statement is about the one log, without any
lock. The writer seals its pending revision before it notifies (`idxWriter_seal`), so a
revision's events go on the channels with the seal of the log that commits it (not yet its
commit certificate, `idxCert`: unit W-M2b), and with the store's caller's certificate of that
log (`certOk`, which `End` takes before it notifies: `evLog`, unit W-M3; for etcd's server, the
KV model of a committed raft prefix).

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
`WatchID`, events and `Revision`; and (ghost, unit W-K) the watchers a progress response covers
(`cov`: `respCov`; empty for any other response) and, for one of id `-1`, the watchers registered
on the channel when it was sent (`regs`); and its position in the sent list (`idx`). -/
structure RespM where
  w : Loc
  id : w64
  evs : List EvM
  rev : w64
  cov : List Loc
  regs : List Loc
  /-- its position in the channel's sent list (ghost, K1b): so the responses sent are distinct -/
  idx : Nat

instance RespM.countable : Pos.Countable RespM :=
  .ofInjective (fun r => Pos.Countable.encode (r.w, r.id, r.evs, r.rev, r.cov, r.regs, r.idx))
    (by rintro ⟨a, b, c, d, e, f, g⟩ ⟨a', b', c', d', e', f', g'⟩ h; have h := Pos.encode_inj h;
        simp_all)

instance watchResponseCountable [FfiSyntax] : Pos.Countable WatchResponse :=
  .ofInjective (fun r => Pos.Countable.encode (r.WatchID', r.Events', r.Revision', r.CompactRevision'))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

-- `WatchChanNames` (the channel's names): `InvWatchStream.lean` (unit W-M2).

/-- A watcher's ghost names (see the module docstring); `lo` is the first revision it watches. -/
structure WatcherNames where
  evs : GName
  live : GName
  wc : WatchChanNames
  lo : Nat

instance WatcherNames.countable : Pos.Countable WatcherNames :=
  .ofInjective (fun g => Pos.Countable.encode (g.evs, g.live, g.wc.ch.stateName, g.wc.ch.offerLockName,
      g.wc.ch.offerParkedPropName, g.wc.ch.offerParkedPredName, g.wc.ch.offerContinuationName,
      g.wc.ch.chanCap, g.wc.recv, g.wc.regl, g.wc.reg, g.wc.ids, g.wc.prog, g.wc.sentl, g.wc.regi,
      g.wc.rsn, g.lo))
    (by
      rintro ⟨a, b, ⟨⟨c1, c2, c3, c4, c5, c6⟩, d, e, f, i, j, k, k2, k3⟩, g⟩
        ⟨a', b', ⟨⟨c1', c2', c3', c4', c5', c6'⟩, d', e', f', i', j', k', k2', k3'⟩, g'⟩ h
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

/-! ## Channel states

`chanInflight` and `chanIsClosed` are the cache's (`InvWatcher`). -/

/-- **A watcher's first revision and its start revision** (pure): the first revision `lo` a
watcher of the range `r` watches from is its start revision, unless that is `0` ("now": then
`lo` is the length of the committed log at the registration, `watcherIs`). -/
def startLo (r : WatchRange) (lo : Nat) : Prop :=
  r.startRev ≠ W64 0 → lo = (sint.Z r.startRev).toNat

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

/-- Every victim, in a batch under the lock or out with the mover, has its `minRev` at most
`N`. -/
def WsState.vicBelow (σ : WsState) (N : Nat) : Prop :=
  (∀ w st, (σ.victimOf w).isSome → σ.ST !! w = some st → sint.Z st.minRev ≤ (N : Int)) ∧
  ∀ w st, σ.Wo !! w = some st → sint.Z st.minRev ≤ (N : Int)

/-- **The lock's state when `s.mu` is free** (unit W-K): every synced watcher is delivered at
most up to the notified log (or its first revision), every victim's `minRev` is at most the
notified log's length. (Not a `WsOk` field: inside `End`'s critical section `notify` delivers
the next revision before the commit extends the notified log.) -/
def WsState.settled (σ : WsState) : Prop := σ.syncedBelow σ.Lmu.length ∧ σ.vicBelow σ.Lmu.length

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

/-- A batch list with a batch that holds `w` finds one for it. -/
theorem findSome_isSome_of_mem {B : GMap Loc EventBatch} {l : List (GMap Loc EventBatch)} {w : Loc}
    (hB : B ∈ l) (hw : (B !! w).isSome) : (l.findSome? (· !! w)).isSome := by
  induction l with
  | nil => cases hB
  | cons x xs ih =>
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 hB with rfl | h
    · cases h' : B !! w with
      | none => rw [h'] at hw; cases hw
      | some _ => simp
    · cases h' : x !! w with
      | none => exact ih h
      | some _ => simp

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

/-- Two metas of a watcher agree (moved from `watcher__send.lean`, unit W-M2). -/
theorem watcherMeta_agree (γ : WsNames) (w : Loc) (γw γw' : WatcherNames) :
    ⊢ watcherMeta (GF := GF) γ w γw -∗ watcherMeta γ w γw' -∗ ⌜γw = γw'⌝ := by
  unfold watcherMeta
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- The watcher was cancelled (persistent). -/
def cancelled (γw : WatcherNames) : IProp GF := dghostVar γw.live DFrac.discard false

instance cancelled_persistent (γw : WatcherNames) : Persistent (cancelled (GF := GF) γw) := by
  unfold cancelled; infer_instance

/-- **A watched log** (persistent; unit W-M3): sealed (`idxSealed`: the index's history has it,
and it is well formed) and certified by the store's caller (`certOk`: the writer's `End` takes the
certificate of the log it commits before it notifies, `certOkNext`, and the store keeps the
committed log's, `revMuInv`). The certificate is what makes a watch event's revision reached in
the server's model (`etcdReached`: a certified log is the KV model of a committed raft log). -/
def evLog (γ : StoreNames) (L : Log) : IProp GF := iprop(idxSealed γ.idx L ∗ certOk γ L)

instance evLog_persistent (γ : StoreNames) (L : Log) : Persistent (evLog (GF := GF) γ L) := by
  unfold evLog; infer_instance

theorem evLog_sealed (γ : StoreNames) (L : Log) : evLog (GF := GF) γ L ⊢ idxSealed γ.idx L := by
  unfold evLog; iintro ⟨#H, -⟩; iexact H

theorem evLog_certOk (γ : StoreNames) (L : Log) : evLog (GF := GF) γ L ⊢ certOk γ L := by
  unfold evLog; iintro ⟨-, #H⟩; iexact H

/-- A committed log the caller certified is watched. -/
theorem evLog_of_cert (γ : StoreNames) (L : Log) :
    idxCert (GF := GF) γ.idx L ∗ certOk γ L ⊢ evLog γ L := by
  unfold evLog
  iintro ⟨#Hc, #Hok⟩
  ihave #Hs := idxCert_sealed _ _ $$ Hc
  iframe Hs Hok

/-- Two watched logs are in prefix order. -/
theorem evLog_cmp (γ : StoreNames) (L L' : Log) :
    ⊢ evLog (GF := GF) γ L -∗ evLog γ L' -∗ ⌜L <+: L' ∨ L' <+: L⌝ := by
  iintro #H1 #H2
  ihave #H1' := evLog_sealed γ L $$ H1
  ihave #H2' := evLog_sealed γ L' $$ H2
  iapply idxSealed_cmp $$ H1' H2'

/-- The empty log is watched. -/
theorem evLog_nil (γ : StoreNames) : ⊢ |==> evLog (GF := GF) γ [] := by
  imod idxSealed_nil (GF := GF) γ.idx with #H
  imodintro
  unfold evLog certOk
  iframe H
  ileft; ipureintro; simp

/-- The events `evs` are the range's of the revisions `[lo, d)` of a watched log (`evLog`:
sealed and certified; persistent; `d` past the log only for an empty range). -/
def evsWf (γ : WsNames) (r : WatchRange) (lo : Nat) (evs : List EvM) (d : Nat) : IProp GF :=
  iprop(∃ L : Log, evLog γ.st L ∗
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
    watcherMeta γ w γw ∗ ⌜γw.wc = γc⌝ ∗ ⌜startLo r γw.lo⌝ ∗ watcherFixed w r fcs ∗
    monoListAuthOwn γw.evs (1 : Qp).half evsw ∗
    ⌜(D.map Prod.fst).flatten = evsw ∧
      (sent.filter (fun x => decide (x.w = w))).map RespM.evs = (D.filter Deliv.sent).map Prod.snd⌝ ∗
    □ (([∗list] dl ∈ D, ∃ fs, filtersImpl fcs fs ∗ ⌜dl.2 = filtered fs dl.1⌝) ∗
      delivsCut γ r γw.lo D) ∗
    evsWf γ r γw.lo evsw d ∗
    ((⌜closed = false⌝ ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true) ∨ cancelled γw))

/-- **What the channel knows of a watcher registered on it** (persistent; unit W-M2): its fixed
range's id is one the channel's stream assigned to it (`chanIdAssigned`, made at the
registration by the stream's callback, `isWatchable`), and not `-1`. -/
def chanRegFact (γc : WatchChanNames) (w : Loc) : IProp GF :=
  iprop(∃ (rr : WatchRange) (fcs : GoSlice), watcherFixed w rr fcs ∗ chanIdAssigned γc rr.id w ∗
    ⌜rr.id ≠ W64 (-1)⌝)

instance chanRegFact_persistent (γc : WatchChanNames) (w : Loc) :
    Persistent (chanRegFact (GF := GF) γc w) := by
  unfold chanRegFact; infer_instance

/-- **What a response covers** (persistent; unit W-K, K1b): for every watcher `w'` it covers
(`x.cov`), on this channel, the responses sent for `w'` before it (`pre`, the sent list before
`x`) are its deliveries `D`'s sent ones, and `D`'s events are the range's of the revisions
`[lo, d)` of a watched log, with `d` past `x`'s revision: `w'` has received every event of its
range up to `x.rev`. -/
def covFact (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (w' : Loc) (rev : w64) :
    IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (D : List Deliv) (L : Log) (d : Nat),
    watcherMeta γ w' γw ∗ ⌜γw.wc = γc⌝ ∗ watcherFixed w' r fcs ∗ evLog γ.st L ∗
    □ (∀ dl : Deliv, ⌜dl ∈ D⌝ -∗ ∃ fs, filtersImpl fcs fs ∗ ⌜dl.2 = filtered fs dl.1⌝) ∗
    ⌜(pre.filter (fun y => decide (y.w = w'))).map RespM.evs = (D.filter Deliv.sent).map Prod.snd ∧
      (D.map Prod.fst).flatten = watchEvents L r γw.lo d ∧ (d ≤ L.length ∨ d ≤ γw.lo) ∧
      sint.Z rev + 1 ≤ (d : Int) ∧ ((d : Int) ≤ sint.Z rev + 1 ∨ d ≤ γw.lo)⌝)

instance covFact_persistent (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (w' : Loc)
    (rev : w64) : Persistent (covFact (GF := GF) γ γc pre w' rev) := by
  unfold covFact; infer_instance

/-- **A watcher cancelled for its reason** (persistent; K1b): its fixed range's id has the
channel's cancellation reason (`rsnFor`). -/
def rsnW (γc : WatchChanNames) (w : Loc) : IProp GF :=
  iprop(∃ (r : WatchRange) (fcs : GoSlice), watcherFixed w r fcs ∗ rsnFor γc.rsn r.id)

instance rsnW_persistent (γc : WatchChanNames) (w : Loc) : Persistent (rsnW (GF := GF) γc w) := by
  unfold rsnW; infer_instance

/-- The completeness of a response of id `-1` (K1b): every watcher registered on the channel when
it was sent (`x.regs`) is covered, or cancelled for its reason; and it has no events and its
revision is at least `1` (so the client broadcasts it: `IsProgressNotify`). -/
def respCompl (γc : WatchChanNames) (x : RespM) : IProp GF :=
  iprop(⌜x.id ≠ W64 (-1)⌝ ∨
    ((□ ∀ w : Loc, ⌜w ∈ x.regs⌝ -∗ ⌜w ∈ x.cov⌝ ∨ rsnW γc w) ∗ ⌜1 ≤ sint.Z x.rev ∧ x.evs = []⌝))

instance respCompl_persistent (γc : WatchChanNames) (x : RespM) :
    Persistent (respCompl (GF := GF) γc x) := by
  unfold respCompl; infer_instance

def respCov (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (x : RespM) : IProp GF :=
  iprop((□ ∀ w' : Loc, ⌜w' ∈ x.cov⌝ -∗ covFact γ γc pre w' x.rev) ∗ respCompl γc x ∗
    ⌜x.evs = [] → x.w ∈ x.cov⌝)

instance respCov_persistent (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (x : RespM) :
    Persistent (respCov (GF := GF) γ γc pre x) := by
  unfold respCov; infer_instance

/-- **The channel's sent list and registration indices** (unit W-K): the sent list's authority
(`sentl`), the registration indices' (`regi`: the registered watchers `L`'s, each at most the
sent list's length; a response of id `-1` sent at or after a watcher's registration lists it
in its `regs`), and what each response sent covers (`respCov`, K1b). -/
def regsOk (RI : GMap Loc Nat) (sent : List RespM) : Prop :=
  ∀ w n k x, RI !! w = some n → n ≤ k → sent[k]? = some x → x.id = W64 (-1) → w ∈ x.regs

/-- Each response sent is at its own position (K1b). -/
def idxOk (sent : List RespM) : Prop := ∀ (k : Nat) (x : RespM), sent[k]? = some x → x.idx = k

def sentAuth (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc) : IProp GF :=
  iprop(monoListAuthOwn γc.sentl 1 sent ∗ ∃ RI : GMap Loc Nat, ghostMapAuth γc.regi 1 RI ∗
    ⌜(∀ w, (RI !! w).isSome → w ∈ L) ∧ (∀ w n, RI !! w = some n → n ≤ sent.length) ∧
      regsOk RI sent ∧ idxOk sent⌝ ∗
    □ ([∗list] k ↦ x ∈ sent, respCov γ γc (sent.take k) x))

/-- **The stream channel `ch`'s invariant** (see the module docstring); unit W-M2: every
registered watcher's `chanRegFact`, and every response of id `-1` sent carries the channel's
progress fact. -/
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
    "#Hrf" ∷ □ ([∗list] w ∈ L, chanRegFact γc w) ∗
    "#Hpf" ∷ □ ([∗list] r ∈ sent, ⌜r.id = W64 (-1)⌝ → progFact γc.prog) ∗
    "Hsentl" ∷ sentAuth γ γc sent L ∗
    "Hws" ∷ [∗list] w ∈ L, chanWatcher γ γc (chanIsClosed s) sent w)

/-- **The channel had sent `l` (at least)** (persistent; unit W-K): a snapshot of the channel's
sent list (`sentl`). -/
def chanSentLb (γc : WatchChanNames) (l : List RespM) : IProp GF := monoListLbOwn γc.sentl l

instance chanSentLb_persistent (γc : WatchChanNames) (l : List RespM) :
    Persistent (chanSentLb (GF := GF) γc l) := by
  unfold chanSentLb; infer_instance

/-- **The stream's channel had sent `l` (at least)** (persistent; unit W-K): `chanSentLb`, named
through the stream's names (`γo.sentl = γc.sentl`, `isWatchStream`). -/
def streamSentLb (γo : WsStreamNames) (l : List RespM) : IProp GF := monoListLbOwn γo.sentl l

instance streamSentLb_persistent (γo : WsStreamNames) (l : List RespM) :
    Persistent (streamSentLb (GF := GF) γo l) := by
  unfold streamSentLb; infer_instance

/-- **`w` was registered on the channel when its sent list had length `n`** (persistent; K1b). -/
def chanRegAt (γc : WatchChanNames) (w : Loc) (n : Nat) : IProp GF :=
  ghostMapElem γc.regi w DFrac.discard n

instance chanRegAt_persistent (γc : WatchChanNames) (w : Loc) (n : Nat) :
    Persistent (chanRegAt (GF := GF) γc w n) := by
  unfold chanRegAt; infer_instance

open Iris.ProofMode in
theorem sentAuth_lb (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc) :
    sentAuth (GF := GF) γ γc sent L ⊢ sentAuth γ γc sent L ∗ chanSentLb γc sent := by
  unfold sentAuth chanSentLb
  iintro ⟨Ha, Hr⟩
  ihave #Hlb := monoListLbOwn_get γc.sentl 1 sent $$ Ha
  iframe Ha Hr Hlb

open Iris.ProofMode in
theorem sentAuth_lb_valid (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc)
    (l : List RespM) :
    sentAuth (GF := GF) γ γc sent L ∗ chanSentLb γc l ⊢ sentAuth γ γc sent L ∗ ⌜l <+: sent⌝ := by
  unfold sentAuth chanSentLb
  iintro ⟨⟨Ha, Hr⟩, #Hl⟩
  ihave %H := mono_list_auth_lb_valid _ _ _ _ $$ Ha Hl
  iframe Ha Hr
  ipureintro; exact H.2

open Iris.ProofMode in
theorem sentAuth_snoc (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc)
    (x : RespM) (hx : x.id = W64 (-1) → ∀ w ∈ L, w ∈ x.regs) (hxi : x.idx = sent.length) :
    ⊢ sentAuth (GF := GF) γ γc sent L -∗ respCov γ γc sent x ==∗ sentAuth γ γc (sent ++ [x]) L := by
  unfold sentAuth
  iintro ⟨Ha, %RI, Hr, %HRI, #Hc⟩ #Hx
  imod monoListAuthOwn_update_app [x] $$ Ha with ⟨Ha, -⟩
  imodintro
  iframe Ha
  iexists RI
  iframe Hr
  isplitr
  · ipureintro
    refine ⟨HRI.1, fun w n h => ?_, fun w n k y h hk hy hid => ?_, fun k y => ?_⟩
    · have := HRI.2.1 w n h
      simp only [List.length_append, List.length_singleton]; omega
    · by_cases hks : k < sent.length
      · rw [List.getElem?_append_left hks] at hy
        exact HRI.2.2.1 w n k y h hk hy hid
      · have hk' : k = sent.length := by
          have := (List.getElem?_eq_some_iff.1 hy).1
          simp only [List.length_append, List.length_singleton] at this; omega
        subst hk'
        rw [List.getElem?_append_right (Nat.le_refl _)] at hy
        simp at hy; subst hy
        exact hx hid w (HRI.1 w (by rw [h]; rfl))
    · show (sent ++ [x])[k]? = some y → y.idx = k
      intro hy
      by_cases hks : k < sent.length
      · rw [List.getElem?_append_left hks] at hy
        exact HRI.2.2.2 k y hy
      · have hk' : k = sent.length := by
          have := (List.getElem?_eq_some_iff.1 hy).1
          simp only [List.length_append, List.length_singleton] at this; omega
        subst hk'
        rw [List.getElem?_append_right (Nat.le_refl _)] at hy
        simp at hy; subst hy
        exact hxi
  imodintro
  iapply BigSepL.bigSepL_snoc.2
  isplitl
  · iapply (BigSepL.bigSepL_mono (fun {k y} hk => by
      have hk' : k < sent.length := (List.getElem?_eq_some_iff.1 hk).1
      rw [List.take_append_of_le_length (by omega)])) $$ Hc
  rw [List.take_left]; iexact Hx

open Iris.ProofMode in
theorem sentAuth_register (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc)
    (w : Loc) (hw : w ∉ L) :
    ⊢ sentAuth (GF := GF) γ γc sent L ==∗ sentAuth γ γc sent (w :: L) ∗ chanRegAt γc w sent.length := by
  unfold sentAuth chanRegAt
  iintro ⟨Ha, %RI, Hr, %HRI, #Hc⟩
  have hn : RI.lookup w = none := by
    cases h : RI.lookup w with
    | none => rfl
    | some _ => exact absurd (HRI.1 w (by rw [show RI !! w = RI.lookup w from rfl, h]; rfl)) hw
  imod ghost_map_insert_persist w sent.length hn $$ Hr with ⟨Hr, #He⟩
  imodintro
  iframe Ha He
  iexists RI.insert w sent.length
  iframe Hr Hc
  ipureintro
  refine ⟨fun x hx => ?_, fun x n h => ?_, fun x n k y h hk hy hid => ?_, HRI.2.2.2⟩
  · by_cases e : w = x
    · subst e; exact List.mem_cons_self
    · rw [show (RI.insert w sent.length) !! x = (<[w := sent.length]> RI) !! x from rfl,
        GMap.lookup_insert_ne _ _ e] at hx
      exact List.mem_cons_of_mem _ (HRI.1 x hx)
  · by_cases e : w = x
    · subst e
      rw [show (RI.insert w sent.length) !! w = (<[w := sent.length]> RI) !! w from rfl,
        GMap.lookup_insert] at h
      cases h; exact Nat.le_refl _
    · rw [show (RI.insert w sent.length) !! x = (<[w := sent.length]> RI) !! x from rfl,
        GMap.lookup_insert_ne _ _ e] at h
      exact HRI.2.1 x n h
  · by_cases e : w = x
    · subst e
      rw [show (RI.insert w sent.length) !! w = (<[w := sent.length]> RI) !! w from rfl,
        GMap.lookup_insert] at h
      cases h
      have := (List.getElem?_eq_some_iff.1 hy).1; omega
    · rw [show (RI.insert w sent.length) !! x = (<[w := sent.length]> RI) !! x from rfl,
        GMap.lookup_insert_ne _ _ e] at h
      exact HRI.2.2.1 x n k y h hk hy hid

open Iris.ProofMode in
theorem sentAuth_reg_le (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc)
    (w : Loc) (n : Nat) : sentAuth (GF := GF) γ γc sent L ∗ chanRegAt γc w n ⊢ ⌜n ≤ sent.length⌝ := by
  unfold sentAuth chanRegAt
  iintro ⟨⟨-, %RI, Hr, %HRI, -⟩, He⟩
  ihave %Hl := ghost_map_lookup $$ Hr He
  ipureintro; exact HRI.2.1 w n Hl

open Iris.ProofMode in
/-- **A response of id `-1` sent after a watcher's registration lists it** (K1b). -/
theorem sentAuth_reg_regs (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc)
    (w : Loc) (n : Nat) : sentAuth (GF := GF) γ γc sent L ∗ chanRegAt γc w n ⊢
      ⌜∀ k x, n ≤ k → sent[k]? = some x → x.id = W64 (-1) → w ∈ x.regs⌝ := by
  unfold sentAuth chanRegAt
  iintro ⟨⟨-, %RI, Hr, %HRI, -⟩, He⟩
  ihave %Hl := ghost_map_lookup $$ Hr He
  ipureintro; exact fun k x hk hx hid => HRI.2.2.1 w n k x Hl hk hx hid

open Iris.ProofMode in
/-- **Each response sent is at its own position** (K1b). -/
theorem sentAuth_idx (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc) :
    sentAuth (GF := GF) γ γc sent L ⊢ ⌜idxOk sent⌝ := by
  unfold sentAuth
  iintro ⟨-, %RI, -, %HRI, -⟩
  ipureintro; exact HRI.2.2.2

/-- Delivered up to `d'` at most `d`: a prefix of the events up to `d` (comparable logs). -/
theorem watchEvents_mono_cmp {L L' : Log} (hc : L <+: L' ∨ L' <+: L) (r : WatchRange) {lo d d' : Nat}
    (h : d ≤ L.length ∨ d ≤ lo) (h' : d' ≤ L'.length ∨ d' ≤ lo) (hd : d' ≤ d) :
    watchEvents L' r lo d' <+: watchEvents L r lo d := by
  by_cases hlo : d' ≤ lo
  · rw [watchEvents_empty _ _ hlo]; exact List.nil_prefix
  · have h1 : d' ≤ L.length := by omega
    rw [← watchEvents_cmp hc r (Or.inl h1) h', watchEvents_append L r (by omega) hd]
    exact List.prefix_append _ _

/-- **A later delivery is past an earlier one's revision** (comparable logs): if the events up to
`d` are a prefix of those up to `d'`, the latter are those of the revisions up to some `d''` at
least `d` (`d'`, or `d` when the two are the same events). -/
theorem watchEvents_cover {L L' : Log} (hc : L <+: L' ∨ L' <+: L) (r : WatchRange) {lo d d' : Nat}
    (h : d ≤ L.length ∨ d ≤ lo) (h' : d' ≤ L'.length ∨ d' ≤ lo)
    (hp : watchEvents L r lo d <+: watchEvents L' r lo d') :
    ∃ (L'' : Log) (d'' : Nat), watchEvents L' r lo d' = watchEvents L'' r lo d'' ∧
      (d'' ≤ L''.length ∨ d'' ≤ lo) ∧ d ≤ d'' ∧ (L'' = L ∨ L'' = L') := by
  by_cases hd : d ≤ d'
  · exact ⟨L', d', rfl, h', hd, Or.inr rfl⟩
  · have hq := watchEvents_mono_cmp hc r h h' (by omega)
    have he := hp.eq_of_length (Nat.le_antisymm hp.length_le hq.length_le)
    exact ⟨L, d, he.symm, h, Nat.le_refl _, Or.inl rfl⟩

/-- **What a sender of a response of id `-1` says of the channel** (persistent; K1b;
`watcher.send`): from its resource `CS` (lent), the channel's record of the registered watchers
(`regl`, at `L`) and the target watcher `γw` live, the progress fact, and every watcher of `L`
covered (`covl`) or cancelled for its reason. -/
def complW (γw : WatcherNames) (ql : Qp) (CS : IProp GF) (covl : List Loc) (id rev : w64)
    (evm : List EvM) : IProp GF :=
  iprop(□ ∀ L : List Loc, ⌜id = W64 (-1)⌝ -∗ CS -∗ ghostVar γw.wc.regl (1 : Qp).half L -∗
    dghostVar γw.live (DFrac.own ql) true -∗
    CS ∗ ghostVar γw.wc.regl (1 : Qp).half L ∗ dghostVar γw.live (DFrac.own ql) true ∗
      progFact γw.wc.prog ∗ □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ ⌜w ∈ covl⌝ ∨ rsnW γw.wc w) ∗
      ⌜1 ≤ sint.Z rev ∧ evm = []⌝)

instance complW_persistent (γw : WatcherNames) (ql : Qp) (CS : IProp GF) (covl : List Loc)
    (id rev : w64) (evm : List EvM) : Persistent (complW γw ql CS covl id rev evm) := by
  unfold complW; infer_instance

open Iris.ProofMode in
/-- What a send learns of a response's id (K1b): `w`'s own (not `-1`), or with `complW`: for id
`-1`, the progress fact and every registered watcher (`L`) covered or cancelled for its
reason. -/
theorem complW_facts (γw : WatcherNames) (ql : Qp) (CS : IProp GF) (L covl : List Loc)
    (id rid rev : w64) (evm : List EvM) (hrid : rid ≠ W64 (-1)) :
    CS ∗ (⌜id = rid⌝ ∨ complW γw ql CS covl id rev evm) ∗ ghostVar γw.wc.regl (1 : Qp).half L ∗
      dghostVar γw.live (DFrac.own ql) true ⊢
    CS ∗ ghostVar γw.wc.regl (1 : Qp).half L ∗ dghostVar γw.live (DFrac.own ql) true ∗
      (⌜id = W64 (-1)⌝ → progFact γw.wc.prog) ∗
      (⌜id ≠ W64 (-1)⌝ ∨ ((□ ∀ w : Loc, ⌜w ∈ L⌝ -∗ ⌜w ∈ covl⌝ ∨ rsnW γw.wc w) ∗
        ⌜1 ≤ sint.Z rev ∧ evm = []⌝)) := by
  iintro ⟨HCS, #Hid, Hregl, Hlv⟩
  by_cases hm : id = W64 (-1)
  · icases Hid with (%Heq | #Hw)
    · exact absurd (Heq ▸ hm) hrid
    iunfold complW at Hw
    icases Hw $$ %L %hm HCS Hregl Hlv with ⟨HCS, Hregl, Hlv, #Hp, #Hcm, %Hr1⟩
    iframe HCS Hregl Hlv
    isplitr
    · iintro %_; iexact Hp
    iright; iframe Hcm; ipureintro; exact Hr1
  · iframe HCS Hregl Hlv
    isplitr
    · iintro %h; exact absurd h hm
    ileft; ipureintro; exact hm

/-- **What `progressIfSync`'s caller says for a response of id `-1`** (persistent; K1b): from its
resource `CS` (lent), the channel's record of the registered watchers (`regl`, at `L`) and a
watcher `u` of the map `M` live, every watcher of `L` is one of `M` or cancelled for its
reason. -/
def complWS (γ : WsNames) (γc : WatchChanNames) (M : GMap w64 Loc) (CS : IProp GF) : IProp GF :=
  iprop(□ ∀ (L : List Loc) (u : Loc) (γw : WatcherNames) (ql : Qp),
    ⌜∃ id : w64, M !! id = some u⌝ -∗ watcherMeta γ u γw -∗ CS -∗
    ghostVar γc.regl (1 : Qp).half L -∗ dghostVar γw.live (DFrac.own ql) true -∗
    CS ∗ ghostVar γc.regl (1 : Qp).half L ∗ dghostVar γw.live (DFrac.own ql) true ∗
      □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ (∃ id : w64, ⌜M !! id = some w⌝) ∨ rsnW γc w))

instance complWS_persistent (γ : WsNames) (γc : WatchChanNames) (M : GMap w64 Loc)
    (CS : IProp GF) : Persistent (complWS γ γc M CS) := by
  unfold complWS; infer_instance

/-- **What a sender says of a watcher a progress response covers** (persistent; K1b;
`watcher.send`'s `covPre`): the watcher `c.w` of names `c.γw` on the channel, its fixed fields, a
lower bound of its delivered events (`c.evsw`), those the range's of `[lo, c.d)` (`evsWf`), `c.d`
past the response's revision, and it registered on the channel. -/
structure CovArg where
  w : Loc
  γw : WatcherNames
  r : WatchRange
  fcs : GoSlice
  evsw : List EvM
  d : Nat

def covEntry (γ : WsNames) (γc : WatchChanNames) (rev : w64) (c : CovArg) : IProp GF :=
  iprop(watcherMeta γ c.w c.γw ∗ ⌜c.γw.wc = γc⌝ ∗ watcherFixed c.w c.r c.fcs ∗
    monoListLbOwn c.γw.evs c.evsw ∗ evsWf γ c.r c.γw.lo c.evsw c.d ∗
    ⌜sint.Z rev + 1 ≤ (c.d : Int) ∧ ((c.d : Int) ≤ sint.Z rev + 1 ∨ c.d ≤ c.γw.lo)⌝ ∗
    ghostMapElem γc.reg c.w DFrac.discard ())

instance covEntry_persistent (γ : WsNames) (γc : WatchChanNames) (rev : w64) (c : CovArg) :
    Persistent (covEntry (GF := GF) γ γc rev c) := by
  unfold covEntry; infer_instance

def covPre (γ : WsNames) (γc : WatchChanNames) (rev : w64) (cs : List CovArg) : IProp GF :=
  [∗list] c ∈ cs, covEntry γ γc rev c

/-- **The covered watchers' delivered events, lent** (K2e-4): a fraction `q` of each one's
delivered events' authority, at the sender's `c.evsw`. While the sender holds it, the channel's
record of the watcher's events is the sender's (`cov_one`). -/
def covAuth (q : Qp) (cs : List CovArg) : IProp GF :=
  [∗list] c ∈ cs, monoListAuthOwn c.γw.evs q c.evsw

theorem covAuth_nil (q : Qp) : ⊢ covAuth (GF := GF) q [] := by
  unfold covAuth; iapply BigSepL.bigSepL_nil.2; iempintro

theorem covPre_nil (γ : WsNames) (γc : WatchChanNames) (rev : w64) :
    ⊢ covPre (GF := GF) γ γc rev [] := by
  unfold covPre; iapply BigSepL.bigSepL_nil.2; iempintro

instance covPre_persistent (γ : WsNames) (γc : WatchChanNames) (rev : w64) (cs : List CovArg) :
    Persistent (covPre (GF := GF) γ γc rev cs) := by
  unfold covPre; infer_instance

open Iris.ProofMode in
/-- **One covered watcher** (K1b): from the sender's `covEntry` and the channel's entry for the
watcher, its coverage of the responses `sent` so far. -/
theorem cov_one (γ : WsNames) (γc : WatchChanNames) (closed : Bool) (sent : List RespM)
    (L : List Loc) (rev : w64) (q : Qp) (c : CovArg) :
    covEntry (GF := GF) γ γc rev c ∗ monoListAuthOwn c.γw.evs q c.evsw ∗
      ghostMapAuth γc.reg 1 (regMap L) ∗
      ([∗list] w ∈ L, chanWatcher γ γc closed sent w) ⊢
    monoListAuthOwn c.γw.evs q c.evsw ∗ ghostMapAuth γc.reg 1 (regMap L) ∗
      ([∗list] w ∈ L, chanWatcher γ γc closed sent w) ∗ covFact γ γc sent c.w rev := by
  iintro ⟨Hce, Hq, Hreg, Hws⟩
  iunfold covEntry at Hce
  icases Hce with ⟨#Hm, %Hwc, #Hf, #Hlb, #Hwf, %Hrev, #Hreg1⟩
  ihave %Hl := ghost_map_lookup $$ Hreg Hreg1
  have hmem : c.w ∈ L := (regMap_lookup L c.w).1 (by
    rw [show (regMap L !! c.w) = (regMap L).lookup c.w from rfl, Hl]; rfl)
  icases BigSepL.bigSepL_mem_acc hmem $$ Hws with ⟨Hcw, Hback⟩
  iunfold chanWatcher at Hcw
  icases Hcw with ⟨%γw', %r', %fcs', %evsw', %D, %d', #Hm', %Hwc', %Hslo, #Hf', Ha', %HD, #HDf,
    #Hwf', Hlc⟩
  ihave %Hγ := watcherMeta_agree _ _ _ _ $$ Hm Hm'
  subst Hγ
  ihave %Hfx : ⌜c.r = r' ∧ c.fcs = fcs'⌝ $$ []
  · iapply watcherFixed_agree
    isplit
    · iexact Hf
    · iexact Hf'
  obtain ⟨hr, hfcs⟩ := Hfx
  subst hr; subst hfcs
  -- the sender's fraction: the channel's events are the sender's (K2e-4)
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Ha' Hq
  ihave #Hcov : covFact γ γc sent c.w rev $$ []
  · iunfold evsWf at Hwf
    icases Hwf with ⟨%L0, #HL0, %Hev0⟩
    iunfold covFact
    iexists c.γw, c.r, c.fcs, D, L0, c.d
    iframe Hm Hf HL0
    isplitr
    · ipureintro; exact Hwc
    isplitr
    · icases HDf with ⟨#HDs, -⟩
      iintro !> %dl %hdl
      icases BigSepL.bigSepL_mem_acc hdl $$ HDs with ⟨H, -⟩
      iexact H
    ipureintro
    exact ⟨HD.2, HD.1.trans (Hag.2.trans Hev0.1), Hev0.2, Hrev⟩
  iframe Hq Hreg Hcov
  iapply Hback
  iunfold chanWatcher
  iexists c.γw, c.r, c.fcs, evsw', D, d'
  iframe Hm' Hf' Ha' Hwf' Hlc
  iframe #
  ipureintro; exact ⟨Hwc', Hslo, HD⟩

open Iris.ProofMode in
/-- **Every covered watcher** (K1b): `cov_one` for each. -/
theorem cov_list (γ : WsNames) (γc : WatchChanNames) (closed : Bool) (sent : List RespM)
    (L : List Loc) (rev : w64) (q : Qp) :
    ∀ cs : List CovArg, covPre (GF := GF) γ γc rev cs ∗ covAuth q cs ∗
      ghostMapAuth γc.reg 1 (regMap L) ∗
      ([∗list] w ∈ L, chanWatcher γ γc closed sent w) ⊢
    covAuth q cs ∗ ghostMapAuth γc.reg 1 (regMap L) ∗
      ([∗list] w ∈ L, chanWatcher γ γc closed sent w) ∗
      □ ([∗list] c ∈ cs, covFact γ γc sent c.w rev)
  | [] => by
    unfold covPre
    iintro ⟨-, Hq, Hreg, Hws⟩
    iframe Hq Hreg Hws
    iintro !>; iapply BigSepL.bigSepL_nil.2; iempintro
  | c :: cs => by
    unfold covPre covAuth
    iintro ⟨#Hp, Hq, Hreg, Hws⟩
    icases BigSepL.bigSepL_cons.1 $$ Hp with ⟨Hc, Hp'⟩
    icases BigSepL.bigSepL_cons.1 $$ Hq with ⟨Hq1, Hq⟩
    icases cov_one γ γc closed sent L rev q c $$ [$Hc $Hq1 $Hreg $Hws] with ⟨Hq1, Hreg, Hws, #Hcf⟩
    icases cov_list γ γc closed sent L rev q cs $$ [Hq Hreg Hws] with ⟨Hq, Hreg, Hws, #Hcfs⟩
    · unfold covPre covAuth; iframe Hp' Hq Hreg Hws
    iunfold covAuth at Hq
    iframe Hreg Hws
    isplitl [Hq1 Hq]
    · iapply BigSepL.bigSepL_cons.2; iframe Hq1 Hq
    iintro !>
    iapply BigSepL.bigSepL_cons.2
    iframe Hcf Hcfs

open Iris.ProofMode in
/-- The coverage of a response whose covered watchers are `cs`'s. -/
theorem respCov_of_list (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (x : RespM)
    (cs : List CovArg) (hcov : x.cov = cs.map CovArg.w) (hown : x.evs = [] → x.w ∈ x.cov) :
    □ ([∗list] c ∈ cs, covFact (GF := GF) γ γc pre c.w x.rev) ∗ respCompl γc x ⊢
      respCov γ γc pre x := by
  iintro ⟨#H, #Hc⟩
  iunfold respCov
  iframe Hc
  isplitr
  rotate_left
  · ipureintro; exact hown
  iintro !> %w' %hw'
  rw [hcov] at hw'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hw'
  icases BigSepL.bigSepL_mem_acc hc $$ H with ⟨Hc, -⟩
  iexact Hc

/-- **What a sent response covers** (persistent; K1b): the coverage of the response at index `k`. -/
theorem sentAuth_cov (γ : WsNames) (γc : WatchChanNames) (sent : List RespM) (L : List Loc)
    (k : Nat) (x : RespM) (hk : sent[k]? = some x) :
    sentAuth (GF := GF) γ γc sent L ⊢ sentAuth γ γc sent L ∗ respCov γ γc (sent.take k) x := by
  unfold sentAuth
  iintro ⟨Ha, %RI, Hr, %HRI, #Hc⟩
  ihave #Hx := BigSepL.bigSepL_lookup (Φ := fun k x => respCov (GF := GF) γ γc (sent.take k) x) hk
    $$ Hc
  iframe Ha Hx
  iexists RI
  iframe Hr Hc
  ipureintro; exact HRI

/-- **A watcher's registration index, named through the stream** (persistent; K1b): the
channel's `chanRegAt`, by the stream's `regi` (`γo.regi = γc.regi`). -/
def streamRegAt (γo : WsStreamNames) (w : Loc) (n : Nat) : IProp GF :=
  ghostMapElem γo.regi w DFrac.discard n

instance streamRegAt_persistent (γo : WsStreamNames) (w : Loc) (n : Nat) :
    Persistent (streamRegAt (GF := GF) γo w n) := by
  unfold streamRegAt; infer_instance

theorem chanRegAt_stream (γo : WsStreamNames) (γc : WatchChanNames) (w : Loc) (n : Nat)
    (h : γo.regi = γc.regi) : chanRegAt (GF := GF) γc w n ⊣⊢ streamRegAt γo w n := by
  unfold chanRegAt streamRegAt; rw [h]; exact .rfl

theorem chanSentLb_stream (γo : WsStreamNames) (γc : WatchChanNames) (l : List RespM)
    (h : γo.sentl = γc.sentl) : chanSentLb (GF := GF) γc l ⊣⊢ streamSentLb γo l := by
  unfold chanSentLb streamSentLb; rw [h]; exact .rfl

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
          victimBatchOk lo st B ∧ B.evs ≠ []⌝ ∗
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

theorem popFacts_synced (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (h : (σ.Ws !! k).isSome) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ d⌝ ∗ evsWf γ r lo evsw d) := by
  unfold popFacts; rw [if_pos h]

theorem popFacts_victim (γ : WsNames) (σ : WsState) (k : Loc) (r : WatchRange) (lo : Nat)
    (st : WatcherSt) (evsw : List EvM) (d : Nat) (B : EventBatch) (h1 : (σ.Ws !! k).isSome = false)
    (h2 : (σ.Wu !! k).isSome = false) (h3 : σ.victimOf k = some B) :
    popFacts (GF := GF) γ σ k r lo st evsw d =
      iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev ∧ victimBatchOk lo st B ∧
        B.evs ≠ []⌝ ∗ evsWf γ r lo (evsw ++ B.evs) d) := by
  unfold popFacts; simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]

/-- `memberRes` moves to a state that agrees with it at the watcher. -/
theorem memberRes_congr (γ : WsNames) (q : Qp) (σ σ' : WsState) (w : Loc) (st : WatcherSt)
    (hM : σ'.M = σ.M) (hWs : (σ'.Ws !! w).isSome = (σ.Ws !! w).isSome)
    (hWu : (σ'.Wu !! w).isSome = (σ.Wu !! w).isSome) (hV : σ'.victimOf w = σ.victimOf w)
    (hE : σ'.E !! w = σ.E !! w) :
    memberRes (GF := GF) γ q σ w st ⊢ memberRes γ q σ' w st := by
  have hl : σ'.live w = σ.live w := by unfold WsState.live; rw [hWs, hWu, hV]
  unfold memberRes popFacts
  simp only [hM, hl, hWs, hWu, hV, hE]
  exact .rfl

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

/-- **The notified log's ghosts** at the lock's fraction `q`: half of `γ.wlog` at it (the sole
writer holds the other half) and `s.mu`'s quarter of the committed log's authority at it (the
outer quarter, `logQ`; unit W-K: the commit happens under `s.mu` after the notify, so a reader
under `s.mu` finds every certified log a prefix of the notified one, `wlogQ_cert_prefix`). -/
def wlogQ (γ : WsNames) (q : Qp) (L : Log) : IProp GF :=
  iprop(monoListAuthOwn γ.wlog q.half L ∗ idxLogAuth γ.st.idx q.half.half L)

/-- **Every certified log is a prefix of the notified one** (unit W-K): under `s.mu`, from the
lock's quarter of the committed log's authority. -/
theorem wlogQ_cert_prefix (γ : WsNames) (q : Qp) (L C : Log) :
    wlogQ (GF := GF) γ q L ∗ idxCert γ.st.idx C ⊢ ⌜C <+: L⌝ := by
  unfold wlogQ
  iintro ⟨⟨-, Ha⟩, Hc⟩
  iapply idxLogAuth_cert_prefix $$ [$Ha $Hc]

/-- **The store had notified `L` (at least)** (persistent; unit W-K): a lower bound of the
notified log (`γ.wlog` is a monotone list, half the lock's, half the sole writer's). -/
def notifiedLb (γ : WsNames) (L : Log) : IProp GF := monoListLbOwn γ.wlog L

instance notifiedLb_persistent (γ : WsNames) (L : Log) : Persistent (notifiedLb (GF := GF) γ L) := by
  unfold notifiedLb; infer_instance

theorem wlogQ_lb (γ : WsNames) (q : Qp) (L : Log) :
    wlogQ (GF := GF) γ q L ⊢ wlogQ γ q L ∗ notifiedLb γ L := by
  unfold wlogQ notifiedLb
  iintro ⟨Ha, Hb⟩
  ihave #Hlb := monoListLbOwn_get γ.wlog _ L $$ Ha
  iframe Ha Hb Hlb

/-- Every lower bound of the notified log is a prefix of the lock's. -/
theorem wlogQ_lb_valid (γ : WsNames) (q : Qp) (L L' : Log) :
    wlogQ (GF := GF) γ q L ∗ notifiedLb γ L' ⊢ ⌜L' <+: L⌝ := by
  unfold wlogQ notifiedLb
  iintro ⟨⟨Ha, -⟩, Hl⟩
  ihave %H := mono_list_auth_lb_valid _ _ _ _ $$ Ha Hl
  ipureintro; exact H.2

/-- A mono list's authority, as two halves. -/
theorem monoList_halves (g : GName) (L : Log) :
    monoListAuthOwn (GF := GF) g 1 L ⊣⊢ monoListAuthOwn g (1 : Qp).half L ∗ monoListAuthOwn g (1 : Qp).half L := by
  have h := (monoListAuthOwn_fractional (GF := GF) g L).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

/-- The two halves of the notified log, updated to a longer log. -/
theorem wlog_update_halves (γ : WsNames) (L L' : Log) (h : L <+: L') :
    ⊢ monoListAuthOwn (GF := GF) γ.wlog (1 : Qp).half L -∗ monoListAuthOwn γ.wlog (1 : Qp).half L ==∗
      monoListAuthOwn γ.wlog (1 : Qp).half L' ∗ monoListAuthOwn γ.wlog (1 : Qp).half L' := by
  iintro H1 H2
  ihave Hf : monoListAuthOwn (GF := GF) γ.wlog 1 L $$ [H1 H2]
  · iapply (monoList_halves γ.wlog L).2
    iframe H1 H2
  imod monoListAuthOwn_update L' h $$ Hf with ⟨Hf, -⟩
  iapply (monoList_halves γ.wlog L').1 $$ Hf

/-- **Under `s.mu`, the committed log is the notified one** (unit W-K): another fraction of the
committed log's authority agrees with the lock's. -/
theorem wlogQ_auth_agree (γ : WsNames) (q q' : Qp) (L C : Log) :
    wlogQ (GF := GF) γ q L ∗ idxLogAuth γ.st.idx q' C ⊢ ⌜C = L⌝ := by
  unfold wlogQ
  iintro ⟨⟨-, Ha⟩, Hc⟩
  ihave %H := monoListAuthOwn_agree _ _ _ _ _ $$ Hc Ha
  ipureintro; exact H.2

/-- The lock invariant at the state `σ` and the fraction `q`. -/
def watchStoreBody (s : Loc) (γ : WsNames) (q : Qp) (σ : WsState) : IProp GF :=
  iprop("Hσ" ∷ ghostVar γ.wst q σ ∗
    "Hwlog" ∷ wlogQ γ q σ.Lmu ∗
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
  iprop(∃ σ : WsState, watchStoreBody s γ q σ ∗ ⌜σ.settled⌝)

/-! ## The store -/

/-- The reader slots a caller lends to the store's calls: the inner store's (`storeReader`) and
one of `s.mu`'s. -/
def watchReader (s st : Loc) (γ : WsNames) : IProp GF :=
  iprop(storeReader st γ.st ∗ sync.ownRWMutex (wsMuAddr s) (watchStoreInv s γ))

-- `isStopChan`: `InvStore.lean` (2026-10-13: the store's stop channel uses it too).

/-- **The watchable store** `s` over the store `st` (persistent): the inner store and its read
view (`newWatchableStore` points it at `s`: unit 3b; `rev()` reads through it), the lock's guard, the victims' wake-up
channel (a bag channel, never closed), the stop channel, and the meta map's facts; the inner
store is a watchable store's (`γ.st.watchQ`, unit W-K: `s.mu` holds the outer quarter). -/
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
    "#Hstop" ∷ isStopChan stc ∗
    "%Hwq" ∷ ⌜γ.st.watchQ = true⌝)

instance isWatchableStore_persistent (s st : Loc) (γ : WsNames) :
    Persistent (isWatchableStore (GF := GF) s st γ) := by
  unfold isWatchableStore; simp only [named]; infer_instance

/-- **What a registration says of the watcher `w`** (persistent; the store's `IWF`): its
names (`watcherMeta`), its fixed fields (range `r`, filters `fcs`), and its first revision `lo`:
the start revision, or, for a start revision `0`, the length of a committed log `C` at the
registration (`idxCert`: the next revision the store will commit); and (unit W-K) its
registration index on its channel (`chanRegAt`). -/
def watcherIs (γ : WsNames) (w : Loc) (r : WatchRange) (fcs : GoSlice) (lo : Nat) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (C : Log), watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
    idxCert γ.st.idx C ∗ (∃ n : Nat, chanRegAt γw.wc w n) ∗
    ⌜γw.lo = lo ∧ lo = if r.startRev = W64 0 then C.length else (sint.Z r.startRev).toNat⌝)

instance watcherIs_persistent (γ : WsNames) (w : Loc) (r : WatchRange) (fcs : GoSlice)
    (lo : Nat) : Persistent (watcherIs (GF := GF) γ w r fcs lo) := by
  unfold watcherIs; infer_instance

/-- The store's choices for the stream's contract (`isWatchable`): a watcher of the store
(`IW`), cancelled (`WC`), nothing of the channel (`C`: the close right has its invariant),
filters deciding predicates (`F`), the close right (`CR`: the channel, its invariant, the
stream's half of the registered watchers), the reader slots (`R`) and a watch token (`T`: a
registration's cost, `watchTok`), and what a registration says of its watcher (`IWF`:
`watcherIs`). -/
def storeWatchParams (s st : Loc) (γ : WsNames) : WatchParams GF where
  IW w := iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    watcherMeta γ w γw ∗ watcherFixed w r fcs ∗ ⌜0 ≤ sint.Z r.startRev ∧ r.id ≠ W64 (-1)⌝)
  WC w := iprop(∃ γw : WatcherNames, watcherMeta γ w γw ∗ cancelled γw)
  C _ := iprop(True)
  F f := iprop(∃ p : EvM → Bool, filterSpec f p)
  CR ch γc L := iprop(isChan ch γc.ch WatchResponse ∗
    inv watchN (watchChanInv γ ch γc) ∗ ghostVar γc.regl (1 : Qp).half L)
  R := watchReader s st γ
  T := watchTok γ
  IWF := watcherIs γ
  OC w γc := iprop(∃ γw : WatcherNames, watcherMeta γ w γw ∗ ⌜γw.wc = γc⌝)
  IW_pers _ := by infer_instance
  WC_pers _ := by infer_instance
  C_pers _ := by infer_instance
  F_pers _ := by infer_instance
  IWF_pers _ _ _ _ := by infer_instance
  OC_pers _ _ := by infer_instance

/-! ## The write transaction -/

/-- The revision tokens the sole writer at the committed log `L` holds (every one not spent). -/
def wBudget (L : Log) : Nat := 2 ^ 63 - 3 - L.length

/-- **The sole writer** of the watchable store at the committed (and notified) log `L`: its
certificate, every revision token not spent, and its half of the notified log. -/
def watchWriter (γ : WsNames) (L : Log) : IProp GF :=
  iprop(idxCert γ.st.idx L ∗ ownToks γ.st.revs (wBudget L) ∗ monoListAuthOwn γ.wlog (1 : Qp).half L)

/-- The write transaction `s.Write` returns (`tw`, a `watchableStoreTxnWrite`): its fields, the
inner transaction (`isTxnWrite` of `metricsTxnWrite` `mw`) over the inner store `st`, and the
sole writer's certificate, tokens but the transaction's and notified-log half. -/
def isWatchTxnWrite (tw s st : Loc) (γ : WsNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) : IProp GF :=
  iprop(∃ mw : Loc,
    "Htw" ∷ tw ↦ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                    s' := s } : watchableStoreTxnWrite) ∗
    "#Hws" ∷ isWatchableStore s st γ ∗
    "Htx" ∷ isTxnWrite mw st γ.st trace ilog pend puts deletes putSize ∗
    "#Hcert" ∷ idxCert γ.st.idx ilog ∗
    "Htoks" ∷ ownToks γ.st.revs (wBudget ilog - 1) ∗
    "Hwlog" ∷ monoListAuthOwn γ.wlog (1 : Qp).half ilog)

end reprs

end mvcc
end EtcdGrove
end Perennial
