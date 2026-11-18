/-
The watchable store (`watchable_store.go`, `watchable_store_txn.go`): its lock invariant, the
stream channels' protocol and the watchers' ghost state. Lean-first; `notes/decisions.md`, "The
watchable store's concurrency (unit 3)".

**The model** (pure; `WatchModel.lean`). The events the watchers see of a revision `r` (`evsOfRevM`) are the
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
flight (with their events' `PrevKv` fields, owned: `respsPk`, k8s 7f-3b), the list of registered watchers (half of `regl`, the other half the stream's close right
`CR`, which the close deposits; every response sent is for one of them) and, per registered watcher, its deliveries: the segments of its delivered events, each
filtered by some predicate its filters implement (sent unless all its events were filtered
out), and whether it is live (an open channel) or cancelled (a closed channel has no live
watcher).

**The lock invariant** (`watchStoreInv s st γ q`, the resource of `s.mu`, at the fraction `q`
of the read side): the notified log `Lmu` (its certificate; `γ.wlog`, the lock's alone since
2026-11-06, until then half, the sole writer's the other), the two groups, the victim batches, every watcher's state
(the cancelled ones included: `cancelWatcher` reads `wa.ch`) and half of the states of the
victims out with the mover, the meta map's authority with the watcher budget (`watchBudget`:
the watchers with names and the unspent watch tokens below `2 ^ 63 - 3`), and per live watcher
its ghosts and the facts of its population (`memberRes`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchPos
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

instance watchResponseCountable [GooseExts] : Pos.Countable WatchResponse :=
  .ofInjective (fun r => Pos.Countable.encode (r.WatchID', r.Events', r.Revision', r.CompactRevision'))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

-- `WatchChanNames` (the channel's names): `InvWatchStream.lean` (unit W-M2).

/-- A watcher's ghost names (see the module docstring); `lo` is the first revision it watches. -/
structure WatcherNames where
  evs : GName
  live : GName
  wc : WatchChanNames
  lo : Nat
  /-- (W2 of `notes/watch-cut-plan.md`) a watch from now (start revision `0`): its first
  revision is the notified log's length at its registration, so within the notified log from then
  on (`WsState.srBelow`). Any other watcher's first revision is its start revision, which
  `progressIfSync`'s guard bounds (no progress notification below a watcher's start). -/
  now : Bool
  /-- (stage 2 of the mvcc API, 2026-11-05) the saved name of its filters' predicates
  (`api.savedFilters`, allocated at the registration): one predicate list per watcher, the
  stream's history's (`watcherFilters`) -/
  fg : GName

instance WatcherNames.countable : Pos.Countable WatcherNames :=
  .ofInjective (fun g => Pos.Countable.encode (g.evs, g.live, g.wc.ch.stateName, g.wc.ch.offerLockName,
      g.wc.ch.offerParkedPropName, g.wc.ch.offerParkedPredName, g.wc.ch.offerContinuationName,
      g.wc.ch.chanCap, g.wc.recv, g.wc.regl, g.wc.reg, g.wc.ids, g.wc.prog, g.wc.sentl, g.wc.regi,
      g.wc.rsn, g.wc.aev, g.wc.ans, g.wc.arcv, g.wc.arx, g.wc.acl, g.lo, g.now, g.fg))
    (by
      rintro ⟨a, b, ⟨⟨c1, c2, c3, c4, c5, c6⟩, d, e, f, i, j, k, k2, k3, a1, a2, a3, a4, a5⟩, g, g2,
          g3⟩
        ⟨a', b', ⟨⟨c1', c2', c3', c4', c5', c6'⟩, d', e', f', i', j', k', k2', k3', a1', a2', a3',
          a4', a5'⟩, g', g2', g3'⟩ h
      have h := Pos.encode_inj h
      simp_all)

/-- The watchable store's ghost names: the store's, the watchers' names (`wmeta`: a ghost map
from a watcher to its names, persistent elements), the notified log (`wlog`: half the lock
invariant's, half the sole writer's), and the lock invariant's state (`wst`: `ghostVar
WsState`, at the lock's fraction, so that two parts of the invariant agree on it); and the
owner's tag (`tag`: a ghost name the store's creator chooses, `newWatchableStore`'s `γtag`, of no
meaning to mvcc: the watch server records its auth mode under it, `auth.modeTag`, so that the
stream specification can name the mode at the store's names; the auth plan's A4, 2026-10-24). -/
structure WsNames where
  st : StoreNames
  wmeta : GName
  wlog : GName
  wst : GName
  /-- the watcher budget (`watchBudget`): a registration costs one token (`watchTok`) -/
  wt : GName
  /-- (D25) the released length: a monotone nat, the notified log's length under `s.mu`
  (`watchStoreInv`), bumped by `End` before it notifies the pending revision's events, so every
  delivered event's revision is below it (`relLb`, kept by `evsWf`) -/
  rel : GName
  /-- the owner's tag (see above): `newWatchableStore` takes it, states nothing of it -/
  tag : GName

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

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

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
def watchN : Namespace := (nroot .@ "mvcc") .@ "watch"

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

/-- `w` is a live watcher under the lock: synced, unsynced or a victim, or (watches across a
compaction, 2026-11-01) compacted with its channel open (`chooseAll` sent it its compaction
response and deleted it from the unsynced group; it waits for its cancel, `cancelWatcher`'s
`compacted` arm). -/
def WsState.live (σ : WsState) (w : Loc) : Prop :=
  (σ.Ws !! w).isSome ∨ (σ.Wu !! w).isSome ∨ (σ.victimOf w).isSome ∨
    (σ.ST !! w).any (fun st => st.compacted && st.ch != null)

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
    (st.compacted = true → (σ.Ws !! w) = none ∧ σ.victimOf w = none) ∧
    (σ.live w → (st.victim = true ↔ (σ.victimOf w).isSome)) ∧ (st.ch = null ↔ ¬ σ.live w)
  wo_flags : ∀ w st, σ.Wo !! w = some st →
    st.compacted = false ∧ st.victim = true ∧ st.ch ≠ null
  synced_d : ∀ w γw ed, (σ.Ws !! w).isSome → σ.M !! w = some γw → σ.E !! w = some ed →
    max γw.lo σ.Lmu.length ≤ ed.2

/-- **An unsynced watcher beyond the notified log is restoring** (D22 receiver epochs, S6,
2026-10-22): its `restore` flag is set (`watchableStore.Restore` sets it of every watcher it moves
from the synced group, whose `minRev` may be past the restored log: `chooseAll` then clears it
rather than panic, and `syncWatchers` moves it to the synced group in the same pass). Not a
`WsOk` field: `chooseAll`'s clearing breaks it inside `syncWatchers`' critical section. Until S6
`WsOk.st_flags` said no watcher restores. -/
def WsState.unsRst (σ : WsState) : Prop :=
  ∀ w st, (σ.Wu !! w).isSome → σ.ST !! w = some st →
    sint.Z st.minRev < σ.Lmu.length ∨ st.restore = true

/-- Every synced watcher is delivered at most up to `N`, or to its first revision (what the
sole writer's history says, before it seals: `End`). -/
def WsState.syncedBelow (σ : WsState) (N : Nat) : Prop :=
  ∀ w γw ed, (σ.Ws !! w).isSome → σ.M !! w = some γw → σ.E !! w = some ed →
    ed.2 ≤ N ∨ ed.2 ≤ γw.lo

/-- Every victim, in a batch under the lock or out with the mover, has its `minRev` at most
`N`. -/
def WsState.vicBelow (σ : WsState) (N : Nat) : Prop :=
  (∀ w st, (σ.victimOf w).isSome → σ.ST !! w = some st → sint.Z st.minRev ≤ (N : Int)) ∧
  ∀ w st, σ.Wo !! w = some st → sint.Z st.minRev ≤ (N : Int)

/-- Every watch from now (`now`) has its first revision at most `N`. -/
def WsState.srBelow (σ : WsState) (N : Nat) : Prop :=
  ∀ w γw, σ.M !! w = some γw → γw.now = true → γw.lo ≤ N

/-- **The lock's state when `s.mu` is free** (unit W-K): every synced watcher is delivered at
most up to the notified log (or its first revision), every victim's `minRev` is at most the
notified log's length. (Not a `WsOk` field: inside `End`'s critical section `notify` delivers
the next revision before the commit extends the notified log.) -/
def WsState.settled (σ : WsState) : Prop := σ.syncedBelow σ.Lmu.length ∧ σ.vicBelow σ.Lmu.length

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## Filters -/

/-- The filter `f` (a `FilterFunc`) decides the predicate `p` on events. -/
def filterSpec (f : GoFunc) (p : EvM → Bool) : IProp GF :=
  iprop(□ ∀ (e : Loc) (ev : EvM),
    {{ evRd e ev }} (App (Val #f) (Val #e)) {{ (b : Bool), RET #b; ⌜b = p ev⌝ }})

/-- The filters `fcs` (a slice, read-only for good) implement the predicates `fs`. -/
def filtersImpl (fcs : GoSlice) (fs : List (EvM → Bool)) : IProp GF :=
  iprop(∃ fps : List GoFunc, fcs ↦*□ fps ∗ ⌜fps.length = fs.length⌝ ∗
    [∗list] x ∈ fps.zip fs, filterSpec x.1 x.2)

/-- **A registered watcher's filters** (persistent; stage 2 of the mvcc API, 2026-11-05): the
filters `fcs` implement the predicates saved under the watcher's name `γw.fg` (the registration's
choice), so that every delivery to it is filtered by the same predicates. -/
def watcherFilters (γw : WatcherNames) (fcs : GoSlice) : IProp GF :=
  iprop(∃ fs, filtersImpl fcs fs ∗ api.savedFilters γw.fg fs)

/-! ## Responses -/

/-- The `WatchResponse` value `v` is the response `r`: its id, revision and compaction revision,
its events a read-only slice of `r`'s events (`evRd` each: their fields but `PrevKv`, which the
response owns, `respPk`). -/
def respIs (v : WatchResponse) (r : RespM) : IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = r.compactRev⌝ ∗
    ∃ ps : List Loc, v.Events' ↦*□ ps ∗ ⌜ps.length = r.evs.length⌝ ∗
      [∗list] x ∈ ps.zip r.evs, evRd x.1 x.2)

/-- **The `PrevKv` fields of the response `v`'s events, owned** (k8s 7f-3b): the watcher's copies'
(`evPk`), which the channel hands to the receiver with the response. -/
def respPk (v : WatchResponse) (r : RespM) : IProp GF :=
  iprop(∃ ps : List Loc, v.Events' ↦*□ ps ∗ [∗list] x ∈ ps.zip r.evs, evPk x.1 x.2)

/-- The in-flight responses' `PrevKv` fields (the channel invariant's). -/
def respsPk (vs : List WatchResponse) (rs : List RespM) : IProp GF :=
  iprop([∗list] x ∈ vs.zip rs, respPk x.1 x.2)

/-- The values `vs` are the responses `rs`, pointwise. -/
def respsIs (vs : List WatchResponse) (rs : List RespM) : IProp GF :=
  iprop(⌜vs.length = rs.length⌝ ∗
    □ (∀ (i : Nat) (v : WatchResponse) (r : RespM), ⌜vs[i]? = some v⌝ -∗ ⌜rs[i]? = some r⌝ -∗
      respIs v r))

/-- What a response says, for good: its revision is at or above its events', a response with
events carries its watcher's id, and (watches across a compaction, 2026-11-01) a compaction
response (`compactRev ≠ 0`, `chooseAll`'s) has no events, carries its watcher's own id (never
`-1`) and no revision (Go leaves `Revision` unset). Margin: the code also gives
`minRev < compactRev ≤ curRev` for the watcher's `minRev` at the choice; no client needs it. -/
def respOk (r : RespM) : IProp GF :=
  iprop(⌜∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev⌝ ∗
    ∃ (rr : WatchRange) (fcs : GoSlice), watcherFixed r.w rr fcs ∗
      ⌜(r.evs ≠ [] → r.id = rr.id) ∧ (r.id = rr.id ∨ r.id = W64 (-1)) ∧
        (r.compactRev ≠ W64 0 → r.evs = [] ∧ r.id = rr.id ∧ r.id ≠ W64 (-1) ∧ r.rev = W64 0)⌝)

/-! ## Per watcher -/

/-- The watcher `w`'s ghost names (persistent). -/
def watcherMeta (γ : WsNames) (w : Loc) (γw : WatcherNames) : IProp GF :=
  ghostMapElem γ.wmeta w DFrac.discard γw

/-- The watcher was cancelled (persistent). -/
def cancelled (γw : WatcherNames) : IProp GF := dghostVar γw.live DFrac.discard false

/-- **A watched log** (persistent; unit W-M3): sealed (`idxSealed`: the index's history has it,
and it is well formed) and certified by the store's caller (`certOk`: the writer's `End` takes the
certificate of the log it commits before it notifies, `certOkNext`, and the store keeps the
committed log's, `revMuInv`). The certificate is what makes a watch event's revision reached in
the server's model (`etcdReached`: a certified log is the KV model of a committed raft log).
(Stage 2 of the mvcc API, 2026-11-05) its changes fewer than `2 ^ 48` (the receipt against a
store's bound on the receipts, `isStore`'s `Hrb`), so its events are positive (`evLog_pos`); and
a lower bound of the API's notified log (`api.nlLb`: the history the API's client was told of has
it), so that every send's bounds and every watcher's delivery are over one history
(`evLog_nlLb`). -/
def evLog (γ : StoreNames) (L : Log) : IProp GF :=
  iprop(idxSealed γ.idx L ∗ certOk γ L ∗ ⌜logCh L < 2 ^ 48⌝ ∗ api.nlLb γ.api L)

/-- **The store had released `n` revisions** (persistent; D25): a lower bound of `γ.rel`, the
notified log's length under `s.mu`, which `End` bumps before it notifies a revision's events. A
log whose events a watcher was delivered is released (`evsWf`). -/
def relLb (γ : WsNames) (n : Nat) : IProp GF := monoNatLbOwn γ.rel n

/-- **A watcher from `lo` is past its exactness condition** (persistent; per watcher, 2026-11-05:
`notes/mvcc-api-invariants.md` §4.4): a notified log `N` (a lower bound of the API's notified
log) and a compaction revision `c` (the API's lower bound) such that `N`'s revisions `[lo, c]`
change a key twice (`¬ onceUpTo N lo c`). Both only grow, so it holds for good: the watch
guarantee (`wsRecvOk`) states nothing more of the watcher's events. Made by `syncWatchers` when
it reads a watcher's events from the compaction revision `c` and revision `c` changes a key twice
(the backend kept only its last change, `nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`). -/
def doomed (γ : WsNames) (lo : Nat) : IProp GF :=
  iprop(∃ (N : Log) (c : Int), api.nlLb γ.st.api N ∗ api.crevAtLeast γ.st.api c ∗
    ⌜¬ api.onceUpTo N lo c⌝)

/-- The events `evs` are the range's of the revisions `[lo, d)` of a watched log (`evLog`:
sealed and certified; persistent; `d` past the log only for an empty range), or the watcher is
past its exactness condition (`doomed`; per watcher, 2026-11-05: until then exact under the
create token's `watchNoDup`), its events then of revisions from `lo` on (none unless `lo < d`)
and positive (`evPos`: a sub-list of a watched log's, `WatchPos.lean`). -/
def evsWf (γ : WsNames) (r : WatchRange) (lo : Nat) (evs : List EvM) (d : Nat) : IProp GF :=
  iprop(∃ L : Log, evLog γ.st L ∗ relLb γ L.length ∗ ⌜d ≤ L.length ∨ d ≤ lo⌝ ∗
    (⌜evs = watchEvents L r lo d⌝ ∨
      (doomed γ lo ∗ ⌜(evs ≠ [] → lo < d) ∧ ∀ ev ∈ evs, evPos ev⌝)))

/-- Every prefix of the deliveries `D` ends at a revision (persistent): its events, concatenated,
are the range's of the revisions `[lo, d')` of a log the index's history has, for some `d'` (a
delivery is the events of whole revisions: `notify` sends one revision's, `syncWatchers` those
of `[minRev, maxRev)` or up to `moreRev`), so a client that received a prefix of the deliveries
knows up to which revision it has every event. -/
def delivsCut (γ : WsNames) (r : WatchRange) (lo : Nat) (D : List Deliv) : IProp GF :=
  iprop(□ ∀ k : Nat, ⌜k ≤ D.length⌝ -∗
    ∃ d' : Nat, evsWf γ r lo ((D.take k).map Prod.fst).flatten d')

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
    □ (([∗list] dl ∈ D, ∃ fs, filtersImpl fcs fs ∗ api.savedFilters γw.fg fs ∗
        ⌜dl.2 = filtered fs dl.1⌝) ∗
      delivsCut γ r γw.lo D) ∗
    evsWf γ r γw.lo evsw d ∗
    ((⌜closed = false⌝ ∗ dghostVar γw.live (DFrac.own (1 : Qp).half) true) ∨ cancelled γw))

/-- **What the channel knows of a watcher registered on it** (persistent; unit W-M2): its fixed
range's id is one the channel's stream assigned to it (`chanIdAssigned`, made at the
registration by the stream's callback, `isWatchable`), and not `-1`. -/
def chanRegFact (γc : WatchChanNames) (w : Loc) : IProp GF :=
  iprop(∃ (rr : WatchRange) (fcs : GoSlice), watcherFixed w rr fcs ∗ chanIdAssigned γc rr.id w ∗
    ⌜rr.id ≠ W64 (-1)⌝)

/-- **A watcher registered on the channel is in the stream's history** (persistent; 2026-11-05,
the sends' premises): its names, its fixed range, and the registration of its range's id with its
range, filters' name and first revision (`chanRegTok`, minted by `watch_register` right after the
registration callback appended it). What a sender of its responses needs for `factAgree`. -/
def chanRegW (γ : WsNames) (γc : WatchChanNames) (w : Loc) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice), watcherMeta γ w γw ∗
    watcherFixed w r fcs ∗ chanRegTok γc r.id r γw.fg γw.lo)

/-- **What a response covers** (persistent; unit W-K, K1b): for every watcher `w'` it covers
(`x.cov`), on this channel, the responses sent for `w'` before it (`pre`, the sent list before
`x`) are its deliveries `D`'s sent ones, and `D`'s events are the range's of the revisions
`[lo, d)` of a watched log, with `d` past `x`'s revision: `w'` has received every event of its
range up to `x.rev`. -/
def covFact (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (w' : Loc) (rev : w64) :
    IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice) (D : List Deliv) (L : Log) (d : Nat),
    watcherMeta γ w' γw ∗ ⌜γw.wc = γc⌝ ∗ watcherFixed w' r fcs ∗ evLog γ.st L ∗
    □ (∀ dl : Deliv, ⌜dl ∈ D⌝ -∗ ∃ fs, filtersImpl fcs fs ∗ api.savedFilters γw.fg fs ∗
      ⌜dl.2 = filtered fs dl.1⌝) ∗
    (⌜(D.map Prod.fst).flatten = watchEvents L r γw.lo d⌝ ∨ doomed γ γw.lo) ∗
    ⌜(pre.filter (fun y => decide (y.w = w'))).map RespM.evs = (D.filter Deliv.sent).map Prod.snd ∧
      (d ≤ L.length ∨ d ≤ γw.lo) ∧
      sint.Z rev + 1 ≤ (d : Int) ∧ ((d : Int) ≤ sint.Z rev + 1 ∨ d ≤ γw.lo) ∧
      startLo r γw.lo ∧ (γw.lo : Int) ≤ sint.Z rev + 1⌝)

/-- **A watcher cancelled by its stream's client** (persistent; K1b; 2026-11-05, the stream's
history): its fixed range's id was cancelled in the stream's history (`chanCancelTok`). -/
def rsnW (γc : WatchChanNames) (w : Loc) : IProp GF :=
  iprop(∃ (r : WatchRange) (fcs : GoSlice), watcherFixed w r fcs ∗ chanCancelTok γc r.id)

/-- The completeness of a response of id `-1` (K1b): every watcher registered on the channel when
it was sent (`x.regs`) is covered, or cancelled for its reason; and it has no events and its
revision is at least `1` (so the client broadcasts it: `IsProgressNotify`). -/
def respCompl (γc : WatchChanNames) (x : RespM) : IProp GF :=
  iprop(⌜x.id ≠ W64 (-1)⌝ ∨
    ((□ ∀ w : Loc, ⌜w ∈ x.regs⌝ -∗ ⌜w ∈ x.cov⌝ ∨ rsnW γc w) ∗ ⌜1 ≤ sint.Z x.rev ∧ x.evs = []⌝))

/-- **The store had notified `L` (at least)** (persistent; unit W-K): a lower bound of the
notified log (`γ.wlog` is a monotone list, half the lock's, half the sole writer's). -/
def notifiedLb (γ : WsNames) (L : Log) : IProp GF := monoListLbOwn γ.wlog L

/-- **A compaction revision `c` the store permits** (persistent): its compaction permit
(`crevPermAt`, C3's store law) and (stage 2 of the mvcc API, 2026-11-05) a lower bound of the
API's compaction revision (`api.crevAtLeast`: a compaction response's revision at most the
store's, §4.5; `syncWatchers` reads both under `s.revMu`). -/
def cmpPerm (γ : WsNames) (c : Int) : IProp GF :=
  iprop(crevPermAt γ.st c ∗ api.crevAtLeast γ.st.api c)

/-- **A compaction response's revision is permitted** (C3's store law, 2026-11-02): none, or a
positive revision the store's compaction permit holds of (`crevPermAt`; `syncWatchers` reads it
with the revision under `s.revMu`). -/
def cmpPermOf (γ : WsNames) (x : RespM) : IProp GF :=
  iprop(⌜x.compactRev = W64 0⌝ ∨ (⌜0 < sint.Z x.compactRev⌝ ∗ cmpPerm γ (sint.Z x.compactRev)))

/-- **The revision `rev` is one of the API's notified log** (persistent; stage 2 of the mvcc API,
2026-11-05): a lower bound of it (`api.nlLb`) past `rev`. What every response but a compaction
response is sent with (`respRev`): its watch guarantee's `rev < |σ.notifiedLog|`. -/
def revApi (γ : WsNames) (rev : w64) : IProp GF :=
  iprop(∃ N : Log, api.nlLb γ.st.api N ∗ ⌜sint.nat rev < N.length⌝)

/-- **An event-less response's revision** (K2e-5): the notified log's last when it was sent, so
at least every earlier event-less response's on the channel (`pre`). (Only `progressIfSync` sends
one: a victim's batch has events.) A compaction response (watches across a compaction,
2026-11-01) claims no revision: its own (`0`, unset) is at or below every other's. Every response's
compaction revision is permitted (`cmpPermOf`, C3's store law: outside the disjunction, which a
compaction response may satisfy by its second disjunct). (Stage 2 of the mvcc API, 2026-11-05)
a response's revision but a compaction response's is one of the API's notified log (`revApi`). -/
def respRev (γ : WsNames) (pre : List RespM) (x : RespM) : IProp GF :=
  iprop((⌜x.evs ≠ []⌝ ∨ (∃ L : Log, notifiedLb γ L ∗
    ⌜sint.Z x.rev + 1 = (L.length : Int) ∧ ∀ y ∈ pre, y.evs = [] → sint.Z y.rev ≤ sint.Z x.rev⌝) ∨
    ⌜x.compactRev ≠ W64 0 ∧ x.rev = W64 0⌝) ∗ cmpPermOf γ x ∗
    (⌜x.compactRev ≠ W64 0⌝ ∨ revApi γ x.rev))

/-- **What a response sent covers** (K1b): the watchers it covers (`covFact`), its completeness
for an id `-1` (`respCompl`), that an event-less one covers its watcher, and its revision
(`respRev`). A compaction response (watches across a compaction, 2026-11-01: `chooseAll`'s, no
events, revision `0`) covers nothing: it is exempt from covering its watcher, and its
`respRev` is the compaction arm. -/
def respCov (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (x : RespM) : IProp GF :=
  iprop((□ ∀ w' : Loc, ⌜w' ∈ x.cov⌝ -∗ covFact γ γc pre w' x.rev) ∗ respCompl γc x ∗
    ⌜x.evs = [] → x.compactRev = W64 0 → x.w ∈ x.cov⌝ ∗ respRev γ pre x)

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

/-- **The stream's API names** (`api.WsAbs`) of the channel `ch` (names `γc`) of a stream of the
watchable store `γ`. -/
abbrev wsAbsOf (γ : WsNames) (ch : Loc) (γc : WatchChanNames) : api.WsAbs :=
  ⟨γ.st.api, γc.aev, γc.ans, γc.arcv, γc.arx, ch, γc.ch, γc.recv, γc.acl⟩

/-- **Every registration of the stream's history is a watcher registered on the channel**
(persistent; 2026-11-05, the sends' premises): for each `.reg id rg _ _` of the history `l`, a
watcher of the channel's registered set (`γc.reg`) with the fixed range `rg`, whose id is `id`.
What a `-1` response's sender needs for `stampsAt`: every watcher of the stream's state is one of
the channel's, so covered by the response or cancelled (`respCompl`). Only a registration adds to
it (`regWit_app`). -/
def regWit (γc : WatchChanNames) (l : List api.sent.SEv) : IProp GF :=
  iprop(□ ∀ (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat),
    ⌜api.sent.SEv.reg id rg fg lo ∈ l⌝ -∗
    ∃ (w : Loc) (fcs : GoSlice), ghostMapElem γc.reg w DFrac.discard () ∗ watcherFixed w rg fcs ∗
      ⌜id = rg.id⌝)

/-- **The channel invariant's API part** (stage 2 of the mvcc API, the watch chain, 2026-11-05):
the stream's history (`api.chanApiAt`, `Api/StreamSteps.lean`), its sends the responses sent on
the channel (`sent`, as the client sees them), the consumer's view (the invariant's half of
`γc.arcv`) the channel's received prefix (`recv`, as the client sees it); every registration of
the history a watcher registered on the channel (`regWit`, for the `-1` sends' `stampsAt`). -/
def chanApi (γ : WsNames) (ch : Loc) (γc : WatchChanNames) (sent recv : List RespM) : IProp GF :=
  iprop(∃ (l : List api.sent.SEv) (dec : GName → List (EvM → Bool)),
    api.chanApiAt (wsAbsOf γ ch γc) l dec (recv.map RespM.toW) ∗
    ⌜api.sent.sendsOf l = sent.map RespM.toW⌝ ∗ regWit γc l)

/-- **The stream channel `ch`'s invariant** (see the module docstring); unit W-M2: every
registered watcher's `chanRegFact`, and every response of id `-1` sent carries the channel's
progress fact; stage 2 of the mvcc API: its API part (`chanApi`), and every registered watcher's
registration in the stream's history (`chanRegW`, for the sends' `factAgree`). -/
def watchChanInv (γ : WsNames) (ch : Loc) (γc : WatchChanNames) : IProp GF :=
  iprop(∃ (s : ChanState WatchResponse) (sent recv : List RespM) (vs : List WatchResponse)
      (L : List Loc),
    "Hch" ∷ ownChan γc.ch WatchResponse s ∗
    "Hrecv" ∷ ghostVar γc.recv (1 : Qp).half recv ∗
    "%Hpre" ∷ ⌜recv <+: sent⌝ ∗
    "%Hinfl" ∷ ⌜chanInflight s = some vs⌝ ∗
    "#Hvs" ∷ respsIs vs (sent.drop recv.length) ∗
    "Hpk" ∷ respsPk vs (sent.drop recv.length) ∗
    "#Hok" ∷ □ ([∗list] r ∈ sent, respOk r) ∗
    "Hregl" ∷ ghostVar γc.regl (1 : Qp).half L ∗
    "Hcl" ∷ (if chanIsClosed s then ghostVar γc.regl (1 : Qp).half L else iprop(True)) ∗
    "Hreg" ∷ ghostMapAuth γc.reg 1 (regMap L) ∗
    "%Hnd" ∷ ⌜L.Nodup ∧ ∀ x ∈ sent, x.w ∈ L⌝ ∗
    "#Hrf" ∷ □ ([∗list] w ∈ L, chanRegFact γc w) ∗
    "#Hrt" ∷ □ ([∗list] w ∈ L, chanRegW γ γc w) ∗
    "#Hpf" ∷ □ ([∗list] r ∈ sent, ⌜r.id = W64 (-1)⌝ → progFact γc.prog) ∗
    "Hsentl" ∷ sentAuth γ γc sent L ∗
    "Hws" ∷ ([∗list] w ∈ L, chanWatcher γ γc (chanIsClosed s) sent w) ∗
    "Hapi" ∷ chanApi γ ch γc sent recv)

/-- The watcher `w` (names `γw`) is registered on the channel `ch` (persistent): the channel, its
invariant, and `w` in its set of registered watchers. -/
def watcherChan (γ : WsNames) (w : Loc) (γw : WatcherNames) (ch : Loc) : IProp GF :=
  iprop(isChan ch γw.wc.ch WatchResponse ∗ inv watchN (watchChanInv γ ch γw.wc) ∗
    ghostMapElem γw.wc.reg w DFrac.discard ())

/-! ## The lock invariant -/

/-- What the lock knows of a victim's batch `B` (the watcher's first revision `lo`, its state
`st`): the first revision the batch left out, if any, is the watcher's `minRev` (`syncWatchers`
sets it so), and its events are at or above `lo` and below `minRev` (the victims' loop resends
them as of `minRev - 1`). -/
def victimBatchOk (lo : Nat) (st : WatcherSt) (B : EventBatch) : Prop :=
  (B.moreRev ≠ W64 0 → B.moreRev = st.minRev) ∧
  ∀ ev ∈ B.evs, (lo : Int) ≤ sint.Z ev.kv.modRev ∧ sint.Z ev.kv.modRev < sint.Z st.minRev

/-- What the lock knows of a live watcher's population: a synced one is delivered up to `d`, at
or past its `minRev` (and the notified log: `WsOk.synced_d`), with nothing of its range between
its `minRev` and `d` (its events are also those up to its `minRev`: `notify` sets `minRev` past
every revision with an event of the watcher's range; D22 receiver epochs, S6, for
`watchableStore.Restore`, which moves it to the unsynced group delivered up to its `minRev`); an
unsynced one up to its `minRev`, at most the larger of its first revision and a committed log's
length (until S6 below a committed log's length: a watcher `Restore` moves may be ahead of every
committed log, its start revision in the future); a victim's batch completes its delivered events
up to its `minRev` (`victimBatchOk`). -/
def popFacts (γ : WsNames) (σ : WsState) (w : Loc) (r : WatchRange) (lo : Nat) (st : WatcherSt)
    (evsw : List EvM) (d : Nat) : IProp GF :=
  if (σ.Ws !! w).isSome then
    iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ d⌝ ∗ evsWf γ r lo evsw d ∗
      evsWf γ r lo evsw (sint.nat st.minRev))
  else if (σ.Wu !! w).isSome then
    iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev⌝ ∗ evsWf γ r lo evsw d ∗
      (∃ Lc : Log, idxCert γ.st.idx Lc ∗ ⌜sint.nat st.minRev ≤ max lo Lc.length⌝) ∗
      -- (watches across a compaction, 2026-11-01) a compacted watcher left unsynced (`choose`'s
      -- copy branch) is behind a compaction revision, so behind every later one: `syncWatchers`
      -- never syncs it
      (⌜st.compacted = true⌝ → ∃ c0 : Int, crevLb γ.st.idx c0 ∗ ⌜sint.Z st.minRev < c0⌝))
  else match σ.victimOf w with
    | some B => iprop(⌜(lo : Int) ≤ sint.Z st.minRev ∧ d = sint.nat st.minRev ∧
          victimBatchOk lo st B ∧ B.evs ≠ []⌝ ∗
        evsWf γ r lo (evsw ++ B.evs) d)
    | none => iprop(True)

/-- A watcher under the lock (at its fraction `q`): its names and fixed fields; live, its
channel, filters, its start revision at or below its first revision `lo`, the lock's parts of its ghosts and its population's facts; else cancelled. -/
def memberRes (γ : WsNames) (q : Qp) (σ : WsState) (w : Loc) (st : WatcherSt) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs ∗
    if σ.live w then
      watcherChan γ w γw st.ch ∗ watcherFilters γw fcs ∗ ⌜sint.Z r.startRev ≤ (γw.lo : Int)⌝ ∗
      ∃ (evsw : List EvM) (d : Nat), ⌜σ.E !! w = some (evsw, d)⌝ ∗
        monoListAuthOwn γw.evs q.half evsw ∗ dghostVar γw.live (DFrac.own q.half) true ∗
        popFacts γ σ w r γw.lo st evsw d
    else cancelled γw)

/-- A victim out with the mover (the lock's half of its state; persistent facts). -/
def outRes (γ : WsNames) (σ : WsState) (w : Loc) (st : WatcherSt) : IProp GF :=
  iprop(∃ (γw : WatcherNames) (r : WatchRange) (fcs : GoSlice),
    ⌜σ.M !! w = some γw⌝ ∗ watcherMeta γ w γw ∗ watcherFixed w r fcs)

/-- The watcher budget at the fraction `q`, for the watchers with names `M` (every registered
watcher, cancelled or not: `M` only grows): the unspent tokens `n` (the authority's count), with
`M.size + n + 3 ≤ 2 ^ 63`. A registration spends a token and names a watcher; a cancel refunds
nothing. -/
def watchBudget (γ : WsNames) (q : Qp) (M : GMap Loc WatcherNames) : IProp GF :=
  iprop(∃ n : Nat, ownTokAuthDfrac γ.wt (DFrac.own q) n ∗ ⌜GMap.size M + n + 3 ≤ 2 ^ 63⌝)

/-! ### The watch tokens backed by time receipts (D19b's method, 2026-10-18) -/

def watchTokN : Namespace := (nroot .@ "mvcc") .@ "watchTok"

/-- **The watch-token pool** (persistent): an invariant holding, for the `a` tokens taken so
far, `a` time receipts, and the `n` tokens left, with `receiptBound GF ≤ a + n + 1`. A token
costs a receipt of the taker's own Go step (`watchTokPool_take`): `a + 1 < receiptBound GF`, so
some token is left. Allocated from `New`'s `2 ^ 63 - 3` tokens (`watchTokPool_alloc`). -/
def watchTokPool (γ : WsNames) : IProp GF :=
  inv watchTokN iprop(∃ a n : Nat, ⧗ a ∗ ownToks γ.wt n ∗ ⌜receiptBound GF ≤ a + n + 1⌝)

/-- **The notified log's ghosts** at the lock's fraction `q`: `γ.wlog` at it (the lock's alone,
2026-11-06: until then half, the sole writer holding the other half; under `s.mu` the writer's log
is the lock's by the committed log's authority, `wlogQ_auth_agree`) and `s.mu`'s quarter of the
committed log's authority at it (the outer quarter, `logQ`; unit W-K: the commit happens under
`s.mu` after the notify, so a reader under `s.mu` finds every certified log a prefix of the notified
one, `wlogQ_cert_prefix`). -/
def wlogQ (γ : WsNames) (q : Qp) (L : Log) : IProp GF :=
  iprop(monoListAuthOwn γ.wlog q L ∗ idxLogAuth γ.st.idx q.half.half L)

/-- **Vestigial** (per watcher, 2026-11-05): was "no watcher, or no compactor or no duplicate keys"
(`watchNoDup`, M2's F1 and watches across a compaction), which `syncWatchers` took to read exactly;
now each watcher's delivery is exact or `doomed` (`evsWf`), so nothing is needed and the
registration takes no such fact (the frozen `Watch` contract gives none). Kept as `True` in the
lock's body until a cleanup removes the conjunct from its users. -/
def wsWatchFrozen (_γ : WsNames) (_σ : WsState) : IProp GF := iprop(True)

/-- The lock invariant at the state `σ` and the fraction `q`. -/
def watchStoreBody (s : Loc) (γ : WsNames) (q : Qp) (σ : WsState) : IProp GF :=
  iprop("Hσ" ∷ ghostVar γ.wst q σ ∗
    "Hwlog" ∷ wlogQ γ q σ.Lmu ∗
    "#Hcert" ∷ idxCert γ.st.idx σ.Lmu ∗
    "#Hwfz" ∷ wsWatchFrozen γ σ ∗
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

/-- **The watchable store's lock's part of the API's ghost state** (the mvcc API, stage 1, strict
M1; `notes/mvcc-api-invariants.md` §1) at fraction `q`: a quarter of `q` of the pending revision,
at `none` (2026-11-05: the watchable `End` notifies and commits under `s.mu`, so no revision is
pending while the lock is free; what `Watch`'s update needs at the registration); and a lower bound of the API's notified log at `Lmu`
(stage 2, per watcher, 2026-11-05: what a doomed watcher's witness and a send's bound take; minted
with the client's authority where the notified log grows, `New`'s and `End`'s notify step). -/
def wsSlot (γ : WsNames) (q : Qp) (Lmu : Log) : IProp GF :=
  iprop(api.pndPart γ.st.api q.half.half none ∗ api.nlLb γ.st.api Lmu)

/-- **The lock's parts at the notified log `Lmu`** (D25; the mvcc API, stage 1): the released
length's authority at `Lmu`'s length, and the API's slot (`wsSlot`). -/
def relAuth (γ : WsNames) (q : Qp) (Lmu : Log) : IProp GF :=
  iprop(monoNatAuthOwn γ.rel q Lmu.length ∗ wsSlot γ q Lmu)

/-- **The watchable store's share of its inner store's fields** (D22 receiver epochs, S3,
2026-10-22): `syncWatchers` reads `s.store.b` under the watchable store's `s.mu` and the inner
store's `s.revMu`, not the inner store's `s.mu` (and `store.Restore`, called by
`watchableStore.Restore` under the watchable store's `s.mu`, writes it before taking `s.revMu`):
the quarter `NewStore` returns (`fieldShare`), at the lock's fraction; and (S5a) the watchable
store's deposit ghost at the fraction (`StoreNames.wsd`: `syncWatchers` deposits it in the
readers' pool while it has a slot out, `readerPool_checkout_ws`). -/
def wsFields (s : Loc) (γ : WsNames) (q : Qp) : IProp GF :=
  iprop(∃ st : Loc, s.[watchableStore, go!"store"] ↦□ st ∗ fieldShare st γ.st q.half.half ∗
    ghostVar γ.st.wsd q ())

/-- **The lock invariant** of `s.mu` (see the module docstring); D25: with the released length's
authority at the notified log's length (`End` bumps it before notifying, inside its critical
section); D22 receiver epochs, S3: with the share of the inner store's fields (`wsFields`). -/
def watchStoreInv (s : Loc) (γ : WsNames) (q : Qp) : IProp GF :=
  iprop(∃ σ : WsState, watchStoreBody s γ q σ ∗ relAuth γ q σ.Lmu ∗
    wsFields s γ q ∗ ⌜σ.settled ∧ σ.srBelow σ.Lmu.length ∧ σ.unsRst⌝)

/-! ## The store -/

-- `isStopChan`: `InvStore.lean` (2026-10-13: the store's stop channel uses it too).

/-- **The watchable store** `s` over the store `st` (persistent): the inner store and its read
view (`newWatchableStore` points it at `s`: unit 3b; `rev()` reads through it) and write view (at
`s` too: `Put`/`DeleteRange`), the lock's guard, the victims' wake-up
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
    -- (M4, track B, 2026-11-06) the inner store's write view, over `s` (`KV.Put`/`DeleteRange`)
    "#HwvW" ∷ (∃ wv : Loc, st.[store, go!"WriteView"] ↦□
        (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
      wv.[writeView, go!"kv"] ↦□
        (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s : GoInterface)) ∗
    "#Hmu" ∷ sync.isRWMutexGuard (wsMuAddr s) (watchStoreInv s γ) ∗
    "#Hvc" ∷ s.[watchableStore, go!"victimc"] ↦□ vc ∗
    "#Hvcb" ∷ isChanBag (V := Unit) γv vc (fun _ => iprop(True)) ∗
    "#Hstopc" ∷ s.[watchableStore, go!"stopc"] ↦□ stc ∗
    "#Hstop" ∷ isStopChan stc ∗
    -- (M2, `notes/m2-plan.md`, S1) the inner store never compacted, as `newWatchableStore` makes
    -- it (`crevFrozen_alloc`): what `syncWatchers`' snapshot (`rangeEvents`) needs, which until M2
    -- the store's reader carried; (M2, the storage side, P3) by the mode: in compaction mode not
    -- (`wsFrozenM`), and `syncWatchers` finds it with a watcher instead (`wsWatchFrozen`)
    "#Hfrz" ∷ wsFrozenM γ.st ∗
    "%Hwq" ∷ ⌜γ.st.watchQ = true⌝)

/-! ## The write transaction -/

end reprs

end mvcc
end EtcdGrove
end Perennial
