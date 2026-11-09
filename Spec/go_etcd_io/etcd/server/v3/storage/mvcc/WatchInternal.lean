/-
# mvcc's watchable store: internal vocabulary (batch 3f)

What the specs of the watchable store's internal functions (`watchable_store.go`'s helpers and
loops, `watcher_group.go`) are stated over. No client of mvcc sees these names: the exported specs
are over `ApiWatch.lean`'s. Internal helpers' specs mirror their code (PRINCIPLES, "Scope").

## The store's invariant and its lock

* `wsInv s γ` (persistent): the watchable store `s` of `γ`: `watchableAt`'s realization
  (`wsInv_watchableAt`). Its lock `s.mu` holds the two groups (`synced`, `unsynced`, each
  `wgOwn` of its watchers with their ranges), the victims (a list of watcher batches), each live
  watcher's record (`wRecAt`: `minRev`, `victim`, `compacted`, `restore`, `ch`) and its stream's
  send right; the store's notified history (`mvccLb`'s authority, 3e's half of `mvccState`'s
  agreement) moves only under it. The relations it keeps: a synced watcher's events of the
  revisions below its `minRev` are all sent and it has no event between its `minRev` and the notified
  revision (its `minRev` may stay at its registration's while it gets no event: a progress does not
  raise it), an unsynced one's below its `minRev` too and its `minRev` at most the current revision
  (but with `restore`); the events position of every watcher (`posEvOf` of its sent responses) is
  below its `minRev`, a victim's are sent but its batch's, which `moveVictims` resends;
  every sent response carries `wsRespOk`.
* `wsMu s γ` (exclusive): **the lock's contents, held** (`s.mu.Lock` gives it, `Unlock` takes it):
  what `notify`, `addVictim`, `chooseAll`/`choose` and the loops' locked sections read and write.
* `wsLoopS s γ`, `wsLoopV s γ` (exclusive): the loops' shares: the stop channel's receive, the wait
  group's `Done` (its deposit: the share itself, given back at `Close`), the loop's reader of the
  store (the right to borrow, per pass and under `s.mu`, one of the store's own reader slots of its
  **current** storage, 3e's `mvccOwnN`: not held for the loop's life, since a `Restore` (under
  `s.mu`, between passes) gives the old storage's slots back, `storageRest B mvccReaderN`; the
  borrowing law is 3e's internal one, requested at integration), and for `syncVictimsLoop` the
  victim channel's receive.

## Data structures (models mirror the code)

* `watcherAt w ι id W` (persistent): `w` is a `*watcher` of the stream `ι`, id `id`, registered as
  `W`: its read-only fields (`key`, `end`, `startRev`, `id`, `fcs` with `filtersAt`).
* `wRecAt w r` (exclusive): the watcher's mutable fields (`WRec`), the lock's.
* `wsetOwn m S` (exclusive): the `watcherSet` map `m` holds the watchers `S` (a list without
  duplicates, its order irrelevant: `wsetOwn_perm`).
* `wskOwn m K` (exclusive): the `watcherSetByKey` map holds, for each key, the watchers `K` lists
  with that key (no empty set is kept).
* `wgOwn v dq G` (fractional): the `watcherGroup` value `v` holds the watchers `G` with their ranges
  (its key watchers' map, its interval tree of range watchers' sets, its set of all), at `dq`.
* `wsIdFree ι id`, `wsMapAt m ι`: the stream's side of a registration (its fresh id, its map).
* `wsSendable w r`, `wsCmpSendable w cr` (exclusive): the response `r` of `w` (its compaction
  response at `cr`) may be sent now (its facts hold).
* `wsReadAt s γ b lg h` (exclusive): `s.mu` and a storage reader held, the storage's image of `h`.
* `ebOwn eb E`, `wbOwn wb B` (exclusive): an `*eventBatch` holding the batch `E` (`EBatch`: its
  events, owned (`evOwn`), its distinct revisions, the first revision left out); a `watcherBatch`
  holding a batch for each watcher of `B`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## Models -/

/-- **A watcher's mutable record** (`*watcher`'s fields the store writes under `s.mu`). -/
structure WRec where
  minRev : Int
  victim : Bool
  compacted : Bool
  restore : Bool
  ch : GoChan

/-- `watchBatchMaxRevs` (`watch_init.spec`). -/
def watchBatchMaxRevsN : Nat := 1000

/-- **An event batch** (`eventBatch`): its events, its distinct revisions, the first revision left
out (`0`: none). -/
structure EBatch where
  evs : List EvM
  revs : Nat
  moreRev : Int

def EBatch.empty : EBatch := ⟨[], 0, 0⟩

/-- `eventBatch.add`: a batch already past `watchBatchMaxRevs` revisions takes nothing; else the
event is appended, unless it starts a revision past the limit (then `moreRev` is that revision). -/
def EBatch.add (b : EBatch) (e : EvM) : EBatch :=
  if watchBatchMaxRevsN < b.revs then b
  else match b.evs.getLast? with
    | none => { b with evs := [e], revs := 1 }
    | some y =>
      if sint.Z y.kv.modRevision < sint.Z e.kv.modRevision then
        (if watchBatchMaxRevsN < b.revs + 1 then
           { b with revs := b.revs + 1, moreRev := sint.Z e.kv.modRevision }
         else { b with evs := b.evs ++ [e], revs := b.revs + 1 })
      else { b with evs := b.evs ++ [e] }

/-- A watcher batch: the batch of each watcher (`none`: not in it). -/
abbrev WBatch := Loc → Option EBatch

/-- `watcherBatch.add`. -/
def WBatch.add (B : WBatch) (w : Loc) (e : EvM) : WBatch :=
  fun w' => if w' = w then some ((B w).getD EBatch.empty |>.add e) else B w'

/-- **`newWatcherBatch`'s result** over the group `G` (watchers with ranges) and their `minRev`s,
of the events `evs` in order: each watcher of an event's key with `minRev` at most its revision
gets (a copy of) it. -/
def wbOf (G : List (Loc × MRange)) (minRev : Loc → Int) (evs : List EvM) : WBatch :=
  evs.foldl (fun B e =>
    G.foldl (fun B' x =>
      if x.2.watchMem e.kv.key ∧ minRev x.1 ≤ sint.Z e.kv.modRevision then B'.add x.1 e else B') B)
    (fun _ => none)

/-- The least `minRev` of the members of `G` not behind the compaction revision `cr` (`chooseAll`'s
result; `math.MaxInt64` for none). -/
def minRevOf (R : Loc → WRec) (G : List (Loc × MRange)) (cr : Int) : Int :=
  (G.filter (fun x => decide (cr ≤ (R x.1).minRev))).foldl (fun m x => min m (R x.1).minRev)
    (2 ^ 63 - 1)

/-- The event a storage entry (its revision key, 3e's `revOfBytes`, and its key-value, 3e's
`kvBytes`) stands for: a tombstone a
delete, with the revision patched in (`kvsToEvents`). -/
def entryEv (rev : Nat) (tomb : Bool) (m : KeyValueM) : EvM :=
  if tomb then { del := true, kv := { m with modRevision := W64 rev } } else { del := false, kv := m }

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

open go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The watchable store `s` of `γ`** (persistent). -/
opaque wsInv (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **The contents of `s.mu`, held** (exclusive). -/
opaque wsMu (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- The share of `syncWatchersLoop` (exclusive). -/
opaque wsLoopS (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- The share of `syncVictimsLoop` (exclusive). -/
opaque wsLoopV (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **`w` is a watcher of the stream `ι`, id `id`, registered as `W`** (persistent). -/
opaque watcherAt (w : Loc) (ι : WsNames) (id : w64) (W : WatcherM) : IProp GF := iprop(True)

/-- **No registration of `id` on the stream `ι` yet** (exclusive; the stream's invariant gives it
for an id the stream's `Watch` chose, under `ws.mu`). -/
opaque wsIdFree (ι : WsNames) (id : w64) : IProp GF := iprop(True)

/-- **The stream's `watchers` map `m`** (held under `ws.mu`): each entry a watcher of the stream
registered, not removed by its `Cancel`. -/
opaque wsMapAt (m : GoMap) (ι : WsNames) : IProp GF := iprop(True)

/-- **The response `r` of the watcher `w` may be sent now** on its stream's channel (exclusive):
its facts (`wsRespOk`, after filtering by the watcher's filters) hold at the send; what the lock's
contents give `notify`, `syncWatchers` and `chooseAll` for each response they build, and a victim
batch carries for `moveVictims`. -/
opaque wsSendable (w : Loc) (r : WResp) : IProp GF := iprop(True)

/-- **The compaction response at `cr` of the watcher `w` may be sent now** (exclusive): `cr` is the
store's compaction revision (at most the notified history's) and above `w`'s `minRev`, so above its
events position + 1. -/
opaque wsCmpSendable (w : Loc) (cr : w64) : IProp GF := iprop(True)

/-- **The caller holds `s.mu` and a reader of the store's storage `b`**, whose image is of the
notified history `h` (nothing pending), with the store's logger `lg`. -/
opaque wsReadAt (s : Loc) (γ : MvccName) (b : GoInterface) (lg : Loc) (h : KVHist) : IProp GF :=
  iprop(True)

/-- The watcher's mutable record (exclusive). -/
opaque wRecAt (w : Loc) (r : WRec) : IProp GF := iprop(True)

/-- **The `watcherSet` map `m` holds `S`** (exclusive). -/
opaque wsetOwn (m : GoMap) (dq : DFrac) (S : List Loc) : IProp GF := iprop(True)

/-- **The `watcherSetByKey` map `m` holds, per key, the watchers `K` lists** (exclusive). -/
opaque wskOwn (m : GoMap) (K : Key → List Loc) : IProp GF := iprop(True)

/-- **The `watcherGroup` value `v` holds the watchers `G`** with their ranges, at `dq`. -/
opaque wgOwn (v : watcherGroup) (dq : DFrac) (G : List (Loc × MRange)) : IProp GF := iprop(True)

/-- **The `*eventBatch` `eb` holds `E`** (its events owned). -/
opaque ebOwn (eb : Loc) (E : EBatch) : IProp GF := iprop(True)

/-- **The `watcherBatch` `wb` holds `B`** (`nil` holds the empty one). -/
opaque wbOwn (wb : GoMap) (B : WBatch) : IProp GF := iprop(True)

/-! ## Laws (internal) -/

def wsInv_watchableAt.spec : Prop := ∀ s γ,
  wsInv (GF := GF) s γ ⊣⊢ watchableAt (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s) γ

def wsInv_persistent.spec : Prop :=
  (∀ s γ, Persistent (wsInv (GF := GF) s γ)) ∧ (∀ w ι id W, Persistent (watcherAt (GF := GF) w ι id W))

/-- A set's order is irrelevant; so is a group's. -/
def wsetOwn_perm.spec : Prop :=
  (∀ m dq (S S' : List Loc), S.Perm S' → wsetOwn (GF := GF) m dq S ⊢ wsetOwn m dq S') ∧
  (∀ v dq (G G' : List (Loc × MRange)), G.Perm G' → wgOwn (GF := GF) v dq G ⊢ wgOwn v dq G')

/-- A set and a group have no duplicate watcher. -/
def wsetOwn_nodup.spec : Prop :=
  (∀ m dq S, wsetOwn (GF := GF) m dq S ⊢ ⌜S.Nodup⌝) ∧
  (∀ v dq G, wgOwn (GF := GF) v dq G ⊢ ⌜(G.map Prod.fst).Nodup⌝)

def wgOwn_fractional.spec : Prop := ∀ v G (d1 d2 : DFrac),
  wgOwn (GF := GF) v (d1 • d2) G ⊣⊢ wgOwn v d1 G ∗ wgOwn v d2 G

end res

end Mvcc
end EtcdGrove
end Perennial
