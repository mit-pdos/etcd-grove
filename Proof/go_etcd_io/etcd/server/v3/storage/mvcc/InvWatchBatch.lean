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

**Representation.** An event is a persistent fact of its pointer (`evIs`: its fields, the
key-value read-only for good, `kvPtrFixed`): events are shared by the batches of all watchers.
`ownEventBatch eb B` owns the batch struct and its slice; `ownWatcherBatch wb Bm` the map and
each batch. The members' mutable fields are the caller's (`ownStates ST`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchGroup
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

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

/-- `&eventBatch{}`. -/
def EventBatch.empty : EventBatch := ⟨[], W64 0, W64 0⟩

/-- `watchBatchMaxRevs` (a package `var`, never written by the verified code: `mvccInit`). -/
def watchBatchMaxRevsV : w64 := W64 1000

/-- `eventBatch.add`, exactly (signed comparisons): past the cap nothing; the first event
starts the batch with one revision; a higher mod revision than the last event's counts a
revision, and if that passes the cap the event is dropped and `moreRev` records its revision;
else the event is appended. -/
def ebAdd (eb : EventBatch) (ev : EvM) : EventBatch :=
  if sint.Z watchBatchMaxRevsV < sint.Z eb.revs then eb
  else match eb.evs.getLast? with
    | none => { evs := [ev], revs := W64 1, moreRev := eb.moreRev }
    | some last =>
      if sint.Z last.kv.modRev < sint.Z ev.kv.modRev then
        if sint.Z watchBatchMaxRevsV < sint.Z (eb.revs + W64 1) then
          { eb with revs := eb.revs + W64 1, moreRev := ev.kv.modRev }
        else { evs := eb.evs ++ [ev], revs := eb.revs + W64 1, moreRev := eb.moreRev }
      else { eb with evs := eb.evs ++ [ev] }

/-- The member `w` has a state, and the event's mod revision is at or above its `minRev`. -/
def minRevLe (ST : GMap Loc WatcherSt) (ev : EvM) (w : Loc) : Bool :=
  match ST !! w with
  | some st => decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev)
  | none => false

/-- A member's batch: the fold of `ebAdd` over the events its range holds at or above its
`minRev`; `none` if there is none. -/
def memberBatch (r : WatchRange) (st : WatcherSt) (evs : List EvM) : Option EventBatch :=
  evs.foldl (fun ob ev =>
    if r.covers ev.kv.key && decide (sint.Z st.minRev ≤ sint.Z ev.kv.modRev) then
      some (ebAdd (ob.getD .empty) ev)
    else ob) none

/-- `newWatcherBatch`: the batch of each member (of `W`, with its state in `ST`) that gets an
event. -/
def batchOf (W : GMap Loc WatchRange) (ST : GMap Loc WatcherSt) (evs : List EvM) :
    GMap Loc EventBatch :=
  ⟨fun w => match W.lookup w, ST.lookup w with
    | some r, some st => memberBatch r st evs
    | _, _ => none,
   by
    obtain ⟨l, hl⟩ := W.finite
    refine ⟨l, fun k h => hl k ?_⟩
    revert h
    cases W.lookup k <;> simp⟩

theorem batchOf_lookup (W : GMap Loc WatchRange) (ST : GMap Loc WatcherSt) (evs : List EvM)
    (w : Loc) :
    batchOf W ST evs !! w = (match W !! w, ST !! w with
      | some r, some st => memberBatch r st evs
      | _, _ => none) := rfl

theorem batchOf_nil (W : GMap Loc WatchRange) (ST : GMap Loc WatcherSt) : batchOf W ST [] = ∅ := by
  refine GMap.ext (fun w => ?_)
  show (batchOf W ST [] !! w) = none
  rw [batchOf_lookup]
  cases W !! w <;> cases ST !! w <;> rfl

/-- One event added to the batches of the members `D`, in order, whose `minRev` it reaches
(`watcherBatch.add`, in `newWatcherBatch`'s inner loop). -/
def batchStepL (ST : GMap Loc WatcherSt) (ev : EvM) (D : List Loc) (Bm : GMap Loc EventBatch) :
    GMap Loc EventBatch :=
  D.foldl (fun Bm w =>
    if minRevLe ST ev w then <[w := ebAdd ((Bm !! w).getD .empty) ev]> Bm else Bm) Bm

/-- The order of the members does not matter. -/
theorem batchStepL_lookup (ST : GMap Loc WatcherSt) (ev : EvM) (D : List Loc)
    (Bm : GMap Loc EventBatch) (hnd : D.Nodup) (w : Loc) :
    batchStepL ST ev D Bm !! w =
      if w ∈ D ∧ minRevLe ST ev w = true then some (ebAdd ((Bm !! w).getD .empty) ev)
      else Bm !! w := by
  induction D generalizing Bm with
  | nil => simp [batchStepL]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    unfold batchStepL at ih ⊢
    rw [List.foldl_cons, ih _ hnd.2]
    by_cases hwx : w = x
    · subst hwx
      have : ¬ w ∈ xs := hnd.1
      by_cases hc : minRevLe ST ev w = true
      · simp [this, hc]
      · simp [this, hc]
    · have hl : (if minRevLe ST ev x = true then
            <[x := ebAdd ((Bm !! x).getD .empty) ev]> Bm else Bm) !! w = Bm !! w := by
        split
        · exact GMap.lookup_insert_ne _ _ (Ne.symm hwx)
        · rfl
      rw [hl]
      have hiff : (w ∈ xs ∧ minRevLe ST ev w = true) ↔
          (w ∈ x :: xs ∧ minRevLe ST ev w = true) := by
        simp [hwx]
      by_cases hin : w ∈ xs ∧ minRevLe ST ev w = true
      · rw [ite_eq_left hin, ite_eq_left (hiff.1 hin)]
      · rw [ite_eq_right hin, ite_eq_right (fun h => hin (hiff.2 h))]

/-- The members holding the event's key, in any order: the batches of the events so far and
this one. -/
theorem batchOf_snoc (W : GMap Loc WatchRange) (ST : GMap Loc WatcherSt) (evs : List EvM)
    (ev : EvM) (D : List Loc) (hnd : D.Nodup)
    (hD : ∀ w, w ∈ D ↔ (membersBy W (·.covers ev.kv.key) !! w).isSome) :
    batchStepL ST ev D (batchOf W ST evs) = batchOf W ST (evs ++ [ev]) := by
  refine GMap.ext (fun w => ?_)
  show batchStepL ST ev D (batchOf W ST evs) !! w = batchOf W ST (evs ++ [ev]) !! w
  rw [batchStepL_lookup _ _ _ _ hnd, batchOf_lookup, batchOf_lookup]
  have hD' := hD w
  rw [mem_membersBy] at hD'
  unfold memberBatch minRevLe
  cases hW : W !! w with
  | none =>
    have : w ∉ D := by rw [hD']; simp [hW]
    simp [this]
  | some r =>
    cases hS : ST !! w with
    | none => simp
    | some st =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hc : r.covers ev.kv.key = true <;>
        by_cases hm : sint.Z st.minRev ≤ sint.Z ev.kv.modRev <;> simp [hD', hW, hc, hm]

/-- The least `minRev` of the members `D` (signed), from `math.MaxInt64` (`chooseAll`). -/
def minRevStep (ST : GMap Loc WatcherSt) (m : Int) (w : Loc) : Int :=
  match ST !! w with
  | some st => min m (sint.Z st.minRev)
  | none => m

def minRevL (ST : GMap Loc WatcherSt) (D : List Loc) : Int :=
  D.foldl (minRevStep ST) (2 ^ 63 - 1)

/-- The least `minRev` of the members `S` (signed), `2^63 - 1` (`math.MaxInt64`) if none. -/
def minRevOf (ST : GMap Loc WatcherSt) (S : GMap Loc Unit) : Int :=
  minRevL ST S.domList

/-- The order of the members does not matter. -/
theorem minRevL_eq (ST : GMap Loc WatcherSt) (S : GMap Loc Unit) (D : List Loc) (hnd : D.Nodup)
    (hD : ∀ w, w ∈ D ↔ (S !! w).isSome) : minRevL ST D = minRevOf ST S := by
  unfold minRevOf minRevL
  apply List.Perm.foldl_eq'
  · rw [List.perm_ext_iff_of_nodup hnd (GMap.nodup_dom_list S)]
    intro a; rw [hD, GMap.mem_dom_list]
  · intro x _ y _ z
    unfold minRevStep
    cases ST !! x <;> cases ST !! y <;> simp only <;> omega

theorem minRevL_snoc (ST : GMap Loc WatcherSt) (D : List Loc) (w : Loc) :
    minRevL ST (D ++ [w]) = minRevStep ST (minRevL ST D) w := by
  unfold minRevL; rw [List.foldl_append]; rfl

/-- The first `n` members of a list, as a submap of `W`. -/
def takeMembers (W : GMap Loc WatchRange) (keys : List Loc) (n : Nat) : GMap Loc WatchRange :=
  GMap.filter (fun k _ => decide (k ∈ keys.take n)) W

theorem takeMembers_zero (W : GMap Loc WatchRange) (keys : List Loc) :
    takeMembers W keys 0 = ∅ := by
  refine GMap.ext (fun k => ?_)
  unfold takeMembers
  simp [GMap.lookup_filter]

theorem takeMembers_subseteq (W : GMap Loc WatchRange) (keys : List Loc) (n : Nat) :
    takeMembers W keys n ⊆ W := GMap.map_filter_subseteq _ _

theorem takeMembers_succ (W : GMap Loc WatchRange) (keys : List Loc) (n : Nat) (key : Loc)
    (r : WatchRange) (hkey : keys[n]? = some key) (hnd : keys.Nodup) (hW : W !! key = some r) :
    takeMembers W keys (n + 1) = <[key := r]> (takeMembers W keys n) ∧
      takeMembers W keys n !! key = none := by
  have htake : keys.take (n + 1) = keys.take n ++ [key] := by
    rw [List.take_add_one, hkey]; rfl
  have hnot : key ∉ keys.take n := by
    intro hm
    obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
    rw [List.getElem_take] at hjk
    have hj' : keys[j]? = some key := by
      rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
    have := list_nodup_getElem?_inj keys hnd j n key hj' hkey
    simp at hj; omega
  constructor
  · refine GMap.ext (fun k => ?_)
    show takeMembers W keys (n + 1) !! k = <[key := r]> (takeMembers W keys n) !! k
    unfold takeMembers
    rw [htake]
    by_cases hk : k = key
    · subst hk
      simp [GMap.lookup_filter, hW]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
      simp [GMap.lookup_filter, hk]
  · unfold takeMembers
    simp [GMap.lookup_filter, hnot]

/-! ## Ownership -/

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

instance kvPtrFixed_persistent (p : Loc) (kv : EtcdKv) :
    Persistent (kvPtrFixed (GF := GF) p kv) := by
  unfold kvPtrFixed; infer_instance

/-- A key-value points-to as the fields the watchers read (`Key`, `ModRevision`). -/
theorem kv_fields (l : Loc) (v : go_etcd_io.etcd.api.v3.mvccpb.KeyValue) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[go_etcd_io.etcd.api.v3.mvccpb.KeyValue, go!"Key"] ↦{dq} v.Key' ∗
        l.[go_etcd_io.etcd.api.v3.mvccpb.KeyValue, go!"ModRevision"] ↦{dq} v.ModRevision' := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe Key ModRevision

/-- An event points-to as its fields `Type`, `Kv`, `PrevKv`. -/
theorem event_fields (l : Loc) (v : go_etcd_io.etcd.api.v3.mvccpb.Event) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Type"] ↦{dq} v.Type' ∗
        l.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Kv"] ↦{dq} v.Kv' ∗
        l.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"PrevKv"] ↦{dq} v.PrevKv' := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  simp only [named]
  icases H with ⟨-, HT, HK, HP, -⟩
  iframe HT HK HP

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

instance evIs_persistent (e : Loc) (ev : EvM) : Persistent (evIs (GF := GF) e ev) := by
  unfold evIs
  cases ev.prevKv <;> infer_instance

/-- The batch at `eb` holds `B`: its fields, its slice of events (owned, with its capacity),
each event's pointer `evIs` of its model; at the fraction `q` (a victim batch, under the
watchable store's lock). -/
def ownEventBatch (eb : Loc) (B : EventBatch) (q : Qp := 1) : IProp GF :=
  iprop(∃ (s : GoSlice) (ps : List Loc),
    typedPointsto eb ({ evs' := s, revs' := B.revs, moreRev' := B.moreRev } : eventBatch)
      (DFrac.own q) ∗
    ownSlice s ps (DFrac.own q) ∗ ownSliceCap Loc s (DFrac.own q) ∗ ⌜ps.length = B.evs.length⌝ ∗
    [∗list] x ∈ ps.zip B.evs, evIs x.1 x.2)

/-- The watcher batch `wb` (a `map[*watcher]*eventBatch`) holds `Bm`: each member's batch,
owned, at a non-nil pointer. -/
def ownWatcherBatch (wb : GoMap) (Bm : GMap Loc EventBatch) (q : Qp := 1) : IProp GF :=
  iprop(∃ PB : GMap Loc (Loc × EventBatch),
    ownMap wb (DFrac.own q) (GMap.fmap Prod.fst PB) ∗ ⌜Bm = GMap.fmap Prod.snd PB⌝ ∗
    [∗map] _w ↦ p ∈ PB, ⌜p.1 ≠ null⌝ ∗ ownEventBatch p.1 p.2 q)

/-- A watcher batch or `nil` (empty). -/
def ownWatcherBatchOpt (wb : GoMap) (Bm : GMap Loc EventBatch) : IProp GF :=
  iprop(⌜wb = map.nil ∧ Bm = ∅⌝ ∨ ownWatcherBatch wb Bm)

/-- The members' mutable fields (the caller's: the store's, or a batch's). -/
def ownStates (ST : GMap Loc WatcherSt) : IProp GF :=
  iprop([∗map] w ↦ st ∈ ST, watcherOwn w st)

/-- The group's all-watchers set, lent (to iterate it): the group's struct and the set, and
the group back from them. -/
theorem ownWatcherGroup_watchers (wg : Loc) (W : GMap Loc WatchRange) :
    ownWatcherGroup (GF := GF) wg W ⊢
      ∃ v : watcherGroup, wg ↦ v ∗ ownWatcherSet v.watchers' (domSet W) ∗
        (wg ↦ v -∗ ownWatcherSet v.watchers' (domSet W) -∗ ownWatcherGroup wg W) := by
  iintro Hg
  unfold ownWatcherGroup
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iexists _
  iframe Hwg Hws
  iintro Hwg Hws
  iexists km, ws, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact HL

end reprs

end mvcc
end EtcdGrove
end Perennial
