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
the history ring) and of a monotone counter on `latest.rev` (`γ.rev`), and half of `q` of
a ghost variable holding the abstract state (`γ.state`). The other half of the ghost
variable is the single writer's (`storeWriter`, with the exclusively owned latest tree:
only the writer reads or writes `latest.tree`). `storeRevLb γ r` is a persistent lower
bound on `latest.rev`. `RWMutex` admits a bounded number of readers, so every reader holds
a token (`storeReader`, an `ownRWMutex`): `newStore` hands out all but the writer's.

Models of the methods: `snapModel` (`getSnapshot`), `kvRange` (`snapshot.Range`),
`applyEvents`/`applyResp` (`Apply`), `restoreState` (`Restore`).
-/
import EtcdGrove.Cache.InvBtree
import EtcdGrove.Cache.InvRingBuffer
import Perennial.Ghost.GhostVar
import Perennial.Ghost.MonoNat

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

/-! ## Predicates -/

/-- The ghost names of a store. -/
structure StoreNames where
  /-- the abstract state (`ghostVar`, half in the lock, half the writer's) -/
  state : GName
  /-- `latest.rev`, monotone (`monoNat`, in the lock) -/
  rev : GName

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

/-- The latest tree, owned by the writer: `s.latest.tree` is a tree holding `m`. -/
def storeLatestTree (s : Loc) (m : KvMap) : IProp GF :=
  iprop(∃ t : Loc, storeLatestTreeAddr s ↦ t ∗
    ownBTree kvItemPtrT t (kvItemIs (hG := hG)) kvLess m (DFrac.own 1) ∗ kvsAt m)

/-- What the writer holds while it holds the write lock (`applyEventsLocked`,
`applyProgressNotifyLocked`): the latest revision, the history ring and the latest
tree. -/
def storeLockedPhys (s : Loc) (cap : Nat) (st : StoreState) : IProp GF :=
  iprop(storeLatestRevAddr s ↦ st.latestRev ∗
    ownRingBuffer (storeHistAddr s) cap (snapIs (hG := hG)) Prod.fst st.history ∗
    storeLatestTree s st.latest)

/-- The lock invariant `P q` of `s.mu` (see the module docstring). -/
def storeLockInv (s : Loc) (γ : StoreNames) (cap : Nat) (q : Qp) : IProp GF :=
  iprop(∃ st : StoreState,
    "Hst" ∷ ghostVar γ.state q.half st ∗
    "Hrev" ∷ monoNatAuthOwn γ.rev q (sint.nat st.latestRev) ∗
    "HlatestRev" ∷ storeLatestRevAddr s ↦{DFrac.own q} st.latestRev ∗
    "Hhist" ∷ ownRingBuffer (storeHistAddr s) cap (snapIs (hG := hG)) Prod.fst st.history (DFrac.own q) ∗
    "%Hinv" ∷ ⌜StoreInv cap st⌝)

instance storeLockInv_fractional (s : Loc) (γ : StoreNames) (cap : Nat) :
    Fractional (storeLockInv (GF := GF) s γ cap) where
  fractional q1 q2 := by
    have hrev : ∀ r : w64, (storeLatestRevAddr s ↦{DFrac.own (q1 + q2)} r : IProp GF) ⊣⊢
        storeLatestRevAddr s ↦{DFrac.own q1} r ∗ storeLatestRevAddr s ↦{DFrac.own q2} r :=
      fun r => (typedPointsto_dfractional (GF := GF) _ r).dfractional (DFrac.own q1) (DFrac.own q2)
    have hring := fun (hs : List (w64 × KvMap)) =>
      (ownRingBuffer_fractional (GF := GF) (storeHistAddr s) cap (snapIs (hG := hG)) Prod.fst hs).fractional q1 q2
    have hmono := fun (n : Nat) => (monoNatAuthOwn_fractional (GF := GF) γ.rev n).fractional q1 q2
    have hgv := fun (st : StoreState) =>
      (ghostVar_fractional (GF := GF) γ.state st).fractional q1.half q2.half
    refine ⟨?_, ?_⟩
    · iintro H
      unfold storeLockInv
      iNamed H
      rw [qp_half_add] at *
      icases (hgv st).1 $$ Hst with ⟨Hst1, Hst2⟩
      icases (hmono _).1 $$ Hrev with ⟨Hrev1, Hrev2⟩
      icases (hrev _).1 $$ HlatestRev with ⟨Hl1, Hl2⟩
      icases (hring _).1 $$ Hhist with ⟨Hh1, Hh2⟩
      isplitl [Hst1 Hrev1 Hl1 Hh1]
      · iexists st; simp only [named]; iframe; ipureintro; exact Hinv
      · iexists st; simp only [named]; iframe; ipureintro; exact Hinv
    · iintro ⟨H1, H2⟩
      unfold storeLockInv
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hst1 Hst2 gives % ⟨_, Heq⟩
      subst Heq
      iexists st
      simp only [named]
      rw [qp_half_add]
      isplitl [Hst1 Hst2]
      · iapply (hgv st).2; iframe
      isplitl [Hrev1 Hrev2]
      · iapply (hmono _).2; iframe
      isplitl [HlatestRev1 HlatestRev2]
      · iapply (hrev _).2; iframe
      isplitl [Hhist1 Hhist2]
      · iapply (hring _).2; iframe
      ipureintro; exact Hinv1

/-- `s` is a store with a history of capacity `cap` (persistent): `s.revCond` is a
condition variable (on `s.mu.RLocker()`), `s.degree` the btrees' degree. `γ` names the
store's ghost state (held by `storeReader`, `storeWriter`, `storeRevLb`). -/
def isStore (s : Loc) (_γ : StoreNames) (cap : Nat) : IProp GF :=
  iprop(∃ (c : Loc) (lk : GoInterfaceOk) (deg : w64),
    "#HrevCond" ∷ structFieldRef store go!"revCond" s ↦□ c ∗
    "#Hcond" ∷ sync.isCond c lk ∗
    "#Hdeg" ∷ structFieldRef store go!"degree" s ↦□ deg ∗
    "%Hdeg" ∷ ⌜1 < sint.Z deg⌝ ∗
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
def storeReader (s : Loc) (γ : StoreNames) (cap : Nat) : IProp GF :=
  sync.ownRWMutex (storeMuAddr s) (storeLockInv (hG := hG) s γ cap)

/-- The single writer's half of the store (the cache's watch loop, which calls `Restore`
and `Apply`): the store's state is `st`. It holds the other half of `γ.state`, a token of
`s.mu` (to `Lock` it), and the latest tree, which only the writer touches; and a lower bound on the latest
revision (the counter itself is in the lock). -/
def storeWriter (s : Loc) (γ : StoreNames) (cap : Nat) (st : StoreState) : IProp GF :=
  iprop(ghostVar γ.state (1 : Qp).half st ∗
    sync.ownRWMutex (storeMuAddr s) (storeLockInv (hG := hG) s γ cap) ∗
    storeLatestTree s st.latest ∗ storeRevLb γ st.latestRev ∗ ⌜StoreInv cap st⌝)

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
  ihave H := isPkgInit_access $$ H
  iexact H

end defs

end EtcdGrove
end Perennial
