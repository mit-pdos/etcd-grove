/-
`client/v3/leasing`'s lease cache (`cache.go`): the vocabulary of its specs. Lean-first (no Rocq
counterpart). See `decisions.md`, "Leasing: the lease cache's lock, exact transitions".

**The state** (`LeaseCacheSt`, a record of pure values): the entries map (`lc.entries`, nil until
the leasing KV's first session, then a map), its entries (`LeaseEntry`: the `*leaseKey` `li`, its
`rev` (the acquisition revision), its waiter channel `waitc`, its `*GetResponse` with the header
(read-only), the cached key-values (`CachedKv`), `More`, `Count`, and two ghost fields: the
holder's lease and the key's record at `rev`), the revocation times (`lc.revokes`), the latest
header (`lc.header`), and the *frozen* entries: entries removed from the map (by `Evict`,
`EvictRange` or a session reset), whose resources the cache keeps read-only, because a `Get`
that found an entry before waiting may read it after its eviction (Go's garbage collector keeps
it; nothing writes it any more).

**The lock** (`lc.mu`, an `RWMutex`): its invariant `leaseCacheInv lc γ pfx X q` (fractional: a
reader holds `q = rfrac`) holds the state in a ghost variable (so the fractions agree), the
physical fields and entries with fraction `q` (`lcOwn`), the facts below, and a client part
`X st q` (fractional in `q`): what the leasing KV keeps under the same lock (`sessionc`,
`session`) and its own invariant over the state, which every transition must preserve (the
writers' specs take the client's step `X st 1 ={⊤}=∗ X (f st) 1 ∗ Q st`). A writer needs only the
persistent `isLeaseCache` (the `RWMutex` guard); a reader, a reader token
(`leaseCacheReader`, one of the `RWMutex`'s bounded reader slots).

**The entry facts** (`entryFacts pfx k e`, persistent, kept for every entry): etcd's whole
keyspace at `e.rev` is a state `s` in which `k` has the record `e.acq` (what the entry cached
when it was added) and the lease key `pfx ++ k` has the holder's lease `e.lease` and a create
revision at most `e.rev` (the acquiring transaction made it, or found it). Unit 4 ties them to
the protocol (`leased_value_stable`).

**Readiness**: `Add` writes the entries map, which must not be nil; `leaseCacheReady γ` (a
persistent witness, a monotone counter at `1`) says that it was made (the session reset of the
leasing KV makes it; nothing makes it nil again).

**Stale readers**: `notify` returns the entry's `*leaseKey` with a persistent witness that it was
installed (`leaseKeyInstalled γ li`: an index into a monotone list of every `li` ever put into
the map); the invariant keeps every installed `li` either in the map or frozen.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.Base
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingModel
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## The model -/

section model
variable [ext : FfiSyntax]

/-- A cache entry: the `*leaseKey` `li` (`response`, `rev`, `waitc`) and its `*GetResponse`
`resp` (`Header`, `Kvs`, `More`, `Count`); `lease` and `acq` are ghost (the holder's lease and
the key's record at `rev`, when the entry was added). -/
structure LeaseEntry where
  li : Loc
  rev : w64
  waitc : GoChan
  resp : Loc
  hdr : Loc
  hm : HdrM
  kvsSl : GoSlice
  kvs : List CachedKv
  more : Bool
  count : w64
  lease : w64
  acq : Option EtcdKv

/-- The lease cache's state (see the module docstring). -/
structure LeaseCacheSt where
  emap : GoMap
  entries : GMap GoString LeaseEntry
  rmap : GoMap
  revokes : GMap GoString time.Time
  header : Loc
  hm : HdrM
  frozen : List (GoString × LeaseEntry)
  installed : List (GoString × Loc)

/-- The `leaseKey` value of an entry. -/
def LeaseEntry.lk (e : LeaseEntry) : leaseKey :=
  { response' := e.resp, rev' := e.rev, waitc' := e.waitc }

/-- The entry's cached record (`Kvs[0]`), if any. -/
def LeaseEntry.kv (e : LeaseEntry) : Option EtcdKv := (e.kvs.head?).map CachedKv.kv

/-- The entries map's readiness, as a counter (`0`: nil, `1`: made). -/
def LeaseCacheSt.readyN (st : LeaseCacheSt) : Nat := if st.emap = map.nil then 0 else 1

/-- The `*leaseKey`s of the map's entries. -/
def LeaseCacheSt.lis (st : LeaseCacheSt) : GMap GoString Loc := GMap.fmap LeaseEntry.li st.entries

/-- `inRange(k, begin, end)` (`cache.go`, not etcd's): `begin ≤ k`, and `k < end` unless `end`
is `"\x00"`. (For `end = ""` nothing is in range.) -/
def leaseInRange (k b e : GoString) : Bool :=
  !decide (go.GoStringLt k b) && (decide (e = [W8 0]) || decide (go.GoStringLt k e))

/-! ### Transitions -/

/-- Remove the entry of `k` (if any) from the map, freezing it. -/
def LeaseCacheSt.removeEntry (k : GoString) (st : LeaseCacheSt) : LeaseCacheSt :=
  match st.entries !! k with
  | some e => { st with entries := GMap.delete k st.entries, frozen := (k, e) :: st.frozen }
  | none => st

/-- `Lock(k)`'s change: `k`'s entry (if any) gets the waiter channel `ch`. -/
def LeaseCacheSt.setWaitc (k : GoString) (ch : GoChan) (st : LeaseCacheSt) : LeaseCacheSt :=
  match st.entries !! k with
  | some e => { st with entries := GMap.insert k { e with waitc := ch } st.entries }
  | none => st

/-- The entries' waiter channels may change, nothing else (`Lock`, `LockRange`). -/
def WaitcOnly (st st' : LeaseCacheSt) : Prop :=
  st'.emap = st.emap ∧ st'.rmap = st.rmap ∧ st'.revokes = st.revokes ∧ st'.header = st.header ∧
  st'.hm = st.hm ∧ st'.frozen = st.frozen ∧ st'.installed = st.installed ∧
  ∀ k, (st'.entries !! k).map (fun e => { e with waitc := null }) =
    (st.entries !! k).map (fun e => { e with waitc := null })

/-- `Evict(k)`'s change, at the time `t` it read: `k`'s entry (if any) is removed (frozen) and its
revocation time is `t`. -/
def LeaseCacheSt.evict (k : GoString) (t : time.Time) (st : LeaseCacheSt) : LeaseCacheSt :=
  match st.entries !! k with
  | some _ => { (st.removeEntry k) with revokes := GMap.insert k t st.revokes }
  | none => st

open Classical in
/-- `EvictRange(key, end)`'s change, at the last time `t` it read: if some entry is in range,
**`key`'s** entry (if any) is removed and `key`'s revocation time is `t` (the code deletes `key`,
not the key in range: a finding, see `STATUS.md`); otherwise nothing. -/
def LeaseCacheSt.evictRange (key e : GoString) (t : time.Time) (st : LeaseCacheSt) :
    LeaseCacheSt :=
  if ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true then
    { (st.removeEntry key) with revokes := GMap.insert key t st.revokes }
  else st

/-- `Add(k, …)`'s change: the entry `e` replaces `k`'s (frozen), is installed, and its header
becomes the cache's if there was none or it is newer. -/
def LeaseCacheSt.add (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) : LeaseCacheSt :=
  let st1 := st.removeEntry k
  let newer := decide (st.header = null ∨ sint.Z st.hm.revision < sint.Z e.hm.revision)
  let inst := st.installed ++ [(k, e.li)]
  let hdr := if newer then e.hdr else st.header
  let hm := if newer then e.hm else st.hm
  { st1 with entries := GMap.insert k e st1.entries, installed := inst, header := hdr, hm := hm }

/-- The change of an entry's first cached key-value by `Update` (the put at revision `r` of the
value `val`, in the slice `valSl`): its version is incremented; if it was modified before `r`, its
mod revision becomes `r` and its value `val`. -/
def CachedKv.bump (c : CachedKv) (r : w64) (valSl : GoSlice) (val : GoString) : CachedKv :=
  if sint.Z c.kv.modRev < sint.Z r then
    let v : EtcdKv := { c.kv with version := c.kv.version + W64 1, modRev := r, value := val }
    { c with valSl := valSl, kv := v }
  else { c with kv := { c.kv with version := c.kv.version + W64 1 } }

/-- `Update`'s change of an entry, for the put at revision `hm.revision` (header `h`): with no
cached key-value, the fresh one `fresh` (in the new slice `sl'`) is appended and the count set
to `1`; then the first key-value is bumped (`CachedKv.bump`) and, if it was modified before the
put, the response's header becomes `h`. -/
def LeaseEntry.update (e : LeaseEntry) (fresh : CachedKv) (sl' : GoSlice) (h : Loc) (hm : HdrM)
    (valSl : GoSlice) (val : GoString) : LeaseEntry :=
  let e1 := if e.kvs = [] then { e with kvsSl := sl', kvs := [fresh], count := W64 1 } else e
  match e1.kvs with
  | c :: cs =>
    if sint.Z c.kv.modRev < sint.Z hm.revision then
      { e1 with kvs := c.bump hm.revision valSl val :: cs, hdr := h, hm := hm }
    else { e1 with kvs := c.bump hm.revision valSl val :: cs }
  | [] => e1

/-- The fresh key-value `Update` makes for a key with no cached key-value: `Key` the key's slice,
`CreateRevision` the put's revision, the rest zero. -/
def freshKv (p : Loc) (keySl : GoSlice) (key : GoString) (r : w64) : CachedKv :=
  let v : EtcdKv :=
    { key := key, createRev := r, modRev := W64 0, version := W64 0, value := [], lease := W64 0 }
  { p := p, keySl := keySl, valSl := slice.nil, kv := v }

/-- `delete`'s change of an entry, for a delete at the header `hm` (copied into `h`): if it is
not older than the response, the cached key-values are dropped and the header becomes `h`. -/
def LeaseEntry.del (e : LeaseEntry) (h : Loc) (hm : HdrM) : LeaseEntry :=
  if sint.Z e.hm.revision ≤ sint.Z hm.revision then
    { e with kvsSl := slice.nil, kvs := [], hdr := h, hm := hm }
  else e

/-- Change `k`'s entry (if any) by `f`. -/
def LeaseCacheSt.modify (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt) :
    LeaseCacheSt :=
  match st.entries !! k with
  | some e => { st with entries := GMap.insert k (f e) st.entries }
  | none => st

/-- `k`'s entry's revision, `0` if none (`Rev`). -/
def LeaseCacheSt.revOf (k : GoString) (st : LeaseCacheSt) : w64 :=
  ((st.entries !! k).map LeaseEntry.rev).getD (W64 0)

/-! ### What a cached get returns -/

/-- `leaseKey.get(op)`'s test: the response is empty if nothing is cached, or `op` is count-only,
or the cached key-value fails one of `op`'s revision filters (signed, as Go compares `int64`s). -/
def getEmpty (o : OpModel) (kvs : List CachedKv) : Bool :=
  match kvs with
  | [] => true
  | c :: _ =>
    decide (o.countOnly = true ∨ sint.Z c.kv.modRev < sint.Z o.minModRev ∨
      (o.maxModRev ≠ W64 0 ∧ sint.Z o.maxModRev < sint.Z c.kv.modRev) ∨
      sint.Z c.kv.createRev < sint.Z o.minCreateRev ∨
      (o.maxCreateRev ≠ W64 0 ∧ sint.Z o.maxCreateRev < sint.Z c.kv.createRev))

/-- **What a cached get returns** for the entry `e` and the get `o`: the first cached key-value
(its value dropped if keys-only), or nothing (`getEmpty`). -/
def getResult (o : OpFull) (e : LeaseEntry) : Option EtcdKv :=
  if getEmpty o.base e.kvs then none
  else (e.kvs.head?).map (fun c => if o.keysOnly then { c.kv with value := [] } else c.kv)

/-- `compareInt64(a, b)`: `-1`, `0` or `1` (signed). -/
def compareInt64M (a b : w64) : w64 :=
  if sint.Z a < sint.Z b then W64 (-1) else if sint.Z b < sint.Z a then W64 1 else W64 0

/-- The revocation times `rv` are some of `rv0`'s (`clearOldRevokes` deletes old ones). -/
def RevokesSub (rv rv0 : GMap GoString time.Time) : Prop := ∀ k t, rv !! k = some t → rv0 !! k = some t

/-- `isBadOp(op)`: a get at an earlier revision or of a range is not served from the cache. -/
def isBadOpM (o : OpFull) : Bool := decide (0 < sint.Z o.base.rev ∨ o.base.rangeEnd ≠ [])

/-- **The well-formedness of the state**: entries have distinct `*leaseKey`s, none of them
frozen; every `*leaseKey` installed under a key is that key's entry or frozen; an entry's `li` is
not nil; the map is not nil if it has entries. -/
structure LeaseCacheWf (st : LeaseCacheSt) : Prop where
  li_inj : ∀ k1 k2 e1 e2, st.entries !! k1 = some e1 → st.entries !! k2 = some e2 →
    e1.li = e2.li → k1 = k2
  li_not_frozen : ∀ k e, st.entries !! k = some e → ∀ f ∈ st.frozen, f.2.li ≠ e.li
  installed : ∀ k li, (k, li) ∈ st.installed → (∃ e, st.entries !! k = some e ∧ e.li = li) ∨
    (∃ e, (k, e) ∈ st.frozen ∧ e.li = li)
  entries_installed : ∀ k e, st.entries !! k = some e → (k, e.li) ∈ st.installed
  li_ne : ∀ k e, st.entries !! k = some e → e.li ≠ null
  empty_if_nil : st.emap = map.nil → st.entries = ∅

end model

/-! ## Countable instances (for the ghost variable holding the state) -/

instance HdrM.countable : Pos.Countable HdrM :=
  .ofInjective (fun h => Pos.Countable.encode (h.clusterId, h.memberId, h.revision, h.raftTerm,
    h.leaderId))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

instance EtcdKv.countable : Pos.Countable EtcdKv :=
  .ofInjective (fun v => Pos.Countable.encode (v.key, v.createRev, v.modRev, v.version, v.value,
    v.lease))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

instance CachedKv.countable : Pos.Countable CachedKv :=
  .ofInjective (fun c => Pos.Countable.encode (c.p, c.keySl, c.valSl, c.kv))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

instance LeaseEntry.countable : Pos.Countable LeaseEntry :=
  .ofInjective (fun e => Pos.Countable.encode (e.li, e.rev, e.waitc, e.resp, e.hdr, e.hm,
    e.kvsSl, e.kvs, e.more, e.count, e.lease, e.acq))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

instance time.Time.countable [FfiSyntax] : Pos.Countable time.Time :=
  .ofInjective (fun t => Pos.Countable.encode (t.wall', t.ext', t.loc'))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

instance LeaseCacheSt.countable [FfiSyntax] : Pos.Countable LeaseCacheSt :=
  .ofInjective (fun st => Pos.Countable.encode (st.emap, st.entries, st.rmap, st.revokes,
    st.header, st.hm, st.frozen, st.installed))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-! ## Ownership -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- What closing a waiter channel announces: nothing (a waiter reads the cache again). -/
abbrev waitQ : IProp GF := iprop(True)

/-- A waiter channel: anyone may receive on it (a broadcast channel, closed by the writer that
installed it, `Lock`, or the package's closed `closedCh`). Persistent. -/
def waitcOk (ch : GoChan) : IProp GF :=
  iprop(∃ γch : ChanNames, ownBroadcastChan ch γch waitQ .Unknown)

instance waitcOk_persistent (ch : GoChan) : Persistent (waitcOk (GF := GF) ch) := by
  unfold waitcOk; infer_instance

/-- **An entry's response** (not nil), with fraction `dq`: its `Header` (a read-only header),
`Kvs` (the slice, its capacity, the key-values), `More` and `Count`. (The fields' points-tos do not
say that the response is not nil, which `copyGetResponseMetadataOnly` tests.) -/
def respOwn (e : LeaseEntry) (dq : DFrac) : IProp GF :=
  iprop(⌜e.resp ≠ null⌝ ∗
    structFieldRef etcdserverpb.RangeResponse go!"Header" e.resp ↦{dq} e.hdr ∗ hdrFull e.hdr e.hm ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" e.resp ↦{dq} e.kvsSl ∗
    e.kvsSl ↦*{dq} (e.kvs.map CachedKv.p) ∗ ownSliceCap Loc e.kvsSl dq ∗
    ([∗list] c ∈ e.kvs, cachedKvOwn c dq) ∗
    structFieldRef etcdserverpb.RangeResponse go!"More" e.resp ↦{dq} e.more ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" e.resp ↦{dq} e.count)

instance respOwn_dfractional (e : LeaseEntry) :
    DFractional (fun dq => respOwn (GF := GF) e dq) := by
  unfold respOwn; infer_instance

/-- **An entry's resources**, with fraction `dq` (`DFrac.discard`: frozen): the `*leaseKey`'s
fields (not nil), the response, and the waiter channel's receive right. (Field by field: the
proof mode does not find a struct field's points-to inside a struct's, `leaseKey_struct` turns
them into the struct's for `Get`'s `*li`.) -/
def entryOwn (e : LeaseEntry) (dq : DFrac) : IProp GF :=
  iprop(⌜e.li ≠ null⌝ ∗ structFieldRef leaseKey go!"response" e.li ↦{dq} e.resp ∗
    structFieldRef leaseKey go!"rev" e.li ↦{dq} e.rev ∗
    structFieldRef leaseKey go!"waitc" e.li ↦{dq} e.waitc ∗ respOwn e dq ∗ waitcOk e.waitc)

instance entryOwn_dfractional (e : LeaseEntry) :
    DFractional (fun dq => entryOwn (GF := GF) e dq) := by
  unfold entryOwn; infer_instance

/-- The `*leaseKey`'s three fields are its points-to (it is not nil). -/
theorem leaseKey_struct (li : Loc) (lk : leaseKey) (dq : DFrac) (h : li ≠ null) :
    structFieldRef leaseKey go!"response" li ↦{dq} lk.response' ∗
      structFieldRef leaseKey go!"rev" li ↦{dq} lk.rev' ∗
      structFieldRef leaseKey go!"waitc" li ↦{dq} lk.waitc' ⊣⊢ (li ↦{dq} lk : IProp GF) := by
  constructor
  · iintro ⟨H1, H2, H3⟩
    iapply typedPointsto_combine _ _ _ h
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · iintro H
    iStructNamed H
    iframe

instance entryOwn_discard_persistent (e : LeaseEntry) :
    Persistent (entryOwn (GF := GF) e DFrac.discard) :=
  (entryOwn_dfractional (GF := GF) e).dfractional_persistent

/-- A map points-to splits and combines by fraction (`InvDemux.ownMap_fractional`, without the
cache's package assumptions). -/
theorem lc_ownMap_fractional {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, mp; simp only [named]; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
      · iexists mv, mp; simp only [named]; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, mp
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact ⟨His_map2, Hagree2, Hdom2, Hdefault2⟩

/-- An existential over a fractional body whose fractions agree on the witness is fractional
(`InvDemux.fractional_exists_agree`, without the cache's package assumptions). -/
theorem lc_fractional_exists_agree {Y : Type} (Φ : Y → Qp → IProp GF)
    (hfrac : ∀ x, Fractional (Φ x)) (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

/-- The entries map's contents, with fraction `dq`: nothing while it is nil. -/
def emapOwn (st : LeaseCacheSt) (dq : DFrac) : IProp GF :=
  if st.emap = map.nil then iprop(True) else iprop(st.emap ↦${dq} st.lis)

/-- The latest header, if any (read-only). -/
def headerOk (h : Loc) (m : HdrM) : IProp GF :=
  if h = null then iprop(True) else hdrFull h m

instance headerOk_persistent (h : Loc) (m : HdrM) : Persistent (headerOk (GF := GF) h m) := by
  unfold headerOk; split <;> infer_instance

/-- **The cache's physical state** `st`, with fraction `dq`: its three fields, the two maps,
the entries' resources, and the frozen entries' (read-only). -/
def lcOwn (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) : IProp GF :=
  iprop(structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap ∗ emapOwn st dq ∗
    structFieldRef leaseCache go!"revokes" lc ↦{dq} st.rmap ∗ st.rmap ↦${dq} st.revokes ∗
    structFieldRef leaseCache go!"header" lc ↦{dq} st.header ∗ headerOk st.header st.hm ∗
    ([∗map] _k ↦ e ∈ st.entries, entryOwn e dq) ∗
    ([∗list] f ∈ st.frozen, entryOwn f.2 DFrac.discard))

theorem emapOwn_fractional (st : LeaseCacheSt) :
    Fractional (fun q => emapOwn (GF := GF) st (DFrac.own q)) := by
  unfold emapOwn
  split
  · infer_instance
  · exact lc_ownMap_fractional _ _

instance lcOwn_fractional (lc : Loc) (st : LeaseCacheSt) :
    Fractional (fun q => lcOwn (GF := GF) lc st (DFrac.own q)) := by
  unfold lcOwn
  haveI := emapOwn_fractional (GF := GF) st
  haveI := lc_ownMap_fractional (GF := GF) st.rmap st.revokes
  haveI : ∀ (l : Loc) (v : Loc), Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q)) :=
    fun l v => fractional_of_dfractional (fun dq => typedPointsto l v dq)
  haveI : ∀ e : LeaseEntry, Fractional (fun q : Qp => entryOwn (GF := GF) e (DFrac.own q)) :=
    fun e => fractional_of_dfractional (fun dq => entryOwn e dq)
  infer_instance

/-- **The facts an entry keeps** (persistent; see the module docstring): etcd's whole keyspace at
`e.rev` is a state where `k` has the record `e.acq` and the lease key `pfx ++ k` has the lease
`e.lease` and a create revision at most `e.rev`. -/
def entryFacts (pfx k : GoString) (e : LeaseEntry) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState e.rev [] s ∗
    ⌜EtcdStateWf [] s ∧ kvOf s k = e.acq ∧ ∃ lv, kvOf s (pfx ++ k) = some lv ∧
      lv.lease = e.lease ∧ sint.Z lv.createRev ≤ sint.Z e.rev⌝)

instance entryFacts_persistent (pfx k : GoString) (e : LeaseEntry) :
    Persistent (entryFacts (GF := GF) pfx k e) := by
  unfold entryFacts; infer_instance

/-- The ghost names of a lease cache: its state, its readiness, its installed `*leaseKey`s. -/
structure LeaseCacheNames where
  st : GName
  ready : GName
  inst : GName

/-- The lock invariant's body for the state `st` (fraction `q`). -/
def leaseCacheBody (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) (st : LeaseCacheSt) (q : Qp) : IProp GF :=
  iprop(ghostVar γ.st q st ∗ monoNatAuthOwn γ.ready q st.readyN ∗
    monoListAuthOwn γ.inst q st.installed ∗ lcOwn lc st (DFrac.own q) ∗
    □ ([∗map] k ↦ e ∈ st.entries, entryFacts pfx k e) ∗
    □ ([∗list] f ∈ st.frozen, entryFacts pfx f.1 f.2) ∗ ⌜LeaseCacheWf st⌝ ∗ X st q)

/-- **The lock invariant** of `lc.mu` (fraction `q`; see the module docstring). -/
def leaseCacheInv (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ st : LeaseCacheSt, leaseCacheBody lc γ pfx X st q)

theorem leaseCacheBody_fractional (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) [hX : ∀ st, Fractional (X st)] (st : LeaseCacheSt) :
    Fractional (leaseCacheBody (GF := GF) lc γ pfx X st) := by
  unfold leaseCacheBody
  haveI := lcOwn_fractional (GF := GF) lc st
  infer_instance

/-- The lock invariant is fractional (for `sync.init_RWMutex`), given that the client part is. -/
instance leaseCacheInv_fractional (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) [hX : ∀ st, Fractional (X st)] :
    Fractional (leaseCacheInv (GF := GF) lc γ pfx X) := by
  unfold leaseCacheInv
  exact lc_fractional_exists_agree (leaseCacheBody lc γ pfx X)
    (leaseCacheBody_fractional lc γ pfx X) (fun x y q1 q2 => by
      unfold leaseCacheBody
      iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
      iapply ghostVar_agree $$ H1 H2)

/-! ### The cache's handles -/

/-- The package's closed channel `closedCh` (a new entry's waiter channel) can be received from
(it is closed; persistent; ghost state, so not in the package's `IsPkgInit`). -/
def closedChInit : IProp GF :=
  iprop(∃ ch : GoChan, globalAddr closedCh ↦□ ch ∗ waitcOk ch)

instance closedChInit_persistent : Persistent (closedChInit (GF := GF)) := by
  unfold closedChInit; infer_instance

/-- **The lease cache** `lc` (persistent): its `RWMutex` with the lock invariant (the writers'
guard), and the closed channel. -/
def isLeaseCache (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) : IProp GF :=
  iprop(sync.isRWMutexGuard (hG := hG) (structFieldRef leaseCache go!"mu" lc) (leaseCacheInv lc γ pfx X) ∗ closedChInit)

instance isLeaseCache_persistent (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) : Persistent (isLeaseCache (GF := GF) lc γ pfx X) := by
  unfold isLeaseCache; infer_instance

/-- A reader's token (one of the `RWMutex`'s reader slots). -/
def leaseCacheReader (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) : IProp GF :=
  sync.ownRWMutex (hG := hG) (structFieldRef leaseCache go!"mu" lc) (leaseCacheInv lc γ pfx X)

/-- The entries map was made (persistent; see the module docstring). -/
def leaseCacheReady (γ : LeaseCacheNames) : IProp GF := monoNatLbOwn γ.ready 1

instance leaseCacheReady_persistent (γ : LeaseCacheNames) :
    Persistent (leaseCacheReady (GF := GF) γ) := by
  unfold leaseCacheReady; infer_instance

/-- The `*leaseKey` `li` was installed under the key `k` (persistent). -/
def leaseKeyInstalled (γ : LeaseCacheNames) (k : GoString) (li : Loc) : IProp GF :=
  iprop(∃ i : Nat, monoListIdxOwn γ.inst i (k, li))

instance leaseKeyInstalled_persistent (γ : LeaseCacheNames) (k : GoString) (li : Loc) :
    Persistent (leaseKeyInstalled (GF := GF) γ k li) := by
  unfold leaseKeyInstalled; infer_instance

/-- The client's peek at its part of the invariant: what it learns (`Qr st`, persistent) of a
state `st` it holds any fraction of. -/
def lcPeek (X : LeaseCacheSt → Qp → IProp GF) (Qr : LeaseCacheSt → IProp GF) : IProp GF :=
  iprop(□ ∀ (st : LeaseCacheSt) (q : Qp), X st q -∗ X st q ∗ □ Qr st)

instance lcPeek_persistent (X : LeaseCacheSt → Qp → IProp GF) (Qr : LeaseCacheSt → IProp GF) :
    Persistent (lcPeek X Qr) := by
  unfold lcPeek; infer_instance

/-- The client's part of the invariant does not depend on the waiter channels (what `Lock`,
`LockRange` and `LockWriteOps` change). -/
def lcWaitcStep (X : LeaseCacheSt → Qp → IProp GF) : IProp GF :=
  iprop(□ ∀ (st st' : LeaseCacheSt), ⌜WaitcOnly st st'⌝ -∗ X st 1 ={⊤}=∗ X st' 1)

instance lcWaitcStep_persistent (X : LeaseCacheSt → Qp → IProp GF) :
    Persistent (lcWaitcStep X) := by
  unfold lcWaitcStep; infer_instance

/-- A waiter channel the caller must close (it was made by `Lock`/`LockRange`). -/
def waitcClose (ch : GoChan) : IProp GF :=
  iprop(∃ γch : ChanNames, ownBroadcastChan ch γch waitQ .Pending)

/-- The entry of `k` in `st` keeps its facts (nothing if none). -/
def entryFactsAt (pfx k : GoString) (st : LeaseCacheSt) : IProp GF :=
  match st.entries !! k with
  | some e => entryFacts pfx k e
  | none => iprop(True)

instance entryFactsAt_persistent (pfx k : GoString) (st : LeaseCacheSt) :
    Persistent (entryFactsAt (GF := GF) pfx k st) := by
  unfold entryFactsAt; split <;> infer_instance

/-- **A fresh `*GetResponse`** `r` (not nil, allocated by the cache, owned by the caller): its `Header` a
fresh copy of the fields `hm`, `More`, `Count`, and the key-value `kv` (if any) in a fresh
`*KeyValue` (the contents of its slices read-only). -/
def freshGetResp (r : Loc) (hm : HdrM) (more : Bool) (count : w64) (kv : Option EtcdKv) :
    IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (cs : List CachedKv),
    structFieldRef etcdserverpb.RangeResponse go!"Header" r ↦ h ∗ hdrFull h hm ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" r ↦ sl ∗ sl ↦* (cs.map CachedKv.p) ∗
    ownSliceCap Loc sl (DFrac.own 1) ∗ ([∗list] c ∈ cs, cachedKvOwn c (DFrac.own 1)) ∗
    ⌜cs.map CachedKv.kv = kv.toList⌝ ∗
    structFieldRef etcdserverpb.RangeResponse go!"More" r ↦ more ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" r ↦ count)

/-! ### Opening the lock invariant -/

/-- The persistent facts of a state: every entry's and frozen entry's. -/
def lcFacts (pfx : GoString) (st : LeaseCacheSt) : IProp GF :=
  iprop(([∗map] k ↦ e ∈ st.entries, entryFacts pfx k e) ∗
    ([∗list] f ∈ st.frozen, entryFacts pfx f.1 f.2))

instance lcFacts_persistent (pfx : GoString) (st : LeaseCacheSt) :
    Persistent (lcFacts (GF := GF) pfx st) := by
  unfold lcFacts; infer_instance

/-- **Opening the lock invariant to read** (any fraction `q`): the state's resources, the
client's part, the installed list's authority, and the way back for the same state. -/
theorem leaseCacheInv_open (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) (q : Qp) :
    leaseCacheInv lc γ pfx X q ⊢ ∃ st : LeaseCacheSt,
      lcOwn lc st (DFrac.own q) ∗ X st q ∗ monoListAuthOwn γ.inst q st.installed ∗
      □ lcFacts pfx st ∗ ⌜LeaseCacheWf st⌝ ∗
      (lcOwn lc st (DFrac.own q) -∗ X st q -∗ monoListAuthOwn γ.inst q st.installed -∗
        leaseCacheInv lc γ pfx X q) := by
  unfold leaseCacheInv leaseCacheBody
  iintro ⟨%st, Hst, Hready, Hinst, Hown, #Hfacts, #Hffacts, %Hwf, HX⟩
  iexists st
  iframe
  isplitr
  · unfold lcFacts; iframe #
  isplitr
  · ipureintro; exact Hwf
  iintro Hown HX Hinst
  iexists st
  iframe
  iframe #
  ipureintro; exact Hwf

/-- **Opening the lock invariant to write** (the whole of it): the state's resources and the
client's part, and the way back for any new state that is well formed, keeps its facts, does not
make the map nil again, and extends the installed list (the ghost state follows). -/
theorem leaseCacheInv_open_w (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString)
    (X : LeaseCacheSt → Qp → IProp GF) :
    leaseCacheInv lc γ pfx X 1 ⊢ ∃ st : LeaseCacheSt,
      lcOwn lc st (DFrac.own 1) ∗ X st 1 ∗ monoListAuthOwn γ.inst 1 st.installed ∗
      monoNatAuthOwn γ.ready 1 st.readyN ∗ □ lcFacts pfx st ∗ ⌜LeaseCacheWf st⌝ ∗
      (∀ st' : LeaseCacheSt, ⌜LeaseCacheWf st'⌝ -∗ □ lcFacts pfx st' -∗
        monoListAuthOwn γ.inst 1 st'.installed -∗ monoNatAuthOwn γ.ready 1 st'.readyN -∗
        lcOwn lc st' (DFrac.own 1) -∗ X st' 1 ==∗ leaseCacheInv lc γ pfx X 1) := by
  unfold leaseCacheInv leaseCacheBody
  iintro ⟨%st, Hst, Hready, Hinst, Hown, #Hfacts, #Hffacts, %Hwf, HX⟩
  iexists st
  iframe
  isplitr
  · unfold lcFacts; iframe #
  isplitr
  · ipureintro; exact Hwf
  iintro %st' %Hwf' #Hfacts' Hinst' Hready' Hown' HX'
  imod ghostVar_update st' $$ Hst with Hst
  imodintro
  iexists st'
  unfold lcFacts
  icases Hfacts' with ⟨#H1, #H2⟩
  iframe
  iframe #
  ipureintro; exact Hwf'

end defs

end EtcdGrove
end Perennial
