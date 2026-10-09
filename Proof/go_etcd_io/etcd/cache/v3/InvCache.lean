/-
etcd's cache `Cache` (`cache/cache.go`, `cache/predicate.go`): the vocabulary of the
request-side helpers' specs (`Spec/{ExactKey,FromKey,Range,KeyPredForRange}.lean`,
`Spec/Cache__validate*.lean`, `Spec/Cache__{Ready,WaitReady,RequestProgress}.lean`) and of
the `clientv3` functions they call (`Spec/Op__*.lean`, `Spec/GetPrefixRangeEnd.lean`,
`Spec/getPrefix.lean`). Lean-first (no Rocq counterpart).

**Keys.** A Go `[]byte` key is modelled by its contents, a `GoString` (`List w8`, as Go's
`string([]byte)` conversion is): `sl ↦*{dq} k`. `bytes.Equal`/`bytes.Compare` are Go's `==`
and `<` on the strings (`bytes.wp_Equal`, `bytes.wp_Compare`), so a key predicate is a
function `GoString → Bool` in terms of `go.GoStringLt`, the order of the store's maps
(`InvStore.lean`). `keyPredForRange start end` is the predicate `KeyPredForRange` builds;
it is `kvRange`'s membership test (`mem_kvRange`), so `Get`'s range and `Watch`'s filter
select the same keys.

**Ranges.** `validRange prefix start end` is `Cache.validateRange`: the range must lie
within the cache's prefix (`prefixRangeEnd`, `clientv3.GetPrefixRangeEnd`, is the least key
above every key with the prefix; `[0]` if there is none).

**`clientv3.Op`.** An `Op` is a struct value; `OpModel` is what the cache's helpers read of
it through its getters, `opAt op o` relates them (the range end is a read-only byte slice).

**The `Cache`'s fields.** `isCacheFields c cf γr γd cap` is a *partial* predicate: the
fields `prefix`, `cfg`, `ready` and `demux`, read-only, with `ready`'s and `demux`'s
persistent predicates. The `Cache` stage extends it (store, watcher, wait group, ...).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux
public import Proof.go_etcd_io.etcd.cache.v3.InvReady
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Key predicates -/

/-- `ExactKey(key)`: `k == key`. -/
def exactKeyPred (key : GoString) (k : GoString) : Bool := decide (k = key)

/-- `FromKey(start)`: `k >= start`. -/
def fromKeyPred (start : GoString) (k : GoString) : Bool := !decide (go.GoStringLt k start)

/-- `Range(start, end)`: `start <= k < end`. -/
def rangePred (start end_ : GoString) (k : GoString) : Bool :=
  !decide (go.GoStringLt k start) && decide (go.GoStringLt k end_)

/-- `KeyPredForRange(start, end)`: the key `start` alone if `end` is empty, the keys from
`start` on if `end` is `"\x00"`, the keys in `[start, end)` otherwise. -/
def keyPredForRange (start end_ : GoString) : GoString → Bool :=
  if end_ = [] then exactKeyPred start
  else if end_ = [W8 0] then fromKeyPred start
  else rangePred start end_

/-- `kvRange` (`snapshot.Range`, the store's `Get`) filters by `keyPredForRange`. -/
theorem kvRange_eq_filter (start end_ : GoString) (m : KvMap) :
    kvRange start end_ m = m.filter (fun e => keyPredForRange start end_ e.1) := by
  unfold kvRange keyPredForRange exactKeyPred fromKeyPred rangePred
  split <;> (try split) <;> rfl

/-- An entry is in `kvRange start end m` iff it is in `m` and its key satisfies
`keyPredForRange start end`. -/
theorem mem_kvRange (start end_ : GoString) (m : KvMap) (e : KvEntry) :
    e ∈ kvRange start end_ m ↔ e ∈ m ∧ keyPredForRange start end_ e.1 = true := by
  rw [kvRange_eq_filter, List.mem_filter]

/-! ## `bytes.Compare` -/

theorem goStringLt_asymm {a b : GoString} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a :=
  fun h' => goStringLt_irrefl a (goStringLt_trans h h')

theorem compareResult_lt (a b : GoString) :
    sint.Z (bytes.compareResult a b) < 0 ↔ go.GoStringLt a b := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, iff_true]; decide
  · simp only [h, ↓reduceIte, iff_false]
    split <;> decide

theorem compareResult_ge (a b : GoString) :
    0 ≤ sint.Z (bytes.compareResult a b) ↔ ¬ go.GoStringLt a b := by
  rw [← compareResult_lt]; omega

theorem compareResult_gt (a b : GoString) :
    0 < sint.Z (bytes.compareResult a b) ↔ go.GoStringLt b a := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (goStringLt_asymm h)⟩
  · simp only [h, ↓reduceIte]
    by_cases he : a = b
    · subst he; simp only [↓reduceIte]
      exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (goStringLt_irrefl a)⟩
    · simp only [he, ↓reduceIte]
      refine ⟨fun _ => ?_, fun _ => by decide⟩
      exact Classical.byContradiction fun h' => he (goStringLt_eq_of_not_lt h h')

theorem compareResult_le (a b : GoString) :
    sint.Z (bytes.compareResult a b) ≤ 0 ↔ ¬ go.GoStringLt b a := by
  rw [← compareResult_gt]; omega

/-! ## Ranges -/

/-- `Cache.validateRange(start, end)` on a cache with prefix `pfx`: a single key (`end`
empty) must be in the prefix's range `[pfx, prefixRangeEnd pfx)`; a "from key" range (`end`
is `"\x00"`) needs the root cache (`pfx` empty); a range `[start, end)` must be non-empty and
within `[pfx, prefixRangeEnd pfx]`. The root cache accepts every key and every non-empty
range. -/
def validRange (pfx start end_ : GoString) : Bool :=
  if end_ = [] then
    decide (pfx = []) ||
      (!decide (go.GoStringLt start pfx) && decide (go.GoStringLt start (prefixRangeEnd pfx)))
  else if end_ = [W8 0] then decide (pfx = [])
  else
    decide (go.GoStringLt start end_) &&
      (decide (pfx = []) ||
        (!decide (go.GoStringLt start pfx) && !decide (go.GoStringLt (prefixRangeEnd pfx) end_)))

/-! ## The `Cache`'s fields -/

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&c.prefix` -/
abbrev cachePrefixAddr (c : Loc) : Loc := structFieldRef Cache go!"prefix" c
/-- `&c.cfg` -/
abbrev cacheCfgAddr (c : Loc) : Loc := structFieldRef Cache go!"cfg" c
/-- `&c.ready` -/
abbrev cacheReadyAddr (c : Loc) : Loc := structFieldRef Cache go!"ready" c
/-- `&c.demux` -/
abbrev cacheDemuxAddr (c : Loc) : Loc := structFieldRef Cache go!"demux" c
/-- `&c.store` -/
abbrev cacheStoreAddr (c : Loc) : Loc := structFieldRef Cache go!"store" c
/-- `&c.kv` -/
abbrev cacheKvAddr (c : Loc) : Loc := structFieldRef Cache go!"kv" c
/-- `&c.progressRequestor` -/
abbrev cachePrAddr (c : Loc) : Loc := structFieldRef Cache go!"progressRequestor" c
/-- `&p.mux` -/
abbrev prMuxAddr (p : Loc) : Loc := structFieldRef conditionalProgressRequestor go!"mux" p

end addrs

/-- The values of the `Cache` fields `isCacheFields` covers (fixed by `newCache`), with the
store's ghost names and history capacity. -/
structure CacheFields [FfiSyntax] where
  pfx : GoString
  cfg : Config
  ready : Loc
  demux : Loc
  store : Loc
  /-- the store's ghost names -/
  γs : StoreNames
  /-- the store's history capacity -/
  scap : Nat
  /-- the `clientv3.KV` interface value -/
  kv : GoInterfaceOk
  /-- the `*conditionalProgressRequestor` in the `progressRequestor` interface -/
  pr : Loc

section prdefs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The lock invariant of a `conditionalProgressRequestor`'s `mux`: the waiter count and the
stopped flag (`run`'s loop, out of scope here, reads both under the lock). -/
def prLockInv (p : Loc) : IProp GF :=
  iprop(∃ (w : w32) (b : Bool),
    structFieldRef conditionalProgressRequestor go!"waiting" p ↦ w ∗
    structFieldRef conditionalProgressRequestor go!"stopped" p ↦ b)

/-- `p` is a `*conditionalProgressRequestor` (persistent): its `mux` guards `prLockInv`, its
`cond` is a condition variable. `add`/`remove` change the waiter count under the lock. -/
def isProgressRequestor (p : Loc) : IProp GF :=
  iprop(∃ (cp : Loc) (lk : GoInterfaceOk),
    structFieldRef conditionalProgressRequestor go!"cond" p ↦□ cp ∗ sync.isCond cp lk ∗
    sync.isMutex (prMuxAddr p) (prLockInv p))

instance isProgressRequestor_persistent (p : Loc) :
    Persistent (isProgressRequestor (GF := GF) p) := by
  unfold isProgressRequestor; infer_instance

end prdefs

section cache
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- Part of the `Cache` predicate (persistent): `prefix`, `cfg`, `ready`, `demux`, `store`, `kv`
and `progressRequestor` point for good to `cf`'s values, `cf.ready` is a `ready` (ghost names
`γr`), `cf.demux` a demux (ghost names `γd`, history capacity `cap`), `cf.store` a store (ghost
names `cf.γs`, history capacity `cf.scap`), `cf.kv` a client of etcd for the prefix
(`isEtcdKV`), and the progress requestor a `*conditionalProgressRequestor`. The `Cache` stage
extends it with the other fields (`watcher`, `waitGroup`, ...). -/
def isCacheFields (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames)
    (cap : Nat) : IProp GF :=
  iprop("#Hprefix" ∷ cachePrefixAddr c ↦□ cf.pfx ∗
    "#Hcfg" ∷ cacheCfgAddr c ↦□ cf.cfg ∗
    "#Hready" ∷ cacheReadyAddr c ↦□ cf.ready ∗
    "#Hdemux" ∷ cacheDemuxAddr c ↦□ cf.demux ∗
    "#HisReady" ∷ isReady cf.ready γr ∗
    "#HisDemux" ∷ isDemux cf.demux γd cap ∗
    "#Hstore" ∷ cacheStoreAddr c ↦□ cf.store ∗
    "#HisStore" ∷ isStore cf.store cf.γs cf.scap ∗
    "#Hkv" ∷ cacheKvAddr c ↦□ GoInterface.ok cf.kv ∗
    "#HisKV" ∷ isEtcdKV cf.kv cf.pfx ∗
    "#Hpr" ∷ cachePrAddr c ↦□
      GoInterface.ok (interface.mk (go.GoType.PointerType conditionalProgressRequestor.ty) #cf.pr) ∗
    "#HisPR" ∷ isProgressRequestor cf.pr)

instance isCacheFields_persistent (c : Loc) (cf : CacheFields) (γr : ReadyNames)
    (γd : DemuxNames) (cap : Nat) : Persistent (isCacheFields (GF := GF) c cf γr γd cap) := by
  unfold isCacheFields; infer_instance

/-- What `validateRange` returns: `nil` for a `validRange`, else the value of
`ErrKeyRangeInvalid`. -/
def rangeErr (pfx start end_ : GoString) (err : GoInterface) : IProp GF :=
  if validRange pfx start end_ then iprop(⌜err = GoInterface.nil⌝)
  else iprop(globalAddr ErrKeyRangeInvalid ↦□ err)

instance rangeErr_persistent (pfx start end_ : GoString) (err : GoInterface) :
    Persistent (rangeErr (GF := GF) pfx start end_ err) := by
  unfold rangeErr; split <;> infer_instance

/-- What `validateGet`/`validateWatch` return, for a request on `key` with range end
`rangeEnd` on a cache with prefix `pfx`: a non-nil error (`fmt.Errorf` wrapping
`ErrUnsupportedRequest`; the wrapping is not modelled) and no predicate if `unsupported`;
otherwise the value of `ErrKeyRangeInvalid` and no predicate if the range is not
`validRange`; otherwise `nil` and the `KeyPredForRange` closure. -/
def validateResult (unsupported : Bool) (pfx key rangeEnd : GoString) (f : GoFunc)
    (err : GoInterface) : IProp GF :=
  if unsupported then iprop(⌜f = func.nil ∧ ∃ e, err = GoInterface.ok e⌝)
  else if validRange pfx key rangeEnd then
    iprop(⌜err = GoInterface.nil ∧ f ≠ func.nil⌝ ∗ keyPredSpec f (keyPredForRange key rangeEnd))
  else iprop(⌜f = func.nil⌝ ∗ globalAddr ErrKeyRangeInvalid ↦□ err)

instance validateResult_persistent (u : Bool) (pfx key rangeEnd : GoString) (f : GoFunc)
    (err : GoInterface) : Persistent (validateResult (GF := GF) u pfx key rangeEnd f err) := by
  unfold validateResult; split
  · infer_instance
  · split <;> infer_instance

/-! ## `Cache.Get` -/

/-- A reader's token of the cache's store, with the cache's certificate (`etcdCert`). -/
def cacheReader (cf : CacheFields) : IProp GF :=
  storeReader cf.store cf.γs cf.scap (etcdCert cf.pfx)

/-- What `waitTillRevision(ctx, rev)` returns: `nil` once the store's latest revision is at
least `rev`; the value of `ErrCacheTimeout`; or the context's (non-nil) error once it is
done. -/
def waitResult (cf : CacheFields) (s : context.ContextDesc (IProp GF)) (rev : w64)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ storeRevLb cf.γs rev) ∨
    globalAddr ErrCacheTimeout ↦□ err ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn))

/-- `Cache.Get`'s errors, for a request on `key` with `Op` `o` (`OpModel`), as the code returns
them: the context is done (waiting for the cache to be ready, or for the store to catch up);
an unsupported option (some non-nil error); a range outside the cache's prefix
(`ErrKeyRangeInvalid`); for a linearizable request (not `WithSerializable`), the client's error
(any), a revision above etcd's current one (`rpctypes.ErrFutureRev`), or the store not catching
up in time (`ErrCacheTimeout`); or the store's (`getSnapshot`'s) error for its state `st`. -/
def cacheGetErr (cf : CacheFields) (r0 : w64) (s : context.ContextDesc (IProp GF))
    (key : GoString) (o : OpModel) (err : GoInterface) : IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ □ s.PDone ∗ context.ContextClosed s.Done_gn) ∨
    ⌜o.getUnsupported = true ∧ err ≠ GoInterface.nil⌝ ∨
    (⌜o.getUnsupported = false ∧ validRange cf.pfx key o.rangeEnd = false⌝ ∗
      globalAddr ErrKeyRangeInvalid ↦□ err) ∨
    ⌜o.serializable = false ∧ err ≠ GoInterface.nil⌝ ∨
    (⌜o.serializable = false⌝ ∗ globalAddr v3rpc.rpctypes.ErrFutureRev ↦□ err ∗
      ∃ (serverRev : w64) (m : KvMap), isEtcdKvs serverRev cf.pfx m ∗
        ⌜sint.Z serverRev < sint.Z o.rev⌝) ∨
    (⌜o.serializable = false⌝ ∗ globalAddr ErrCacheTimeout ↦□ err) ∨
    (∃ st : StoreState, storeSeen cf.γs cf.scap r0 st ∗ snapErr (snapModel st o.rev) err ∗
      ⌜∀ r m, snapModel st o.rev ≠ .ok r m⌝))

/-- The `GetResponse` `Cache.Get` builds: `{Header: hdr, Kvs: kvs, Count: n}`. -/
def getRespVal (hdr : Loc) (kvs : GoSlice) (n : w64) : go_etcd_io.etcd.client.v3.GetResponse :=
  { (zero_val etcdserverpb.RangeResponse) with Header' := hdr, Kvs' := kvs, Count' := n }

/-- The `ResponseHeader` `Cache.Get` builds: `{Revision: rev}`. -/
def respHeaderVal (rev : w64) : etcdserverpb.ResponseHeader :=
  { (zero_val etcdserverpb.ResponseHeader) with Revision' := rev }

/-- `Cache.Get`'s answer, for a request on `key` with `Op` `o`: a fresh response (owned by the
caller) whose header revision is the store's latest revision in some state `st` (at least the
caller's `r0`), listing, in key order, the `*KeyValue`s of the snapshot `(r, m)` that
`getSnapshot(o.rev)` picks in `st` (`snapModel`: the greatest cached revision at most `o.rev`,
or at most `st.latestRev` for `o.rev = 0`) in the range `[key, o.rangeEnd)` (`kvRange`), with
its count; and `m` is etcd's state at `r` (`isEtcdKvs`). A linearizable request (not
`WithSerializable`) is moreover at least as fresh as etcd was when it started: etcd had a
state at a revision `serverRev`, at least the requested one, that the store's latest revision
has reached. -/
def cacheGetOk (cf : CacheFields) (r0 : w64) (key : GoString) (o : OpModel) (resp : Loc) :
    IProp GF :=
  iprop(∃ (hdr : Loc) (kvsSl : GoSlice) (st : StoreState) (r : w64) (m : KvMap),
    resp ↦ getRespVal hdr kvsSl (W64 (kvRange key o.rangeEnd m).length) ∗
    hdr ↦ respHeaderVal st.latestRev ∗
    kvsSl ↦* ((kvRange key o.rangeEnd m).map Prod.snd) ∗ ownSliceCap Loc kvsSl (DFrac.own 1) ∗
    kvsAt (kvRange key o.rangeEnd m) ∗
    isEtcdKvs r cf.pfx m ∗ storeSeen cf.γs cf.scap r0 st ∗
    ⌜snapModel st o.rev = .ok r m ∧ o.getUnsupported = false ∧
      validRange cf.pfx key o.rangeEnd = true⌝ ∗
    (if o.serializable then iprop(True)
     else iprop(∃ (serverRev : w64) (m' : KvMap), isEtcdKvs serverRev cf.pfx m' ∗
       ⌜sint.Z o.rev ≤ sint.Z serverRev ∧ sint.Z serverRev ≤ sint.Z st.latestRev⌝)))

/-- What `Cache.Get` returns: `nil` and an error (`cacheGetErr`), or a response
(`cacheGetOk`) and `nil`. -/
def cacheGetResult (cf : CacheFields) (r0 : w64) (s : context.ContextDesc (IProp GF))
    (key : GoString) (o : OpModel) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜resp = null⌝ ∗ cacheGetErr cf r0 s key o err) ∨
    (⌜err = GoInterface.nil⌝ ∗ cacheGetOk cf r0 key o resp))

end cache

theorem pairwise_le_getLast {V : Type} {f : V → Int} {l : List V}
    (h : l.Pairwise (fun a b => f a < f b)) {x y : V} (hx : x ∈ l) (hy : l.getLast? = some y) :
    f x ≤ f y := by
  obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.1 hy
  rcases List.mem_append.1 hx with hx | hx
  · exact Int.le_of_lt ((List.pairwise_append.1 h).2.2 x hx y (List.mem_singleton_self _))
  · rw [List.mem_singleton.1 hx]; exact Int.le_refl _

/-- What `snapModel st rev = .ok r m` means: `(r, m)` is a snapshot of the history, at a revision
at most `rev` (at most the latest revision for `rev = 0`), the greatest such; and (with
`StoreInv`) at most the latest revision. The latest revision itself need not be `r` even for
`rev = 0`: a progress notification moves it without a snapshot. -/
theorem snapModel_ok_spec {cap : Nat} {st : StoreState} {rev r : w64} {m : KvMap}
    (hinv : StoreInv cap st) (h : snapModel st rev = .ok r m) :
    (r, m) ∈ st.history ∧ sint.Z r ≤ sint.Z st.latestRev ∧
    sint.Z r ≤ sint.Z (if rev = W64 0 then st.latestRev else rev) ∧
    ∀ h' ∈ st.history, sint.Z h'.1 ≤ sint.Z (if rev = W64 0 then st.latestRev else rev) →
      sint.Z h'.1 ≤ sint.Z r := by
  unfold snapModel at h
  by_cases h0 : st.latestRev = W64 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  by_cases hn : sint.Z rev < 0
  · rw [ite_eq_left hn] at h; cases h
  rw [ite_eq_right hn] at h
  generalize hrev' : (if rev = W64 0 then st.latestRev else rev) = rev' at h ⊢
  by_cases hf : sint.Z st.latestRev < sint.Z rev'
  · rw [ite_eq_left hf] at h; cases h
  rw [ite_eq_right hf] at h
  cases hlast : (st.history.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev'))).getLast? with
  | none => rw [hlast] at h; cases h
  | some x =>
    rw [hlast] at h
    cases h
    have hmem := List.mem_of_getLast? hlast
    rw [List.mem_filter] at hmem
    refine ⟨hmem.1, hinv.hist_le _ hmem.1, by simpa using hmem.2, ?_⟩
    intro h' hh' hle
    -- the last element of the filtered (sorted) history is its greatest
    have hin : h' ∈ st.history.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev')) :=
      List.mem_filter.2 ⟨hh', by simpa using hle⟩
    exact pairwise_le_getLast (f := fun x : w64 × KvMap => sint.Z x.1)
      (hinv.hist_sorted.filter _) hin hlast

end EtcdGrove
end Perennial
