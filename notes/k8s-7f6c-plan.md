# k8s 7f-6 stage C, the bridge (Draft D1): plan (2026-11-16, branch `k8s-7f6c`)

Scope: `/shared/etcd-grove-k8s7f6/notes/k8s-7f6-scope.md` §3, §5 row C; Draft `notes/k8s-7f5a-draft.md`
§1-2. Target: from the store's `kStreamOk` (`WatchDefs.lean`, over `KVState`, `DObj`) to the driver's
`StreamOkL` (`KWatchStream.lean`, over `HSt`, `Obj`), the premise of `watchOkL_of_stream`.

**Status.** F1 was a hard stop (§2); decided by etcd-grove-02 2026-11-16: option 1, `KvNext` gains
`KvOne` (at most one change per step), every producer re-proved. Then the bridge as below, with the
forms of §4.

## 1. The target statement

New module `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/KWatchBridge.lean` (namespace
`k8s_etcd3`), importing `KWatchStream` (the driver's pure check), `RefineList` (`KRelH`, pure) and
`Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs` (the store's vocabulary); nothing of the
driver's Go proofs.

```lean
/-- etcd's history, as the bridge reads it (pure, at the configuration's state `σ`). -/
structure KHistW (σ : KVState) : Prop where
  comp : σ.compacted = 0                                          -- F0
  wf : ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs,                            -- kvWfHist c σ under CfgD c
    (kpfxD <+: v.key → driverCodec.dec v.value ≠ none) ∧ 0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ r
  keys : ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, ∃ n, v.key = mkeyL n     -- from KOk.keys (keysOk σ)
  one : ∀ r ≤ σ.rev,                                               -- F1: NOT GIVEN (§2)
    ((σ.changesAt r).filter fun ch => decide (kpfxD <+: ch.key)).length ≤ 1

/-- The request's mode as the driver makes it (`genWatch`, `watchOptions`). -/
def kModeOk (x : Input) (req : Nat) (m : KWatchMode) : Prop :=
  m.req = req ∧ (x.SendInit' = W64 2 → m.forceInit = true ∧ m.bmReq = true) ∧
    (x.SendInit' ≠ W64 2 → m.forceInit = false)

/-- A store event as the driver records it (`toWEvent` of `wevAt`'s object). -/
def kToWEv (e : KWEv DObj) : WEv := ⟨e.t, { e.o.toObj (W64 (e.rv : Int)) with Annotated' := e.ann }⟩

/-- The driver's record `w` of the store event `e` (an Error event's object is free). -/
def kWEvRel (e : KWEv DObj) (w : WEv) : Prop := w.t = e.t ∧ (e.t ≠ 4 → w = kToWEv e)

theorem streamOkL_of_kStreamOk (x : Input) (h : HSt) (σ σ0 : KVState) (k : GoString) (reqw : w64)
    (m : KWatchMode) (sel : DObj → Bool) (emp : Bool) (z : DObj) (st : Nat)
    (evs : List (KWEv DObj)) (ws : List WEv)
    (hrel : KRelH h σ) (hlen : h.hist.length = σ.rev) (hw : KHistW σ)
    (hk : prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k)
    (hsel : ∀ o, sel o = selD x o) (hemp : emp = true → ∀ o, sel o = true)
    (hm : kModeOk x (uint.nat reqw) m) (h0 : 1 ≤ σ0.rev) (hstart : kStartOk m σ0 st)
    (hs : kStreamOk driverCodec.dec sel emp z (kInScope (go!"/registry" ++ k) x.Recursive') m σ st evs)
    (hws : List.Forall₂ kWEvRel evs ws) :
    StreamOkL x (uint.nat reqw) h.hist ws
```

With it (same module):
- `histWf_of_krel (x) (hrel : KRelH h σ) (hlen) (hw : KHistW σ) : HistWf x h.hist` (`watchOkL_of_stream`'s
  other premise);
- `kStreamOk_hist (h : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) : kStreamOk … σ st evs → kStreamOk … σ' st evs`
  (the stream's state, where `Q` fired, to the configuration's at the linearization point: Scope §6);
- `sieOfL x` (`SendInit` 2/1/other ↦ `some true`/`some false`/`none`) and `kModeOk_of`:
  `(x.SendInit' = 2 → x.Bookmarks' = true) → (x.SendInit' ≠ 2 → x.SendInit' = 1 ∨ 0 < uint.nat reqw) →
  kModeOk x (uint.nat reqw) (kModeOf (sieOfL x) x.Bookmarks' reqw)` (both facts of `genWatchFrom`, stage B).

Premise sources (stage E): `hrel`, `hlen`, `KHistW.wf`/`.keys` from `KOk` (`cfg`, `hwf` with `CfgD`,
`keys`); `KHistW.comp` from the boot state (`kvStateOf …`) and `KvExt` (keeps `compacted`): a new `KOk`
conjunct; `hsel`/`hemp` from `selPredOk` of `watchOptions x` (stage D); `hm` from `kModeOk_of`;
`hstart`, `hs` from `kResElem`; `h0` from E's `Q` (the store's `Q` laws do not give `1 ≤ σ.rev`;
E's `Q` fires at states of the configuration's history, revision at least the boot state's `1`); `hws` from `wevAt` and `toWEvent` (stage D).

F2 (`createRev` of a key-value at revision `r-1` is not `r`, so that `kEvOfL`'s create test agrees with
the driver's "absent before") is **derived** from `comp` and `wf` (`wf` at `r = 0` makes the base
empty; every later key-value was created by a put: `createRev ≤ modRev ≤ r - 1`).

## 2. The missing fact F1 (one change under the prefix per revision): counterexample

`oneKeyRevs` says each revision changes the *state* at one key under the prefix at most (its ghost
entries are `chgOf` of consecutive states); the store's `KTail` is over etcd's *events*
(`revEvents r`: one per change). They differ when a revision's changes touch one key twice:

- `σ`: `compacted = 0`, base empty, revision 1 no change, revision 2's changes
  `[put K v1, put K v2]` with `K = mkeyL n`, `v1`, `v2` decoding to `o1 ≠ o2`, both selected.
  `KRelH` holds with the driver's history `[∅, {n ↦ o2@2}]`; `kvWfHist` holds; the ghost entry at 2 is
  `[(K, some v2)]`, so `oneKeyRevs` holds.
- A watch from revision 1 (legacy match, `req = 1`): `KTail.chg 1 2` gives the ideal stream
  `[Added o1@2, Added o2@2]` (both puts' key-values have `createRev = modRev = 2`), so `kStreamOk`
  holds of `evs = [Added o1@2]`.
- The driver's `evAtL 2 = Added o2@2`: no `TailOk` from 1 starts with `Added o1@2`; `StreamOkL` fails,
  and `watchOkL` rejects (`eventsEqual`). The bridge is false without F1.

Also not available: `NoDupKeysPerRev` of the server's log (v3rpc checks it per request, the server's
state does not carry it), which with `LogWf'` and `oneKeyRevs` would give F1.

**Recommendation.** Strengthen the store's update report: `KvNext σ σ'` (`Updates.lean`) gains, in its
step disjunct, `∃ cs, σ'.changes = σ.changes ++ [cs] ∧ cs.length ≤ 1` (the store's transactions are
`putTxn`/`delTxn`, one operation each, so `kvOpStep` commits at most one change; `kvNext_step` gains the
op's single-write premise). Stage E then carries `∀ cs ∈ σ.changes, cs.length ≤ 1` (the k8s
compactor's `OneChange`, `compactor/KeyHist.lean`) in `KOk` from the boot state, and `KHistW.one`
follows. This is a change to the store's exported update spec (7e/7f-5's), hence the stop.
Alternative: F1 stays a named premise of the bridge, and its producer is decided at stage E.

## 3. Lemmas (internal, all pure, in the new module)

1. `at_succ_kvs`: `compacted = 0`, `1 ≤ r ≤ rev` → `(σ.at r).kvs = applyChanges (W64 r) (σ.at (r-1)).kvs (σ.changesAt r)`.
2. `base_nil`, `createRev_le`: from `comp` and `wf` (F2).
3. `rev_cases`: at `2 ≤ r ≤ rev`, the in-scope events of revision `r` and the change: none under the
   prefix (the states agree under the prefix; any in-scope event is a delete of an absent key, which
   `kEvOfL` drops), or the one change `ch` at `K = mkeyL n` (put/delete, present/absent before),
   every other key under the prefix unchanged (`findKey_applyChanges_other`).
4. `changeAtL_one`: two sorted item lists agreeing at every name but `n` give the change at `n` (none
   if they agree there).
5. `evAtL_eq`: `(kEventsInL … σ inS r (r+1)).map kToWEv = (evAtL x h.hist r).toList` for `2 ≤ r ≤ rev`
   (`kEvOfL`'s cases against `toEventL`'s; `selOkL` reads no resource version; `kPrevAt` is
   `histN (r-1)`'s item through `KRelS`).
6. `noEv_of_kRange_nil`: no in-scope etcd event in `(c, p]` → `evAtL` none there.
7. `tailOk_of_kTail`: `KTail … σ inS c full`, `1 ≤ c` → `TailOk x h.hist c (full.map kToWEv) ∧
   NoAnn (full.map kToWEv)`; `TailOk.prefix` (prefix closure).
8. `initial_eq`: `(kInitialL … (σ.at r)).map kToWEv = initialEventsL x (histN h.hist r)`, `1 ≤ r ≤ rev`
   (from `scopeL_eq`/`storeScope`).
9. `nonErr_rel`: `Forall₂ kWEvRel evs ws` → `nonErr ws = (kNonErr evs).map kToWEv`.
10. `histN_eq`: `histN hs r = histAtL hs (W64 r)` for `r < 2^64`.
11. The theorem: the two modes (watch-list: prefix of `initial ++ [bm] ++ tail` splits into a prefix of
    the initial events, or all of them, the bookmark and a prefix of the tail; otherwise a prefix of a
    tail), then `histWf_of_krel`, `kStreamOk_hist`, `kModeOk_of`.

Estimate 700-1100 lines, as the Scope's.

## 4. Forms decided while proving (form decided by the agent, reviewed at checkpoint)

- `KHistW.keys` dropped; `streamOkL_of_kStreamOk` and `histWf_of_krel` take `hlk : "/objs/" <+: x.WKey'`
  instead (as `refine_list`'s `hlk`; `genWatchFrom`'s keys are all `ResourcePrefix + "/" + …`): the scope
  is then under `"/registry/objs/"`, every key in it a name's.
- `histWf_of_krel` takes `k`, `hk`, `hlk` (it reads the events through `evAtL_eq`).
- F1's form: `KvOne σ σ'` (`Updates.lean`): `∀ cs ∈ σ'.changes.drop σ.changes.length, cs.length ≤ 1`, the
  fourth conjunct of `KvNext`'s step; `kvNext_step`/`kvNext_commit` take it (`hone`, `cs.length ≤ 1`);
  `k8sAu1_kvAu1`, `k8sAuRW_kvAu1`, `k8sAusRW_kvAu1` take `hone : ∀ σ, kvWf c σ → KvOne σ (kvOpStep op σ)`,
  discharged by `kvOne_optPut`/`kvOne_optDel` (`Steps.lean`) and `seedOp_one` (`Seed.lean`).
