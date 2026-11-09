# k8s etcd3 stage 7e-2: Draft (2026-11-08, branch `k8s-7e`; for etcd-grove-81's review, no Lean yet)

The exact statement text of everything 7e-2 adds or changes on the store's paginated list path
(`notes/k8s-7e-scope.md` §4-§7, approved), each item with its status, its producer and its Go
evidence. The text below is not built; names follow the repository's (checked against the
worktree at `c0c3bb5a66` and lean's 7c-2 vocabulary). Pins: `k8s.io/apiserver` `9c4ec15b8038`
(below `apiserver/`), `k8s.io/apimachinery` `0b7d352f711c` (`apimachinery/`), etcd fork
`673da07c8f` (`client/v3/kubernetes/client.go`), all from `go env GOMODCACHE`
(`/root/go/pkg/mod`); translations in `Code/k8s_io/apiserver/pkg/storage{,/etcd3}.lean`.

## Revision after the attack (2026-11-09; decided by etcd-grove-81)

The trusted statements were attacked before any Lean (`notes/k8s-7e-2-attack.md`, Go probes in
`examples/k8s7e2attack/`). Changes, made in place below:

1. **`reflect.MakeSlice` (T8, refuted as stated)**: new premise `sint.Z m ≤ 2 ^ 41` (gc refuses an
   allocation above `maxAlloc` = 2^48 bytes with a panic; `sizeof(Obj) = 112`, 2^41·112 < 2^48).
   Carried into `listContractOk'`'s two `MakeSlice` clauses and `growSlice.spec` (`sint.Z mx ≤ 2 ^
   41`: the cap `growSlice` asks for is at most `mx`). New requirement on 7e-1 (`notes/k8s-7e-scope.md`):
   `Client.List`'s post bounds `len(Kvs) ≤ 2 ^ 41`.
2. **The list metrics (T16-T17)**: premises `0 ≤ sint.Z` of the three counts and `utf8Valid` of every
   label (registered metrics panic otherwise). **R1, new item**: the existing `RecordEtcdRequest` and
   `RecordDecodeError` axioms get the `utf8Valid` premises too (a trust-base repair, restated here and
   fixed in 7e-2's Lean; `nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`). `isStore`
   (#15) gains `utf8Valid` of the store's `groupResource`; `numFetched`/`numEvald` are non-negative by
   the pages' key bound (change 5).
3. **`leafErrTy`** (§4.5) is defined: no `Unwrap() error`, no `Unwrap() []error`, no `As(any) bool`
   method (`errors.As` follows all three; the attack's `asErr`/`joinErr`). `knownReasons` is the 19
   reasons of `errors.go:49-67`, without `""` (`StatusReasonUnknown`).
4. **`reflect.Value.IsNil`**: post `⌜b = true → uint.Z s.len = 0⌝` (was "some bool", too weak:
   `finalizeList`'s `true` branch empties the items). `ListSpec` gains `itemsAt_len`.
5. **`store.getList.spec`** gains `lo.Continue'.length ≤ opKeyMax` (`Client.List`'s premise); the
   later pages' continue key is the last key and `"\x00"`, so `GetList.spec` and `pagedChunks.spec`
   take `kvKeysShort σ` from `Q` (every key of every revision of `σ` is shorter than `opKeyMax`),
   *hypothesis-until-7e-4*, from the driver's writes (each `pathPrefix ++ name` of the finite
   workload, far below `opKeyMax` = 2^27; recorded with `kvWfHist` in `γ.r`). It also bounds the
   pages' total keys (the store is finite and its keys distinct), hence the metrics' counts.

Trusted texts by count: 14 new, 5 restated (R1 adds two), as revised.

**Status words.** *proved*: a spec with a proof in 7e-2 (from translated code and existing or listed
specs). *trusted*: a trust-boundary axiom (new or restated), with why it is faithful; each one goes
through the `axiom` skill before the Freeze. *hypothesis-until-X*: a premise or callee spec that X
produces; until then it is a binder of the proof (no axiom).

## Corrections (2026-11-09; decided by etcd-grove-81 under the user's delegation of 2026-11-07)

Found when 7e-2's Lean started (before any was written); `questions.md`, "k8s 7e-2: corrections".
They supersede the text of §1, §2 and §8 below where they differ. 7e-4 discharges every new premise
from the driver; one that would surface as a premise of a closed theorem goes to the user.

- **R1** (§8, the statement was false): `refine_list`'s too-large case is `σ.rev < uint.nat n` for
  both reads (for a past read `R = n`, so this is `GetList`'s two branches):
  ```lean
      (if σ.rev < uint.nat n then tooLargeL = mlistL x h
       else listOutDriver x (if uint.Z R = 0 then W64 (σ.rev : Int) else R) a = mlistL x h)
  ```
- **R2** (§8): premise `x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2` (`matchOptL` reads
  any other value as the legacy match, `pastReadL` only `0`). Producer: `genList`.
- **R3** (§8): premise `go!"/objs/" <+: x.ListKey'` (else the scope may hold `"/registry/objs"`,
  under the store's prefix but no driver item). Producer: `genList`.
- **R4** (§8, gaps filled): the selector is `fun o : DObj => selOkL x (o.toObj (W64 0))`;
  `listOutDriver x R a` is the driver's `listOut` of `listIs`'s list; `KRelH h σ` relates `h.st` to
  `absK driverSpec.dec c.pfx` of `σ` and `histAtL h.hist r` to that of `σ.at r` for `1 ≤ r ≤ σ.rev`
  (`KRel`'s form, with `ItemRel` comparing the whole object, `it.obj' = ki.obj.toObj (W64 ki.rv)`),
  and `(histAtL h.hist r).rv = W64 r`. In a new module (`Refine.lean` waits for 7e-4); 7e-4 adopts
  this `ItemRel`.
- **G1** (§2): `store.GetList.spec` takes `uint.Z n < 2 ^ 63` (`ValidateListOptions`' `int64(parsedRV)`
  would be negative, and etcd reads a revision `≤ 0` as the current one:
  `nonissues/k8s-etcd3-list-exact-rv-above-int64.md`). Producer: the driver's `minRV`.
- **G2** (§2): `store.GetList.spec` takes `0 ≤ sint.Z opts.Predicate'.Limit'` (`pagedChunks` and
  `Client.List` require it). Producer: `genList` (limits 0, 1, 2).
- **G3** (§2, §3.5): `kvKeysShort σ := ∀ R ≤ σ.rev, (σ.at R).kvs.length < 2 ^ 41 ∧ ∀ kv ∈ (σ.at R).kvs,
  kv.key.length < opKeyMax` (`hasMore := int64(len(Kvs)) < Count` and the metrics' sums need the
  key count below `2^63`; "finite with distinct keys" does not bound it). It also gives 7e-1's
  `len(Kvs) ≤ 2 ^ 41`. Producer: 7e-4 (the driver's workload keys).

**Forms settled at Prove (first third, 2026-11-09; accepted by etcd-grove-81):** `reflect.Append`
takes the variadic one-element slice `esl ↦*{dqe} [e]` (for `sliceV [#e]`); `ApiErrView.status st
cs` carries the causes (the Draft's `causesOf st` cannot be a function of `st`, which holds only the
details' address): `statusDetailsAt st cs` is `st.Details' = null ∧ cs = []`, or `st.Details' ↦□ d ∗
d.Causes' ↦*□ cs`, so `cs` is the heap's; `leafErrTy` is stated with
`GoSemanticsFunctions.methodSet t !! m ≠ some sig` for `Unwrap() error`, `Unwrap() []error`,
`As(any) bool`; `RawURLEncoding_init` gives `↦□` (weaker than `↦`); `json.Marshal`'s post is `sl ↦*
tokJson rv start` (no `.toBytes`: a `GoString` is bytes); `Value.Kind` returns `#(W64 23)`
(`reflect.Slice`, inlined by the translation).

**Forms settled at Prove (second third, 2026-11-09; accepted by etcd-grove-81):** the
`SelectionPredicate.Matches` spec and `getAttrsOk` are stated for any object predicate `objAt`
(the store's use is `objAt := S.objAt _ _ rv`; `mlist` calls `Matches` on `&o ↦{dq} o`);
`predOk_driver` takes its callee specs as premises and selects by `selD x` (R4's filling for
`selOkL x`); `mlist`'s callee triples `mlistMatches`/`mlistPCT` (`examples/k8s/etcd3/PredOk.lean`)
require the driver's package initialization; `labels.Set.{Get,Has}`, `fields.Set.Get` keep the
non-`nil` premise, the `nil` maps handled in the selector proofs.

**Forms settled at Prove (second third, part 2, 2026-11-09; accepted by etcd-grove-81, with D1-D3 below):**
(1) `listContractOk'`'s `…` spots are filled one clause per reflect call: `GetItemsPtr` (as the
Draft); `MakeSlice(rt, 0, m)` giving `L.itemsAt s' []`; `MakeSlice(rt, n, m)` for `n = |os|` giving
`w`, `s'` and a one-shot wand for `Copy(w, v)` that moves `L.itemsAt s os` to `L.itemsAt s' os` and
returns `#(r : w64)`; `Append(v, esl)` with `esl ↦*{dqe} [e]`, `reflElem e S.objTy q` and
`S.objAt (mkOk *objTy q) o rv`, giving `L.itemsAt s' (os ++ [(o, rv)])` (the composite-WP form of
the Draft does not fit the translation, which stores `MakeSlice`'s result in a local between the
calls); (2) `ListSpec` gains the law `itemsAt_wf : itemsAt s os ⊢ ⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤
sint.Z s.cap⌝` (`ownSliceCap_wf` for the driver): `growSlice`'s `MakeSlice(rt, v.Len(), max)` needs
`len ≤ max` from `max > cap`; (3) `listErr`'s 410 is `∃ st, apiErrAt err (.status st []) ∗
⌜st.Reason' = "Expired" ∧ st.Code' = 410⌝` (the Draft's `expiredStatus` predates the `.status st cs`
form; producing it needs `NewResourceExpired.spec`'s post to add `st.Details' = null`, true of its
literal); (4) `validateMinimumResourceVersion.spec`'s post is `if … then tooLargeErrIs err else
⌜err = nil⌝` (an Iris `if`, as `tooLargeErrIs` is spatial-persistent).
**D1-D3 (decided by etcd-grove-81, 2026-11-09):** D1: `ErrCompacted_init`, `ErrFutureRev_init` and
`rpctypesInit` state the globals' dynamic type, `∃ x : EtcdError, e = mkOk EtcdError.ty #x` (a
trust-base restatement, attacked by a Go test under `examples/`; the TCB baseline changes at
linking), and `readErrIs` takes the client branch of `unkErr`; D2: `New.spec` gains `utf8Valid
gr.Group'`, `utf8Valid gr.Resource'`, the two aggregator-factory specs return `aggrFactoryOk`, and
`isStore` gains its conjuncts (#15); D3: `NewResourceExpired.spec`'s post adds `st.Details' = null`.

**Decided by etcd-grove-81 (2026-11-09, at the start of the last third):** `New.spec`'s
`threadBound GF ≤ 2 ^ 30 - 1` accepted; `interpretListError` takes `kClientErr` accepted;
`listReadError`'s key premise (`∃ k, prepareKeyM c.resourcePrefix c.resourcePrefix false = some k ∧
(c.pathPrefix ++ k).length ≤ opKeyMax`) accepted, with the condition that `GetList` derives it from
its own key premise rather than adding one (see the blockers below: it does not follow).

**Forms proposed at Prove (last third, 2026-11-09; for etcd-grove-81):**
(1) `ctxNeverDone ctx` (§3.4, named but not defined): `∃ ci, ctx = ok ci ∗ □ (Done() returns the
`nil` channel)` (`ListDefs`); (2) `appendChunk.spec` gains the premises `∀ kv ∈ kvs, 0 ≤ sint.Z
kv.modRev` (processListItem's `fmtRV kv.modRev` against `itemsOf`'s `fmtRV (W64 (sint.nat …))`) and
`kvs.length ≤ 2 ^ 41` (`growSlice(v, len(kvs))`'s `mx` bound when the predicate is empty), and its post
gives the count `n` of key-values evaluated: `ev = W64 n`, `n ≤ len`, all of them unless the limit
was reached, `lastKeyIs lk kvs n` (`nil` or the `n`-th key), and, when the limit is reached or the
bucket full, that key is `st'.last` (what `GetList`'s continue key needs); the Draft's App count
for `appendChunk` was one too many (7 arguments); (3) `chunkL` (Draft: `ListModel.chunkL`) is in
`ListDefs` (sparing the driver a rebuild), with `decodedL`, `itemsOf`, `lastKeyIs`; (4) the binders
of `finalizeList.spec` include the v3rpc `Assumptions` instance (`isStore` needs it); (5) new callee
`store.getResourceSizeEstimator` (spec + proof: `isStore ∗ threadTok`, returns `nil`, borrowing a
reader token from `storeListOk`'s pool).

**Blockers found in the last third (2026-11-09; stop, for etcd-grove-81):**
- **B1 (`listReadError`'s key premise does not follow from `GetList`'s).** `prepareKeyM rp key r =
  some k` gives `rp <+: k` and no `.`/`..` segment in `key`, but says nothing of `rp`'s own segments:
  `rp = "/r/."`, `key = "/r/.x"` satisfies `GetList`'s premise while `prepareKeyM rp rp false = none`
  (`"/."` is a suffix of `rp`); `rp = []` too. The length half follows. Options: (a) `isStore` (or
  `StoreCfg`) records `prepareKeyM c.resourcePrefix c.resourcePrefix false = some c.resourcePrefix`,
  established by `New` (a premise of `New.spec`, which the driver discharges by `decide` on
  `"/objs"`); (b) `GetList.spec` takes it (refused by 81). Recommended: (a).
- **B2 (the context's `Done()`).** `processListItem` selects on `ctx.Done()`; a done context returns
  `NewTimeoutError` (a `*StorageError`), which `GetList`'s post (`listErr`: `unkErr` or the 410) does
  not allow, and `ctxOk`/`ctxErrClient` say nothing of `Done()`. `GetList` passes `tracing.Start`'s
  derived context, whose trusted spec gives only `ctxOk ci' cd ∗ ctxErrClient ci' cd`. Needed:
  `GetList.spec` takes `ctxNeverDone (GoInterface.ok ci)` (the driver's `context.Background()`:
  Perennial's `wp_background_Done`), and `tracing.Start.spec` (trusted) is restated to carry it to
  `ci'` (OpenTelemetry's value context delegates `Done` to its parent, as its docstring already
  says). Alternative: `listErr` admits the timeout error and the select's `Done` case gets a spec.
  Recommended: the restatement (a trust-base change: an attack before linking).
- **B3 (mod revisions of past reads).** `GetList`'s post reports each item's resource version as
  `fmtRV (W64 (sint.nat kv.modRev))` (`kListL`), the store as `fmtRV kv.modRev`; they agree only if
  `0 ≤ sint.Z kv.modRev`. `kvWf` gives it for the current store (`KWf`), nothing for `σ.at R` (the
  base's key-values overwritten later keep any mod revision). Recommended: `kvWfHist` also states
  `0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ r` (as `KWf`), same producer (7e-4).
- **B4 (client vocabulary the Draft names without text).** `getList` needs `Client.List.spec`
  (§7's text uses `rangeErrSound`, defined nowhere; `notes/k8s-etcd3-plan.md` describes it) and a
  `Client.Get` at a revision (§7: prose only; the existing `Client.Get.spec` requires
  `opts.Revision' = 0`). Needed: `rangeErrSound`'s text and a name and text for the revision `Get`
  hypothesis (or 7c-3's restated `Client.Get.spec`). Recommended: `rangeErrSound o Q err :=
  □ (⌜errDesc err = futureRevDesc⌝ -∗ ∃ σ, □ Q (W64 σ.rev) σ ∗ ⌜σ.rev < sint.nat o⌝)` (the future
  half, all `readErrIs` uses) and a hypothesis `Client.GetAt.spec` with §7's answer, both premises of
  `getList`'s proof only.

## 0. Summary

| # | Item | Status | Producer |
|---|---|---|---|
| 1 | `store.GetList.spec` | proved | 7e-2 |
| 2 | `store.pagedChunks`, `store.getList`, `store.listReadError`, `interpretListError` | proved | 7e-2 |
| 3 | `store.appendChunk`, `store.processListItem`, `growSlice`, `getNewItemFunc`, `store.finalizeList`, `shouldStream` | proved | 7e-2 |
| 4 | `storage.ValidateListOptions`, `PrepareContinueToken` (final, generic), `EncodeContinue` | proved | 7e-2 |
| 5 | `SelectionPredicate.{Matches,Empty,MatchesSharding,ShardingEnabled,labelFieldEmpty,MatchesObjectAttributes,SetShardInfoOnList}` | proved (translated) | 7e-2 |
| 6 | `fields.Set.Get`, `labels.Set.{Get,Has}` | proved after a re-translation (recommended; trusted otherwise) | 7e-2 |
| 7 | `storage.IsTooLargeResourceVersion`, `NewTooLargeResourceVersionError` (post strengthened) | proved | 7e-2 |
| 8 | `apierrors.IsTimeout` (new), `apierrors.HasStatusCause` (restated) | trusted | here |
| 9 | reflect: `Value.{Kind,Len,Cap,IsNil}`, `Type.Elem`, `MakeSlice`, `Copy`, `Append`; restated `Value.Set`, `ValueOf` | trusted | here |
| 10 | `meta.GetItemsPtr` (the driver's list type) | trusted | here |
| 11 | `json.Marshal` (the continue token), base64's `RawURLEncoding` (restated `base64Init`, new init axiom) | trusted | here |
| 12 | `metrics.RecordStorageListMetrics`, `metrics.RecordListLatency` | trusted (no-ops) | here |
| 13 | the gate fact (`featureGateOk`, `featureOff`, `Set`) | trusted, B5's text (`/shared/tmp/sweep-repairs-1/b5-r1.md`), used as is | sweep repairs 1 |
| 14 | the list contract `ListSpec`, `listContractOk` (decoder's `DecodeListItem`, versioner's `UpdateList`, the reflect calls on items) | premise of `GetList`; proved for the driver | 7e-2 (driver side) |
| 15 | `isStore` gains the aggregator factory, `collectorMux`'s reader pool and `utf8Valid` of its `groupResource` | definition change; `New`'s proof | 7e-2 |
| 16 | `kubernetes.Client.List.spec` (as consumed) | hypothesis-until-7e-1 | 7e-1 |
| 17 | `kubernetes.Client.Get.spec` at a revision (as consumed) | hypothesis-until-7c-3 | 7c-3 |
| 18 | `Q`'s facts: one history, every revision well formed | hypothesis-until-7e-4 | 7e-4 (`readQ`, `γ.r`) |
| 19 | `threadTok` for `collectorMux.RLock` | hypothesis-until-7e-4 | lintest's `applySpec` (lent token) |
| 20 | ETooLarge: `respIs`'s `.tooLarge` case, `store.Get.spec`'s post (by `respIs`) | changed statement, proved | 7e-2 |
| 21 | driver: `decoder.DecodeListItem`, `versioner.UpdateList`, `getAttrs`, `objLabels`, `fieldSel.Matches`, `labelSel.Matches`, `listOut`, `noStreaming` | proved | 7e-2 (driver functions) |
| 22 | 7e-3b's two hypothesis files (`SelectionPredicate__Matches`, `PrepareContinueToken`) | replaced by #5 and #4 and the driver's `predOk_driver` | 7e-2 |
| 23 | `encL` (`KList.lean`): `opaque` becomes a definition from #11's opaque functions | changed definition | 7e-2 |
| 24 | `refine_list` (the model relation the store's post feeds) | stated here, proved in 7e-3c | 7e-3c |
| R1 | `metrics.RecordEtcdRequest`, `metrics.RecordDecodeError`: `utf8Valid` label premises (a trust-base repair, attack R1) | trusted, restated | here |

Axioms by count: 14 new (#8: `IsTimeout`; #9: `Kind`, `Len`, `Cap`, `IsNil`, `Type.Elem`, `MakeSlice`,
`Copy`, `Append`; #10: `GetItemsPtr`; #11: `json.Marshal`, `RawURLEncoding_init`; #12: two metrics),
3 restated (`HasStatusCause`, `reflect.Value.Set`, `reflect.ValueOf`; after the attack 5, with R1's
`RecordEtcdRequest`, `RecordDecodeError`), the trusted fact `base64Init`
restated, two new opaque functions (`tokJson`, `rawUrlEnc`; no axiom), plus B5's (#13, counted
there). The scope estimated 10-14; with #6's re-translation refused, 17 (its three as axioms).

## 1. Vocabulary (new module `Proof/k8s_io/apiserver/pkg/storage/etcd3/ListDefs.lean`, pure part)

```lean
/-- **A list's scope** (`store.go:1081-1100`): recursive, the keys under the prepared prefix `kp`
(`kubernetes.Client.List`'s range `[kp, GetPrefixRangeEnd kp)`, `client.go:59-73`); not recursive,
the key `kp` itself (`kubernetes.Client.Get`, `client.go:47-57`). -/
def kInScope (kp : GoString) (rec : Bool) (k : GoString) : Bool :=
  if rec then decide (kp <+: k) else decide (k = kp)

/-- **The store's list over the store `s` at the list's revision**: the key-values of the scope in
key order, each decoded by `dec` (`ObjSpec.dec`) with its mod revision, through 7e-3a's loop
(`ListModel.loop`): the first `lim` the predicate `sel` selects (all for `lim = 0`), whether a key in
scope follows the `lim`-th match (`more`), the last match's key, and the count of keys in scope. -/
def kListL (dec : Dec Obj) (sel : Obj → Bool) (lim : Nat) (kp : GoString) (rec : Bool)
    (s : KVStore) : ListModel.LState w8 (Obj × Nat) :=
  ListModel.loop (fun x => sel x.1) lim
    ((s.kvs.filter fun v => kInScope kp rec v.key).filterMap fun v =>
      (dec v.value).map fun d => (v.key, (d.1, sint.nat v.modRev)))

/-- A list's limit as a count (`opts.Predicate.Limit`; none for `≤ 0`). -/
def limN (l : w64) : Nat := if 0 < sint.Z l then sint.nat l else 0

/-- **Two states of one history**: the same base and compaction revision, one's changes a prefix
of the other's (so they agree at every revision both keep: `kvSameHist_at`). -/
def kvSameHist (σ σ' : KVState) : Prop :=
  σ.compacted = σ'.compacted ∧ σ.base = σ'.base ∧
    (σ.changes <+: σ'.changes ∨ σ'.changes <+: σ.changes)

theorem kvSameHist_at (σ σ' : KVState) (r : Nat) (h : kvSameHist σ σ') (hr : r ≤ σ.rev)
    (hr' : r ≤ σ'.rev) : σ.at r = σ'.at r   -- proved (pure)

/-- **Every revision of `σ` is the store's** (D30i, at each revision a past read may read): the key-
values under the prefix decode. -/
def kvWfHist (c : StoreCfg GF Obj) (σ : KVState) : Prop :=
  ∀ r, r ≤ σ.rev → ∀ v ∈ (σ.at r).kvs, c.pfx <+: v.key → c.S.dec v.value ≠ none

/-- **The revision a list reads** (`ValidateListOptions`, `interfaces.go:372-410`): its resource
version `n` for `Exact`, and for the legacy match when recursive with a limit and `n > 0`; else
(`0`) the latest. -/
def listRevL (m : GoString) (rec : Bool) (lim : w64) (n : w64) : w64 :=
  if m = go!"Exact" then n
  else if m = [] ∧ rec ∧ 0 < sint.Z lim ∧ 0 < uint.Z n then n else W64 0
```

`kListL` reuses `ListModel.loop` (7e-3a), whose `last` is the last *match*: the store's `lastKey`
is the last *evaluated* key (`store.go:1066`), and the two agree whenever `more` holds (after the
`lim`-th match the next key stops the loop before `lastKey` is set: `store.go:1064-1066`, or the
chunk ended at it: `store.go:847-850`). The lemma `kListL_last` states it for the proof; only `more`'s
token reads `last`. The single pass stands for the pages: with a non-empty predicate the store pages
with a doubling limit (`store.go:907-915`) and reads `count` from the last page, but then it reports
no remaining count (`continue.go:116`); with an empty predicate (every object selected,
`selPredOk`'s third conjunct) one page holds the first `lim` keys (`store.go:852-855`).

## 2. The store's spec (`Spec/k8s_io/apiserver/pkg/storage/etcd3/store__GetList.lean`) — proved

```lean
/-- **A list's answer** in the list object `lx`: the items (each object at its mod revision's string),
the list's resource version, the continue token (`encL` of the last match's key and `"\x00"`, the
prefix and the revision, iff more) and the remaining count (iff more and the predicate is empty). -/
def listIs (c : StoreCfg GF Obj) (L : ListSpec GF Obj) (kp : GoString) (emp : Bool) (lim : w64)
    (R : w64) (a : ListModel.LState w8 (Obj × Nat)) (lx : GoInterface) : IProp GF :=
  L.listAt lx (a.items.reverse.map fun x => (x.1, c.S.fmtRV (W64 (x.2 : Int)))) R
    (if a.more then encL (a.last.getD [] ++ [W8 0]) kp R else [])
    (if a.more ∧ emp then some (W64 (a.total : Int) - lim) else none)

/-- **A list's error** whose outcome tells nothing (the driver's `EOther`): the client's, or the
410 `interpretListError` makes of an `ErrCompacted` (no compaction happens, but 7e-2 does not need
to rule it out: a failed read is accepted, `step`'s first case). -/
def listErr (c : StoreCfg GF Obj) (err : GoInterface) : IProp GF :=
  iprop(unkErr c err ∨ apiErrAt err (.status expiredStatus))

abbrev store.GetList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (L : ListSpec GF Obj)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (lx : GoInterface)
    (rv0 : w64) (cont0 : GoString) (rem0 : Option w64)
    (k : GoString) (n : w64) (sel : Obj → Bool) (emp : Bool)
    (Q : w64 → KVState → IProp GF) (P : KVState → IProp GF),
  (∀ R σ, Q R σ ⊢ ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ R σ σ', Q R σ ∗ P σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ⌜prepareKeyM c.resourcePrefix key opts.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV opts.ResourceVersion' = some n ∧
        opts.ResourceVersionMatch' ∈ [[], go!"NotOlderThan", go!"Exact"] ∧
        opts.Predicate'.Continue' = []⌝ ∗
      selPredOk c.S opts.Predicate' sel emp ∗ listContractOk c L ∗ rangeStreamOff ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      L.listAt lx [] rv0 cont0 rem0 ∗
      (∀ R, |==> □ [∧list] x ∈ c.ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) ∗
      □ (|==> □ [∧list] x ∈ c.ms, ⌜P = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv P) }}
    (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"GetList")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #opts)) (Val #lx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((listErr c err ∗ ∃ os rv cont rem, L.listAt lx os rv cont rem) ∨
       (∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
         let R := listRevL opts.ResourceVersionMatch' opts.Recursive' opts.Predicate'.Limit' n
         if uint.Z R = 0 then
           -- a read at the latest revision, `σ`'s
           (if σ.rev < uint.nat n then tooLargeErrIs err ∗ ∃ os rv cont rem, L.listAt lx os rv cont rem
            else ⌜err = GoInterface.nil⌝ ∗ listIs c L (c.pathPrefix ++ k) emp opts.Predicate'.Limit'
              (W64 (σ.rev : Int))
              (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k) opts.Recursive'
                σ.store) lx)
         else
           -- a read at the past revision `R`
           (if σ.rev < uint.nat R then tooLargeErrIs err ∗ ∃ os rv cont rem, L.listAt lx os rv cont rem
            else ⌜err = GoInterface.nil⌝ ∗ listIs c L (c.pathPrefix ++ k) emp opts.Predicate'.Limit' R
              (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k) opts.Recursive'
                (σ.at (uint.nat R))) lx))) }}
```

Remarks (the reasons for the premises, with their producers):
- `Q` fires at the first page (its prophecy is the first response's header revision, as `Get`'s;
  D30n), `P` at every later page (each a read at the first page's revision, `store.go:893-898`).
  The answer is the first page's state's store at the read revision; later pages read the same
  store because `Q`'s and `P`'s states are of one history (`kvSameHist`, second premise).
  *hypothesis-until-7e-4*: the driver's `readQ` records each state it fires at in `γ.r` (`Inv.lean:693`),
  `P` is `plainQ` plus that record, and `kInv` makes the recorded states prefixes of one log. Item 18.
- `kvKeysShort σ := ∀ R ≤ σ.rev, ∀ kv ∈ (σ.at R).kvs, kv.key.length < opKeyMax` (revision after
  the attack, change 5): a later page reads from the last key and `"\x00"` (`store.go:903`), which
  `Client.List` needs within `opKeyMax`. Same producer as `kvWfHist` (the driver's keys).
- `kvWfHist`: a past read decodes the values of its revision (`processListItem`, `store.go:1037`):
  every revision's key-values under the prefix decode. Same producer.
- `P`'s update is persistent (`□ (|==> …)`): one per later page. `Q`'s is used once.
- `opts.Predicate'.Continue' = []` (the traffic never sets it: scope §1), so `DecodeContinue` is
  unreachable (`interfaces.go:373`) and `interpretListError`'s paging branch too (`store.go:902`).
- `parseRV` succeeds and the match is one of the three: else `ValidateListOptions` returns a
  `BadRequest`/an error (`interfaces.go:385-408`); the driver's inputs meet both (`rvBytes`,
  `matchOpt`).
- `threadTok`: `getList` calls `getResourceSizeEstimator` (`store.go:1104`, `store.go:279-283`), whose
  `collectorMux.RLock` needs a reader token (`Perennial/Proof/sync/RWMutex__RLock.lean`); per
  `notes/bounds-plan.md` the store owns the pool (#15) and the caller lends its thread token, as the
  lessor's specs do (`lessor__Leases.lean:37`). *hypothesis-until-7e-4*: lintest's `applySpec` lends
  `Apply` the token (`examples/lib/lintest/Defs.lean`, `applySpec`).
- `rangeStreamOff` (#13): `∃ g, globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□
  GoInterface.ok g ∗ featureOff g go!"EtcdRangeStream"`. Producer: the driver's `noStreaming` before
  `etcd3.New` (B5's `Set` triple); the `↦□` agrees with the package fact's.
- The latest read's too-large outcome is `validateMinimumResourceVersion`'s (`store.go:832-835`); the
  past read's is `ErrFutureRev` (7c's soundness: the state the read was served at is below `R`), then
  `listReadError` (`store.go:922-934`). In both the outcome is about the `σ` `Q` fired at.
- Go evidence (whole path): `store.go:763-860` (GetList), `:881-920` (pagedChunks), `:1005-1018`
  (finalizeList), `:1020-1053` (processListItem), `:1055-1079` (appendChunk), `:1081-1115` (getList),
  `:1117-1140` (growSlice), `:639-654` (getNewItemFunc), `:748-760` (shouldStream). 7e-0's Go runs
  (`TestMainLinearizable`/`Cluster`/`Partition` under porcupine, token bytes compared) exercise every
  branch the statement keeps.

## 3. The store's callees (all *proved*; `Spec/k8s_io/apiserver/pkg/storage/etcd3/`)

### 3.1 `shouldStream` (`shouldStream.lean`)

```lean
abbrev shouldStream.spec : Prop :=
  ∀ (opts : k8s_io.apiserver.pkg.storage.ListOptions) (Obj : Type) (S : ObjSpec GF Obj)
    (sel : Obj → Bool) (emp : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      selPredOk S opts.Predicate' sel emp ∗ rangeStreamOff }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.shouldStream)) (Val #opts))
  {{ RET #false; True }}
```
Go: `store.go:748-760`: false if not recursive, false for a limit with a non-empty predicate, else
`Enabled(EtcdRangeStream) && Supports(...)`, `false` by `featureOff` (B5's `Enabled` triple), and
`&&` does not call `Supports`.

### 3.2 `getNewItemFunc` (`getNewItemFunc.lean`)

```lean
/-- `newItemFunc` makes a fresh zero object, as `NewFunc()` does (`ObjSpec.newObj`). -/
def newItemOk (S : ObjSpec GF Obj) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ x, S.objAt x S.zero [] -∗ Φ #x) -∗
    WP (App (Val #f) (Val #())) {{ Φ }})

abbrev getNewItemFunc.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (L : ListSpec GF Obj) (pl : Loc) (v : reflect.Value),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      ⌜S.tyOk ∧ L.listTy ≠ k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.UnstructuredList.ty ∧
        reflElem v (go.GoType.SliceType S.objTy) (L.itemsRef pl)⌝ }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.getNewItemFunc))
      (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl))) (Val #v))
  {{ (f : GoFunc), RET #f; newItemOk S f }}
```
Go: `store.go:639-654`. From `reflect.Value.Type` (existing), `reflect.Type.Elem` (#9), `reflect.New`
and `Value.Interface` (existing), the `runtime.Object` assertion (`S.tyOk`), `S.newObj`. The
unstructured type's exact Lean name is the translation's (`k8s_io.apimachinery.pkg.apis.meta.v1.unstructured`).

### 3.3 `growSlice` (`growSlice.lean`)

```lean
abbrev growSlice.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (L : ListSpec GF Obj) (vp : Loc) (v : reflect.Value)
    (p : Loc) (s : GoSlice) (os : List (Obj × GoString)) (mx : w64) (szs : GoSlice) (zs : List w64),
  sint.Z mx ≤ 2 ^ 41 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      listContractOk' S L ∗ ⌜reflElem v (go.GoType.SliceType S.objTy) p⌝ ∗
      p ↦ s ∗ L.itemsAt s os ∗ szs ↦*□ zs }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.growSlice)) (Val #v)) (Val #mx))
      (Val #szs))
  {{ RET #(); ∃ s', p ↦ s' ∗ L.itemsAt s' os }}
```
Go: `store.go:1117-1140` (`Cap`, `MakeSlice`, `Copy`, `Set`: the items unchanged, the capacity
grown). `listContractOk' S L` is #14's reflect part. `sint.Z mx ≤ 2 ^ 41` (revision after the attack):
the cap asked of `MakeSlice` is at most `mx` (`max > maxCapacity` sets it to `mx`); `appendChunk` passes
`len(kvs)` (7e-1's bound) or `2048`.

### 3.4 `store.processListItem` and `store.appendChunk`

```lean
abbrev store.processListItem.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (L : ListSpec GF Obj)
    (ctx : GoInterface) (kvp : Loc) (kv : EtcdKv) (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool) (nf : GoFunc) (ag : GoInterface) (v : reflect.Value) (p : Loc)
    (s : GoSlice) (os : List (Obj × GoString)) (o : Obj),
  (∃ b, c.S.dec kv.value = some (o, b)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      listContractOk c L ∗ selPredOk c.S pred sel emp ∗ newItemOk c.S nf ∗ ctxNeverDone ctx ∗
      ⌜reflElem v (go.GoType.SliceType c.S.objTy) p⌝ ∗ txn.kvIs kvp kv ∗ p ↦ s ∗ L.itemsAt s os }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"processListItem")) (Val #ctx))
      (Val #kvp)) (Val #pred)) (Val #nf)) (Val #ag)) (Val #v))
  {{ RET (PairV #true #GoInterface.nil); ∃ s', p ↦ s' ∗
      L.itemsAt s' (if sel o then os ++ [(o, c.S.fmtRV kv.modRev)] else os) }}
```
(The hypothesis: the value reads as `o`, `kvWfHist`'s.) Go: `store.go:1020-1053`: `TransformFromStorage` (`transformerOk`; no error since
`dec` is `some`), the `ctx.Done()` select (`ctxNeverDone ctx`: the driver's `context.Background()`,
whose `Done()` is `nil`, so the `default` case runs; existing context specs), `DecodeListItem`
(#14), `pred.Matches` (`selPredOk`), `reflect.Append`/`ValueOf(obj).Elem()`/`Set` (#14, #9). The
aggregator is not reached.

```lean
abbrev store.appendChunk.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (L : ListSpec GF Obj)
    (ctx : GoInterface) (ksl : GoSlice) (ps : List Loc) (kvs : List EtcdKv)
    (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate) (sel : Obj → Bool) (emp : Bool)
    (nf : GoFunc) (ag : GoInterface) (v : reflect.Value) (p : Loc) (paging : Bool)
    (st : ListModel.LState w8 (Obj × Nat)),
  (∀ kv ∈ kvs, c.S.dec kv.value ≠ none) → paging = decide (0 < sint.Z pred.Limit') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      listContractOk c L ∗ selPredOk c.S pred sel emp ∗ newItemOk c.S nf ∗ ctxNeverDone ctx ∗
      ⌜reflElem v (go.GoType.SliceType c.S.objTy) p⌝ ∗ ksl ↦* ps ∗
      ([∗list] q;kv ∈ ps;kvs, txn.kvIs q kv) ∗
      (∃ s, p ↦ s ∗ L.itemsAt s (itemsOf c st)) ∗ ⌜st.more = false⌝ }}
    (App (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"appendChunk")) (Val #ctx)) (Val #ksl))
      (Val #pred)) (Val #nf)) (Val #ag)) (Val #v)) (Val #paging))
  {{ (lk : GoSlice) (ev : w64) (lr : Bool), RET (PairV (PairV (PairV #lk #ev) #lr) #GoInterface.nil);
      let st' := ListModel.chunkL (fun x => sel x.1) (limN pred.Limit') st (decodedL c.S.dec kvs)
      ⌜lr = st'.more⌝ ∗ (∃ ps', ksl ↦* ps') ∗ (∃ s, p ↦ s ∗ L.itemsAt s (itemsOf c st')) ∗
      lastKeyIs lk kvs st' }}
```
with `itemsOf c st := st.items.reverse.map fun x => (x.1, c.S.fmtRV (W64 (x.2 : Int)))`,
`decodedL dec kvs` the `(key, (obj, modRev))` of `kvs`, `ListModel.chunkL` the loop that stops at
`more` (`foldl lstep` on the chunk; equal to it on the items, `ListModel.lstep` being idempotent
past `more`), and `lastKeyIs lk kvs st'`: `lk` holds the last evaluated key (`nil` if none), which
is `st'.last` when `st'.more`. Go: `store.go:1055-1079` (`kvs[i] = nil` writes the slice: hence
`ksl ↦* ps`, owned, item 16's constraint).

### 3.5 `store.getList`, `store.listReadError`, `interpretListError`, `store.pagedChunks`

```lean
/-- **A page of a list read** at revision `R` from `start` with limit `l`, in the store `s`: the first
`l` key-values of the scope from `start` (all for `l = 0`), the count of the scope from `start`. -/
def pageKvsL (s : KVStore) (kp : GoString) (rec : Bool) (start : GoString) (l : Nat) :
    List EtcdKv × Nat :=
  let sc := s.kvs.filter fun v => kInScope kp rec v.key && !decide (go.GoStringLt v.key start)
  (if l = 0 then sc else sc.take l, sc.length)

/-- `getList`'s answer (`store.go:1081-1115`): a page of `σ`'s store at `σ.readRev rev`, the
response's revision `σ`'s (the client's `Get`'s and `List`'s header revision). -/
def listRespIs (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (σ : KVState)
    (kp : GoString) (rec : Bool) (rev lim : w64) (start : GoString) : IProp GF :=
  let pg := pageKvsL (σ.at (σ.readRev rev)) kp rec start (if rec then limN lim else 1)
  iprop(⌜resp.Revision' = W64 (σ.rev : Int) ∧ resp.Count' = W64 (pg.2 : Int)⌝ ∗
    ∃ ps, resp.Kvs' ↦* ps ∗ [∗list] q;kv ∈ ps;pg.1, txn.kvIs q kv)

abbrev store.getList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (kp : GoString) (rec : Bool)
    (lo : go_etcd_io.etcd.client.v3.kubernetes.ListOptions) (Q : w64 → KVState → IProp GF),
  kp.length ≤ opKeyMax → lo.Continue'.length ≤ opKeyMax → 0 ≤ sint.Z lo.Revision' →
  0 ≤ sint.Z lo.Limit' → (rec = false → lo.Continue' = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (∀ R, |==> □ [∧list] x ∈ c.ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) }}
    (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"getList")) (Val #(GoInterface.ok ci)))
      (Val #kp)) (Val #rec)) (Val #lo))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (err : GoInterface),
      RET (PairV #resp #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ, □ Q (W64 (σ.rev : Int)) σ ∗ ⌜σ.readRev lo.Revision' ≤ σ.rev⌝ ∗
          listRespIs resp σ kp rec lo.Revision' lo.Limit' (if lo.Continue' = [] then kp else lo.Continue')) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ readErrIs c lo.Revision' Q err)) }}
```
`readErrIs c rev Q err` (in `ListDefs`): `unkErr c err` and, by its description (7c's `errDesc`,
D29), `errDesc err = futureRevDesc → ∃ σ, □ Q (W64 σ.rev) σ ∗ ⌜σ.rev < sint.nat rev⌝`
(`rangeErrSound`'s future half; the compacted half is not needed, §2's `listErr`). Go:
`store.go:1081-1115`; recursive: `Client.List` (#16); not: `Client.Get` with `Revision` (#17),
`Count` 1 or 0, the `KV` in a fresh one-element slice; `getResourceSizeEstimator` under `RLock`
(`nil`: `isStore`'s pool invariant, #15), so `stats.Update` is not called.

```lean
/-- `listReadError`'s result (`store.go:922-934`, `errors.go:66-75`). -/
abbrev store.listReadError.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) (withRev : w64) (ck kp : GoString)
    (Q : w64 → KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ readErrIs c withRev Q err ∗
      ⌜prepareKeyM c.resourcePrefix c.resourcePrefix false ≠ none⌝ }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"listReadError")) (Val #(GoInterface.ok ci)))
      (Val #err)) (Val #withRev)) (Val #false)) (Val #ck)) (Val #kp))
  {{ (e : GoInterface), RET #e;
      (tooLargeErrIs e ∗ ∃ σ, □ Q (W64 (σ.rev : Int)) σ ∗ ⌜σ.rev < sint.nat withRev⌝) ∨ listErr c e }}
```
`errors.Is(err, ErrFutureRev)`: 7c-3's lemma (the description, `rpctypes` init's `errDesc`);
`GetCurrentResourceVersion` (existing spec) with the trivial update (`Q' := fun _ _ _ => True`,
allowed by its premise's left disjunct); `NewTooLargeResourceVersionError` (#7);
`interpretListError` with `paging = false` (`Continue = ""`): `err == ErrCompacted` (comparable:
`ErrCompacted`'s dynamic type is `rpctypes.EtcdError`, a comparable struct) gives
`NewResourceExpired(expired)` (translated, `apierrors.NewResourceExpired.spec` existing), else `err`.

```lean
abbrev interpretListError.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Obj : Type) (c : StoreCfg GF Obj) (err : GoInterface)
    (ck kp : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ unkErr c err }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.interpretListError)) (Val #err))
      (Val #false)) (Val #ck)) (Val #kp))
  {{ (e : GoInterface), RET #e; listErr c e }}
```

`store.pagedChunks` returns the iterator; its spec says what the iterator does with any `yield`
that keeps a consumer invariant (`J i` before page `i`):

```lean
/-- **The pages**: page `0` reads at `rev0` from `kp` with limit `lim0`; page `i + 1` at the
first page's revision `R`, from page `i`'s last key and `"\x00"`, with the limit doubled up to
`maxLimit` (10000), while page `i` had more (`len(kvs) < count`). -/
def pagesL (s : KVStore) (kp : GoString) (rec : Bool) (lim0 : Nat) : Nat → GoString × Nat
  | 0 => (kp, lim0)
  | i + 1 => let (st, l) := pagesL s kp rec lim0 i
             (((pageKvsL s kp rec st (if rec then l else 1)).1.getLast?.map EtcdKv.key).getD st ++ [W8 0],
              if l < 10000 then min (2 * l) 10000 else l)

/-- A chunk value (`listChunk`, `store.go:873-878`) of page `i`. -/
def chunkIs (ch : k8s_io.apiserver.pkg.storage.etcd3.listChunk) (s : KVStore) (kp : GoString)
    (rec : Bool) (lim0 : Nat) (R : w64) (i : Nat) : IProp GF :=
  let pg := pageKvsL s kp rec (pagesL s kp rec lim0 i).1 (if rec then (pagesL s kp rec lim0 i).2 else 1)
  iprop(ch.revision' ↦□ R ∗ ⌜ch.count' = W64 (pg.2 : Int) ∧ ch.hasMore' = decide (pg.1.length < pg.2)⌝ ∗
    ∃ ps, ch.kvs' ↦* ps ∗ [∗list] q;kv ∈ ps;pg.1, txn.kvIs q kv)

/-- **`f` iterates the pages** (persistent): for any `yield` and consumer invariant `J`, `f(yield)`
calls `yield(page 0, nil)` with the state `σ` `Q` fired at and `R` (`σ`'s revision, or `rev0`), then
`yield(page i+1, nil)` while `yield` returned `true` and page `i` had more; or `yield(zero, e)` once
on an error (`listReadError`'s). -/
def pagesOk (c : StoreCfg GF Obj) (f : GoFunc) (kp : GoString) (rec : Bool) (rev0 lim0 : w64)
    (Q : w64 → KVState → IProp GF) (P : KVState → IProp GF) : IProp GF :=
  iprop(□ ∀ (y : GoFunc) (J : Option (KVState × w64) → Nat → IProp GF) (Φ : val → IProp GF),
    J none 0 -∗
    (□ ∀ σ R i ch, J (if i = 0 then none else some (σ, R)) i -∗
        (if i = 0 then □ Q (W64 (σ.rev : Int)) σ ∗
            ⌜R = (if uint.Z rev0 = 0 then W64 (σ.rev : Int) else rev0) ∧ uint.nat R ≤ σ.rev⌝
         else iprop(True)) -∗
        chunkIs ch (σ.at (uint.nat R)) kp rec (limN lim0) R i -∗
        WP (App (App (Val #y) (Val #ch)) (Val #GoInterface.nil))
          {{ v, ∃ b : Bool, ⌜v = #b⌝ ∗ J (some (σ, R)) (i + 1) }}) -∗
    (□ ∀ o i e, J o i -∗
        ((tooLargeErrIs e ∗ ⌜o = none⌝ ∗ ∃ σ, □ Q (W64 (σ.rev : Int)) σ ∗ ⌜σ.rev < uint.nat rev0⌝) ∨
          listErr c e) -∗
        WP (App (App (Val #y) (Val #(zero_val k8s_io.apiserver.pkg.storage.etcd3.listChunk)))
          (Val #e)) {{ _, Φ #() }}) -∗
    (∀ o i, J o i -∗ Φ #()) -∗
    WP (App (Val #f) (Val #y)) {{ Φ }})
```
(Later pages are read with `P`'s update; `kvSameHist` turns `P`'s state's store at `R` into `σ`'s, so
`chunkIs` is stated on `σ.at R` for every page. A `yield` that returned `false` or a last page
without more ends the iteration: the last premise. The proof of `GetList` instantiates `J` with its
loop state; `ListModel` lemmas compose the pages into `kListL`.)

```lean
abbrev store.pagedChunks.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (kp : GoString) (opts : k8s_io.apiserver.pkg.storage.ListOptions)
    (rev0 lim0 : w64) (Q : w64 → KVState → IProp GF) (P : KVState → IProp GF),
  kp.length ≤ opKeyMax → 0 ≤ sint.Z rev0 → 0 ≤ sint.Z lim0 → opts.Predicate'.Continue' = [] →
  (∀ R σ, Q R σ ⊢ ⌜kvKeysShort σ⌝) →
  (∀ R σ σ', Q R σ ∗ P σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (∀ R, |==> □ [∧list] x ∈ c.ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) ∗
      □ (|==> □ [∧list] x ∈ c.ms, ⌜P = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv P) }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"pagedChunks")) (Val #(GoInterface.ok ci)))
      (Val #kp)) (Val #opts)) (Val #rev0)) (Val #lim0)) (Val #([] : GoString)))
  {{ (f : GoFunc), RET #f; pagesOk c f kp opts.Recursive' rev0 lim0 Q P ∗ threadTok }}
```
(The thread token goes back at once; the iterator re-borrows it per page. In the final text
`threadTok` is a premise of `pagesOk`'s `WP f y` instead, returned at its end: the iterator runs in
`GetList`'s goroutine.) Go: `store.go:881-920`.

### 3.6 `store.finalizeList` (`store__finalizeList.lean`)

```lean
abbrev store.finalizeList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Obj : Type) [DecidableEq Obj] (sp : Loc)
    (c : StoreCfg GF Obj) (L : ListSpec GF Obj) (lx : GoInterface) (pl : Loc)
    (pred : k8s_io.apiserver.pkg.storage.SelectionPredicate) (sel : Obj → Bool) (emp : Bool)
    (rev : w64) (cont : GoString) (rem : Loc) (remV : Option w64) (ag : GoInterface)
    (v : reflect.Value) (os : List (Obj × GoString)) (rv0 : w64) (cont0 : GoString) (rem0 : Option w64),
  lx = interface.mkOk (go.GoType.PointerType L.listTy) #pl →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      listContractOk c L ∗ selPredOk c.S pred sel emp ∗ freshAggr ag ∗
      ⌜reflElem v (go.GoType.SliceType c.S.objTy) (L.itemsRef pl)⌝ ∗
      L.listAtItems pl os rv0 cont0 rem0 ∗ remIs rem remV }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"finalizeList")) (Val #lx)) (Val #pred))
      (Val #rev)) (Val #cont)) (Val #rem)) (Val #ag)) (Val #v))
  {{ RET #GoInterface.nil; L.listAt lx os rev cont remV }}
```
`remIs rem remV`: `rem = null` for `none`, `rem ↦ n` for `some n`. `freshAggr ag`: the
aggregator the factory made, nothing appended (its `Aggregate()` is `nil`: #15). Go:
`store.go:1005-1018`; `IsNil`/`MakeSlice`/`Set` (#9; `IsNil` true only of an empty slice, so with `itemsAt_len` the items
are `[]` and stay so; revision after the attack, change 4),
`UpdateList` (#14), `SetShardInfoOnList` (translated, a no-op with a `nil` `ShardSelector`:
`selection_predicate.go:192-199`).

## 4. `storage`'s functions (translated; *proved*; `Spec/k8s_io/apiserver/pkg/storage/`)

### 4.1 `ValidateListOptions`

```lean
abbrev storage.ValidateListOptions.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (kp : GoString) (vi : GoInterfaceOk)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (n : w64),
  opts.Predicate'.Continue' = [] → S.parseRV opts.ResourceVersion' = some n →
  opts.ResourceVersionMatch' ∈ [[], go!"NotOlderThan", go!"Exact"] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ versionerOk S vi }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.ValidateListOptions)) (Val #kp))
      (Val #(GoInterface.ok vi))) (Val #opts))
  {{ RET (PairV (PairV #(listRevL opts.ResourceVersionMatch' opts.Recursive' opts.Predicate'.Limit' n)
      #([] : GoString)) #GoInterface.nil); True }}
```
Go: `interfaces.go:372-410`. (An empty resource version returns `withRev = 0` without parsing; it
parses as `0` anyway, `ObjCodec.parse_empty`, and `listRevL … 0 = 0` in every case but `Exact`,
where `n = 0`.)

### 4.2 `EncodeContinue` and `PrepareContinueToken` (final form; replaces 7e-3b's hypothesis)

```lean
abbrev storage.EncodeContinue.spec : Prop :=
  ∀ (key kp : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.EncodeContinue)) (Val #key)) (Val #kp))
      (Val #rv))
  {{ (t : GoString) (err : GoInterface), RET (PairV #t #err);
      ⌜if encOkL key kp then t = encL key kp rv ∧ err = GoInterface.nil
       else err ≠ GoInterface.nil⌝ }}

abbrev storage.PrepareContinueToken.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (kl kp : GoString) (rv cnt : w64) (more : Bool)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (sel : Obj → Bool) (emp : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗
      selPredOk S opts.Predicate' sel emp }}
    (App (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.PrepareContinueToken))
      (Val #kl)) (Val #kp)) (Val #rv)) (Val #cnt)) (Val #more)) (Val #opts))
  {{ (t : GoString) (rem : Loc) (err : GoInterface), RET (PairV (PairV #t #rem) #err);
      if more then
        (if encOkL (kl ++ [W8 0]) kp then
          ⌜err = GoInterface.nil ∧ t = encL (kl ++ [W8 0]) kp rv⌝ ∗
            (if emp then rem ↦ (cnt - opts.Predicate'.Limit') else ⌜rem = null⌝)
        else ⌜err ≠ GoInterface.nil⌝)
      else ⌜t = [] ∧ rem = null ∧ err = GoInterface.nil⌝ }}
```
Go: `continue.go:83-122`. Both specs keep `encL` opaque in what matters (#23): `EncodeContinue`'s
proof uses `strings.TrimPrefix` (Perennial, proved), `json.Marshal` and `RawURLEncoding` (#11).
The driver's `mlist` uses `PrepareContinueToken.spec` at `opts := listOptsV x`, `sel := selOkL x`,
`emp := predEmptyL x` (`predOk_driver`, §6), which gives 7e-3b's hypothesis text exactly
(`x.Limit' = (listOptsV x).Predicate'.Limit'` by `rfl`).

`encL` (`KList.lean`, #23) becomes:

```lean
/-- `storage.EncodeContinue(key, prefix, rv)`'s token: base64 (URL alphabet, no padding) of the
JSON of `{"v": "meta.k8s.io/v1", "rv": rv, "start": key without prefix}`, through the opaque
`rawUrlEnc` and `tokJson` (#11). No property of it is used (Q7e-1; no injectivity). -/
def encL (key pfx : GoString) (rv : w64) : GoString :=
  encoding.base64.rawUrlEnc (encoding.json.tokJson rv (key.drop pfx.length))
```

### 4.3 `SelectionPredicate` (translated; the general specs, and the predicate fact)

```lean
/-- **The predicate `p` selects by `sel`, and is empty iff `emp`** (persistent): `Matches` on an
object answers `sel` of its body, `Empty` answers `emp`; no sharding (a `nil` `ShardSelector`); an
empty predicate selects everything. -/
def selPredOk (S : ObjSpec GF Obj) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool) : IProp GF :=
  iprop(⌜p.ShardSelector' = GoInterface.nil ∧ (emp = true → ∀ o, sel o = true)⌝ ∗
    □ (∀ (pp : Loc) (dq : DFrac) (x : GoInterface) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
      pp ↦{dq} p -∗ S.objAt x o rv -∗
      ▷ (pp ↦{dq} p -∗ S.objAt x o rv -∗ Φ (PairV #(sel o) #GoInterface.nil)) -∗
      WP (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
        @!! go!"Matches")) (Val #x)) {{ Φ }}) ∗
    □ (∀ (pp : Loc) (dq : DFrac) (Φ : val → IProp GF),
      pp ↦{dq} p -∗ ▷ (pp ↦{dq} p -∗ Φ #emp) -∗
      WP (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
        @!! go!"Empty")) (Val #())) {{ Φ }}))
```

The general method specs it is proved from (each a spec + proof file; `Matches`,
`MatchesObjectAttributes`, `Empty`, `labelFieldEmpty`, `ShardingEnabled`, `MatchesSharding`,
`SetShardInfoOnList`), written over what the selectors and `GetAttrs` do:

```lean
/-- A label selector's `Empty`/`Matches` (`labels.Selector`, on a `labels.Set` held at a map
pointer, as a `labels.Labels`) answer `le` and `lm` of the set's contents. -/
def labelSelOk (ls : GoInterface) (le : Bool) (lm : GMap GoString GoString → Bool) : IProp GF := …
/-- The same for a field selector (`fields.Selector` on a `fields.Set`). -/
def fieldSelOk (fs : GoInterface) (fe : Bool) (fm : GMap GoString GoString → Bool) : IProp GF := …
/-- `GetAttrs` on an object answers its label and field sets (fresh maps, read-only after), no error. -/
def getAttrsOk (S : ObjSpec GF Obj) (ga : GoFunc) (lab fld : Obj → GMap GoString GoString) : IProp GF := …

abbrev storage.SelectionPredicate.Matches.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (pp : Loc) (dq : DFrac)
    (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) (le fe : Bool)
    (lm fm : GMap GoString GoString → Bool) (lab fld : Obj → GMap GoString GoString)
    (x : GoInterface) (o : Obj) (rv : GoString),
  p.ShardSelector' = GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ pp ↦{dq} p ∗
      labelSelOk p.Label' le lm ∗ fieldSelOk p.Field' fe fm ∗ getAttrsOk S p.GetAttrs' lab fld ∗
      S.objAt x o rv }}
    (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
      @!! go!"Matches")) (Val #x))
  {{ RET (PairV #((le && fe) || (lm (lab o) && fm (fld o))) #GoInterface.nil);
      pp ↦{dq} p ∗ S.objAt x o rv }}
```
(`selection_predicate.go:96-121`; `Label`/`Field` non-nil in the statement's uses, the `nil`
cases are the translated code's and need no premise; `Empty.spec` the same with
`RET #(le && fe)`, `selection_predicate.go:149-162`.) The driver's fact (proved, §6):

```lean
theorem predOk_driver (x : Input) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      selPredOk driverSpec (predV x) (selOkL x) (predEmptyL x)
```
which replaces 7e-3b's hypothesis `Spec/k8s_io/apiserver/pkg/storage/SelectionPredicate__Matches.lean`
(#22): `mlist`'s proof takes `predOk_driver` instead (its `Matches` and `Empty` conjuncts at
`objAt := (&o ↦{dq} o)`: `driverSpec`'s `objAtD` with the resource version string).

### 4.4 `fields.Set.Get`, `labels.Set.{Get,Has}` (#6)

Recommended: **translate them** (`Code/k8s_io/apimachinery/pkg/{fields,labels}.toml`: `translate =
["!*", "Set.Get"]` and `["!*", "Set.Get", "Set.Has"]`; a k8s-apiserver re-translation, like B5's
`features` constants). Their bodies are a map index and a comma-ok lookup (`labels.go:55-63`,
`fields.go:55-57`), so the specs are proved:

```lean
abbrev labels.Set.Get.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (M : GMap GoString GoString) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels ∗ m ↦${dq} M }}
    (App (Val #(methods k8s_io.apimachinery.pkg.labels.Set.ty go!"Get" #m)) (Val #k))
  {{ RET #((M.lookup k).getD []); m ↦${dq} M }}
```
(`labels.Set.Has.spec`: `RET #(decide ((M.lookup k).isSome))`; `fields.Set.Get.spec` as
`labels.Set.Get.spec`.) Fallback, if the re-translation is refused: the same three statements as
trusted axioms (faithful: they are the Go bodies).

### 4.5 ETooLarge: `NewTooLargeResourceVersionError`, `IsTooLargeResourceVersion` (#7, #20)

```lean
/-- **What an `APIStatus` check sees of an error** (`apimachinery/pkg/api/errors`): a
`*StatusError` with its status (read-only), or an error that neither is nor wraps an `APIStatus`
(a leaf whose dynamic type has no `Status()` method; `errors.As` finds none). -/
inductive ApiErrView where
  | status (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
  | plain

def apiErrAt (err : GoInterface) : ApiErrView → IProp GF
  | .status st => iprop(∃ l : Loc, ⌜err = interface.mkOk
        (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ ∗
      l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗ statusDetailsAt st)
  | .plain => iprop(⌜err ≠ GoInterface.nil ∧ ∃ t v, err = GoInterface.ok ⟨t, v⟩ ∧
      go.typeSetContains t k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false ∧
      leafErrTy t⌝)

/-- **A leaf error type** (revision after the attack, change 3): `errors.As` neither unwraps nor
asks it, i.e. its method set has none of `Unwrap() error`, `Unwrap() []error`, `As(any) bool`
(`errors/wrap.go`: `As` follows all three; the attack's `asErr`, a non-`APIStatus` leaf with an `As`
method, and `joinErr`, with `Unwrap() []error`, both make `IsTimeout` true). -/
def leafErrTy (t : go.GoType) : Prop :=
  ¬ go.hasMethod t go!"Unwrap" (go.FuncType [] [error.ty]) ∧
  ¬ go.hasMethod t go!"Unwrap" (go.FuncType [] [go.GoType.SliceType error.ty]) ∧
  ¬ go.hasMethod t go!"As" (go.FuncType [go.any] [go.bool])
-- (`go.hasMethod`'s exact Lean name and the function types' form are Perennial's; settled at Prove.)

/-- `statusDetailsAt st`: `st.Details` is `nil` or points (read-only) to details whose causes slice
holds (read-only) its causes. `causesOf st` lists them (`[]` for `nil` details). -/

/-- **The error `IsTooLargeResourceVersion` recognizes** (`errors.go:259-265`): a timeout (`Timeout`
reason) `*StatusError` whose details list the `ResourceVersionTooLarge` cause. -/
def tooLargeErrIs (err : GoInterface) : IProp GF :=
  iprop(∃ st, apiErrAt err (.status st) ∗
    ⌜st.Reason' = go!"Timeout" ∧ go!"ResourceVersionTooLarge" ∈ (causesOf st).map (·.Type')⌝)

abbrev storage.NewTooLargeResourceVersionError.spec : Prop :=   -- restated (post strengthened)
  ∀ (minRV curRV : w64) (retry : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError))
      (Val #minRV)) (Val #curRV)) (Val #retry))
  {{ (err : GoInterface), RET #err; tooLargeErrIs err }}

abbrev storage.IsTooLargeResourceVersion.spec : Prop :=
  ∀ (err : GoInterface) (w : ApiErrView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ apiErrAt err w }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion)) (Val #err))
  {{ RET #(tooLargeV w); True }}
```
`tooLargeV (.status st) := timeoutV st && causeIn st "ResourceVersionTooLarge"`, `tooLargeV .plain :=
false`, `timeoutV st := st.Reason' = "Timeout" || (st.Reason' ∉ knownReasons && st.Code' = 504)`
(`errors.go:689-698`), with `knownReasons` the 19 reasons of `errors.go:49-67`; `""`
(`StatusReasonUnknown`, commented out at `:48`) is not among them, so `Reason "" ∧ Code 504` is a
timeout (revision after the attack, change 3). Proved from #8 (`NewTooLargeResourceVersionError`: the translated body and
`NewTimeoutError`'s, which already allocates the status: the post persists the struct, its details
and the one-cause slice; `errors.go:248-257`). The old post (`∃ l, err = mkOk *StatusError l`)
follows from the new one, so the cacher's uses (KEP-6404) stay.

**`store.Get.spec` (changed through `respIs`, not its text).** `respIs`'s `.tooLarge` case
(`Store.lean:191-194`) becomes `tooLargeErrIs err ∗ ∃ o rv', c.S.objAt out o rv'`.
`store.Get.spec`'s text is unchanged; its meaning grows (the too-large error is recognizable). The
proof of `store__Get` follows from `validateMinimumResourceVersion.spec`, whose post is
restated the same way (`if uint.nat rev < uint.nat n then tooLargeErrIs err else err = nil`).
`errIs` (the driver's `Calls.lean`) gains `(tooLargeErrIs err ∗ ⌜y = tooLargeL⌝)`, and
`unkErr_errIs`/`listErr`'s users need `apiErrAt err .plain` for the client's errors: **7c-3's
`*StatusError` exclusion (T2 (c)) must state `typeSetContains t APIStatus.ty = false` and a leaf
type, not only `t ≠ *StatusError`** (the check in `IsTooLargeResourceVersion` is `errors.As` to the
interface; `errors.go:817-822`). For `InternalError` (a struct with `Error()` only) and the 410
`*StatusError` (`Reason = Expired`, `Code = 410`, `timeoutV` false) `tooLargeV` is false by the
same specs.

## 5. Trusted statements (new or restated; each through the `axiom` skill before the Freeze)

### 5.1 `apierrors.IsTimeout` (new) and `apierrors.HasStatusCause` (restated) — #8

```lean
/-- `apierrors.IsTimeout(err)` (`errors.go:689-698`, names-only): of a `*StatusError` its status's
timeout test (`reasonAndCodeForError`, `:817-822`: the `APIStatus` assertion, then `Status()`, the
struct's `ErrStatus`); of an error that is no `APIStatus` and wraps none, `false` (reason
`Unknown`, code 0). Stated as a post every view of the error answers (callers holding no view see
some bool). -/
abbrev apierrors.IsTimeout.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsTimeout)) (Val #err))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status st => timeoutV st | .plain => false⌝ }}

/-- `apierrors.HasStatusCause(err, name)` (`errors.go:92-109`), restated: of a `*StatusError`
whether its details list a cause of type `name`; of a plain error `false`. -/
abbrev apierrors.HasStatusCause.spec : Prop :=
  ∀ (err : GoInterface) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.HasStatusCause)) (Val #err)) (Val #name))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status st => decide (name ∈ (causesOf st).map (·.Type')) | .plain => false⌝ }}
```
Faithful: both read the error only through `err.(APIStatus)` / `errors.As(err, &status)` and
`Status()`, which for `*StatusError` returns `ErrStatus` (`errors.go:52-56`); for a value whose type
does not implement `APIStatus` and has no `Unwrap`/`As`, `errors.As` is false. The old
`HasStatusCause` post ("some bool", the DaemonSet's hypothesis, `etc/link-lean-first-k8sdaemon.txt`
`?`) is implied, so its callers are unchanged; it becomes an axiom here (was a named hypothesis):
**a decision, Q7e-2-3**.

### 5.2 reflect (#9) — vocabulary in `Proof/reflect/Values.lean`

New opaque: `reflSliceV (w : reflect.Value) (T : go.GoType) (s : GoSlice) : Prop` ("`w` is the
non-addressable `Value` of the slice `s : []T`", what `MakeSlice` and `Append` return).

Generic in the element type `T` (they read or write a slice header only, or a type):

```lean
abbrev reflect.Value.Kind.spec : Prop :=          -- `v.Kind()` of a slice variable's Value
  ∀ (vp : Loc) (dq : DFrac) (v : reflect.Value) (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v (go.GoType.SliceType T) p⌝ }}
    (App (Val #(methods (go.GoType.PointerType reflect.Value.ty) go!"Kind" #vp)) (Val #()))
  {{ RET #reflect.Slice; vp ↦{dq} v }}

abbrev reflect.Value.Len.spec : Prop :=           -- `Cap.spec`: `s.cap`
  ∀ (vp : Loc) (dq dq' : DFrac) (v : reflect.Value) (T : go.GoType) (p : Loc) (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗
      ⌜reflElem v (go.GoType.SliceType T) p⌝ ∗ p ↦{dq'} s }}
    (App (Val #(methods (go.GoType.PointerType reflect.Value.ty) go!"Len" #vp)) (Val #()))
  {{ RET #s.len; vp ↦{dq} v ∗ p ↦{dq'} s }}

abbrev reflect.Value.IsNil.spec : Prop :=         -- true only of an empty slice (revised, change 4)
  ∀ (vp : Loc) (dq dq' : DFrac) (v : reflect.Value) (T : go.GoType) (p : Loc) (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗
      ⌜reflElem v (go.GoType.SliceType T) p⌝ ∗ p ↦{dq'} s }}
    (App (Val #(methods (go.GoType.PointerType reflect.Value.ty) go!"IsNil" #vp)) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = true → uint.Z s.len = 0⌝ ∗ vp ↦{dq} v ∗ p ↦{dq'} s }}

abbrev reflect.Type.Elem.spec : Prop :=           -- the element type of a slice type
  ∀ (rt : reflect.Type') (T : go.GoType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜reflType rt (go.GoType.SliceType T)⌝ }}
    (App (App (Val (GoInstruction (MethodResolve reflect.Type'.ty go!"Elem"))) (Val #rt)) (Val #()))
  {{ (et : reflect.Type'), RET #et; ⌜reflType et T⌝ }}
```

Restated, generic (the existing ones plus one case each):

```lean
abbrev reflect.Value.Set.spec : Prop :=   -- old: the zero Value only; new: or a slice Value
  ∀ (vp : Loc) (dq : DFrac) (v z : reflect.Value) (T : go.GoType) (p : Loc)
    (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T] (x y : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ vp ↦{dq} v ∗ ⌜reflElem v T p⌝ ∗
      ⌜reflZero z T ∧ y = zero_val V ∨ ∃ E s, T = go.GoType.SliceType E ∧ reflSliceV z E s ∧
        HEq y s⌝ ∗ p ↦ x }}
    (App (Val #(methods (go.GoType.PointerType reflect.Value.ty) go!"Set" #vp)) (Val #z))
  {{ RET #(); vp ↦{dq} v ∗ p ↦ y }}

abbrev reflect.ValueOf.spec : Prop :=     -- old post plus `Elem` of a non-nil pointer
  ∀ (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
    (App (Val (@! reflect.ValueOf)) (Val #(interface.mkOk (go.GoType.PointerType T) #p)))
  {{ (v : val), RET v;
      □ ({{ True }} (App (App (Val (GoInstruction (MethodResolve reflect.Value.ty go!"IsNil")))
            (Val v)) (Val #())) {{ RET #(decide (p = null)); True }}) ∗
      □ ({{ ⌜p ≠ null⌝ }} (App (App (Val (GoInstruction (MethodResolve reflect.Value.ty go!"Elem")))
            (Val v)) (Val #())) {{ (e : reflect.Value), RET #e; ⌜reflElem e T p⌝ }}) }}
```
(`HEq y s` is written with `V = GoSlice` in the final text: a second triple's instance, or the
slice case as its own `Value.Set` instantiation `V := GoSlice`; Lean form to settle at Prove.)

Specialized to the driver's object (`E := examples.k8s.etcd3.Obj.ty`, elements the Lean record
`Obj`), as the scope approved:

```lean
abbrev reflect.MakeSlice.spec : Prop :=
  ∀ (rt : reflect.Type') (n m : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      ⌜reflType rt (go.GoType.SliceType Obj.ty) ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z m ∧
        sint.Z m ≤ 2 ^ 41⌝ }}
    (App (App (App (Val (@! reflect.MakeSlice)) (Val #rt)) (Val #n)) (Val #m))
  {{ (w : reflect.Value), RET #w; ∃ s, ⌜reflSliceV w Obj.ty s ∧ s.len = n ∧ s.cap = m⌝ ∗
      s ↦* List.replicate (sint.nat n) (zero_val Obj) ∗ ownSliceCap Obj s (DFrac.own 1) }}

abbrev reflect.Copy.spec : Prop :=        -- dst a MakeSlice Value, src a slice variable's Value
  ∀ (w : reflect.Value) (sd : GoSlice) (ds : List Obj) (v : reflect.Value) (p : Loc) (dq dq' : DFrac)
    (ss : GoSlice) (os : List Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      ⌜reflSliceV w Obj.ty sd ∧ reflElem v (go.GoType.SliceType Obj.ty) p⌝ ∗
      sd ↦* ds ∗ p ↦{dq} ss ∗ ss ↦*{dq'} os }}
    (App (App (Val (@! reflect.Copy)) (Val #w)) (Val #v))
  {{ RET #(W64 (min ds.length os.length : Int)); p ↦{dq} ss ∗ ss ↦*{dq'} os ∗
      sd ↦* (os.take ds.length ++ ds.drop os.length) }}

abbrev reflect.Append.spec : Prop :=      -- as Perennial's `slice.append`: consumes the old slice
  ∀ (v : reflect.Value) (p : Loc) (dq : DFrac) (s : GoSlice) (os : List Obj)
    (e : reflect.Value) (q : Loc) (dq' : DFrac) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      ⌜reflElem v (go.GoType.SliceType Obj.ty) p ∧ reflElem e Obj.ty q⌝ ∗
      p ↦{dq} s ∗ s ↦* os ∗ ownSliceCap Obj s (DFrac.own 1) ∗ q ↦{dq'} o }}
    (App (App (Val (@! reflect.Append)) (Val #v)) (Val #(sliceV [#e])))
  {{ (w : reflect.Value), RET #w; ∃ s', ⌜reflSliceV w Obj.ty s'⌝ ∗
      s' ↦* (os ++ [o]) ∗ ownSliceCap Obj s' (DFrac.own 1) ∗ p ↦{dq} s ∗ q ↦{dq'} o }}
```
(`Append` is variadic: the translation passes a one-element `[]reflect.Value`; `sliceV [#e]`
stands for that slice, read-only, in the final text.) Faithful: `reflect` implements these by the
runtime's slice operations on the typed memory (`reflect/value.go`: `Len`/`Cap` read the header,
`MakeSlice` allocates zeroed, `Copy` is `typedslicecopy` of `min(len)`, `Append` grows by `growslice`
as `append` does, `Set` stores the header, `Elem` of a pointer is the addressable pointee,
`Type.Elem` of a slice type its element type, `Kind` of a `[]T` variable `Slice`). The restriction
to `Obj` keeps each axiom to one concrete element type whose Lean representation is the
translation's (`IntoValTyped Obj Obj.ty`, generated). `MakeSlice`'s `sint.Z m ≤ 2 ^ 41` (revision after
the attack, change 1): the runtime's allocation limit, `m·sizeof(Obj) ≤ maxAlloc` = 2^48 with
`sizeof(Obj) = 112` (2^41·112 < 2^48); above it `runtime.unsafe_NewArray` panics `allocation size out
of range` (`examples/k8s7e2attack`, `TestMakeSliceHugeCapPanics`).

### 5.3 `meta.GetItemsPtr` (#10)

```lean
abbrev apimeta.GetItemsPtr.spec : Prop :=     -- the driver's list type
  ∀ (pl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗ ⌜pl ≠ null⌝ }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».GetItemsPtr))
      (Val #(interface.mkOk (go.GoType.PointerType ObjList.ty) #pl)))
  {{ RET (PairV #(interface.mkOk (go.GoType.PointerType (go.GoType.SliceType Obj.ty))
        #(structFieldRef ObjList go!"Items" pl) : GoInterface) #GoInterface.nil); True }}
```
Faithful (`help.go:80-111`): `EnforcePtr` of a `*ObjList`, `FieldByName("Items")` valid, its kind
`Slice`, `items.Addr().Interface()`: the field's address at type `*[]Obj`.

### 5.4 The continue token's encoders (#11)

```lean
/-- (`Proof/encoding/json/Token.lean`) `json.Marshal` of a continue token's struct: opaque. -/
opaque encoding.json.tokJson : w64 → GoString → GoString

abbrev encoding.json.Marshal.spec : Prop :=    -- one shape: `&continueToken{...}`, never an error
  ∀ (l : Loc) (dq : DFrac) (t : k8s_io.apiserver.pkg.storage.continueToken),
  t.APIVersion' = go!"meta.k8s.io/v1" →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ l ↦{dq} t }}
    (App (Val (@! encoding.json.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.continueToken.ty) #l)))
  {{ (sl : GoSlice), RET (PairV #sl #GoInterface.nil); l ↦{dq} t ∗
      sl ↦* (encoding.json.tokJson t.ResourceVersion' t.StartKey').toBytes }}
```
Faithful: `encoding/json` marshals a struct of two strings and an `int64` without error (invalid UTF-8
is replaced, never an error; no `MarshalJSON` methods, no cycles, no unsupported types), and
deterministically, so a function of the two varying fields.

```lean
/-- (`Proof/encoding/base64/Base.lean`, added) `RawURLEncoding.EncodeToString`: opaque. -/
opaque encoding.base64.rawUrlEnc : List w8 → GoString

-- `base64Init` restated: also `∃ e', globalAddr RawURLEncoding ↦□ e' ∗ □ ∀ sl dq d Φ, sl ↦*{dq} d -∗
--   ▷ (sl ↦*{dq} d -∗ Φ #(rawUrlEnc d)) -∗ WP (methods (*Encoding) "EncodeToString" #e') (#sl) {{ Φ }}`
-- New init axiom (gen-init.py `SPECIAL['encoding.base64']` custom `RawURLEncoding`):
axiom RawURLEncoding_init :
    {{ True }} (App (Val RawURLEncoding.init) (Val #()))
    {{ RET #(); ∃ e' : Loc, globalAddr RawURLEncoding ↦ e' ∗ (□ ∀ sl dq d Φ, …as above…) }}
```
Faithful: `RawURLEncoding = URLEncoding.WithPadding(NoPadding)` (`base64.go`) is a fixed
`*Encoding` (never written after init), and `EncodeToString` is deterministic, reads and keeps its
argument (as `StdEncoding_init`'s statement, 2026-10-26).

### 5.5 The list metrics (#12)

```lean
abbrev metrics.RecordStorageListMetrics.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (idx : GoString) (a b c' : w64),
  0 ≤ sint.Z a → 0 ≤ sint.Z b → 0 ≤ sint.Z c' →
  utf8Valid gr.Group' → utf8Valid gr.Resource' → utf8Valid idx →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }}
    (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordStorageListMetrics))
      (Val #gr)) (Val #idx)) (Val #a)) (Val #b)) (Val #c'))
  {{ RET #(); True }}
```
`RecordListLatency.spec` alike, with `utf8Valid gr.Group' → utf8Valid gr.Resource' →` (its other
label is a literal; `Observe` takes any float). Faithful (revised after the attack, change 2):
prometheus counters and histograms, no result; once registered (the apiserver registers them,
`server/routes/metrics.go:53-60`) a negative count panics (`counter cannot decrease in value`,
`storage/metrics/metrics.go:79-84`) and so does a label that is not valid UTF-8 (`WithLabelValues`);
unregistered (the driver), every call is a no-op. The store passes `""`, its `groupResource`
(`isStore`: `utf8Valid` of both fields) and counts that are slice lengths or their sums, non-negative
by `kvKeysShort`'s bound on the pages' keys.

**R1 (restated, a trust-base repair)**: the existing `metrics.RecordEtcdRequest.spec` gains
`utf8Valid verb → utf8Valid gr.Group' → utf8Valid gr.Resource' →`, and `metrics.RecordDecodeError.spec`
`utf8Valid gr.Group' → utf8Valid gr.Resource' →` (same panic, `TestMetricsRegistered`; recorded in
`nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md` and `notes/k8s-7e-2-attack.md`).
Every caller passes literal verbs and the store's `groupResource`.

### 5.6 The gate (#13)

B5's text (`/shared/tmp/sweep-repairs-1/b5-r1.md`, approved), used as is: `featureGateOk g`, its
`Enabled`/`Set` triples, `featureOff g s`, `features.EtcdRangeStream` translated. 7e-2 uses
`featureGateOk`'s `Enabled` conjunct at `s = go!"EtcdRangeStream"` (`decide`: in
`k8sQueriedFeatures`) in `shouldStream`, and its `Set` conjunct in the driver's `noStreaming`:

```lean
abbrev noStreaming.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.noStreaming)) (Val #()))
  {{ (b : Bool), RET #b; if b then rangeStreamOff else True }}
```
(`k8setcd3.go:1682`: the literal `"EtcdRangeStream=false"` equals `s ++ "=false"` at
`s = "EtcdRangeStream"`, by `decide`.) Not 7e-2's to restate; listed for the Draft's completeness.

## 6. The list contract (#14) and the driver's side (#21)

New in `Proof/k8s_io/apiserver/pkg/storage/etcd3/Contract.lean` (premises of `GetList`, not of
`New`: `contractOk` and `isStore`'s existing conjuncts are unchanged, so no existing proof moves):

```lean
/-- **The list objects**: a list type, where its items slice is, what the items hold, and the
list's metadata. -/
structure ListSpec (GF : BundledGFunctors) (Obj : Type) where
  listTy : go.GoType
  itemsRef : Loc → Loc
  /-- `itemsAt s os`: the slice `s` holds the items `os` (bodies and resource version strings),
  with its capacity -/
  itemsAt : GoSlice → List (Obj × GoString) → IProp GF
  itemsAt_nil : ⊢ itemsAt slice.nil []
  /-- the slice's length is the item count (revision after the attack, change 4) -/
  itemsAt_len : ∀ s os, itemsAt s os ⊢ ⌜uint.nat s.len = os.length⌝
  /-- the list's `ListMeta`: resource version, continue token, remaining count -/
  metaAt : Loc → w64 → GoString → Option w64 → IProp GF

def ListSpec.listAtItems (L : ListSpec GF Obj) (pl : Loc) (os : List (Obj × GoString)) (rv : w64)
    (cont : GoString) (rem : Option w64) : IProp GF :=
  iprop(⌜pl ≠ null⌝ ∗ ∃ s, L.itemsRef pl ↦ s ∗ L.itemsAt s os ∗ L.metaAt pl rv cont rem)

def ListSpec.listAt (L : ListSpec GF Obj) (lx : GoInterface) (os : List (Obj × GoString))
    (rv : w64) (cont : GoString) (rem : Option w64) : IProp GF :=
  iprop(∃ pl, ⌜lx = interface.mkOk (go.GoType.PointerType L.listTy) #pl⌝ ∗
    L.listAtItems pl os rv cont rem)

/-- The reflect calls on the items (#9 at the store's abstract element type). -/
def listContractOk' (S : ObjSpec GF Obj) (L : ListSpec GF Obj) : IProp GF :=
  iprop(
    -- `meta.GetItemsPtr(lx)`
    (□ ∀ pl Φ, ⌜pl ≠ null⌝ -∗ ▷ Φ (PairV #(interface.mkOk (go.GoType.PointerType
          (go.GoType.SliceType S.objTy)) #(L.itemsRef pl) : GoInterface) #GoInterface.nil) -∗
      WP (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».GetItemsPtr))
        (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl))) {{ Φ }}) ∗
    -- `reflect.MakeSlice(rt, n, m)`, then `reflect.Copy(extra, v)` of the items: the items in a new slice
    (□ ∀ rt (n m : w64) (v : reflect.Value) p dq s os Φ, ⌜reflType rt (go.GoType.SliceType S.objTy) ∧
        reflElem v (go.GoType.SliceType S.objTy) p ∧ sint.nat n = os.length ∧ sint.Z n ≤ sint.Z m ∧
        sint.Z m ≤ 2 ^ 41⌝ -∗
      p ↦{dq} s -∗ L.itemsAt s os -∗
      ▷ (∀ w, ∀ s', ⌜reflSliceV w S.objTy s'⌝ -∗ p ↦{dq} s -∗ L.itemsAt s' os -∗ Φ #w) -∗
      WP (let w := App (App (App (Val (@! reflect.MakeSlice)) (Val #rt)) (Val #n)) (Val #m) in
          …growSlice's two calls…) {{ Φ }}) ∗
    -- `reflect.MakeSlice(rt, 0, m)`: an empty items slice
    (□ ∀ rt (m : w64) Φ, ⌜reflType rt (go.GoType.SliceType S.objTy) ∧ 0 ≤ sint.Z m ∧ sint.Z m ≤ 2 ^ 41⌝ -∗
      ▷ (∀ w s', ⌜reflSliceV w S.objTy s'⌝ -∗ L.itemsAt s' [] -∗ Φ #w) -∗
      WP (App (App (App (Val (@! reflect.MakeSlice)) (Val #rt)) (Val #(W64 0))) (Val #m)) {{ Φ }}) ∗
    -- `reflect.Append(v, reflect.ValueOf(x).Elem())`: one item more
    (□ ∀ (v : reflect.Value) p dq s os x o rv Φ, ⌜reflElem v (go.GoType.SliceType S.objTy) p⌝ -∗
      p ↦{dq} s -∗ L.itemsAt s os -∗ S.objAt x o rv -∗
      ▷ (∀ w s', ⌜reflSliceV w S.objTy s'⌝ -∗ p ↦{dq} s -∗ L.itemsAt s' (os ++ [(o, rv)]) -∗
          S.objAt x o rv -∗ Φ #w) -∗
      WP (App (App (Val (@! reflect.Append)) (Val #v)) (Val #(sliceV [#(…ValueOf(x).Elem()…)])))
        {{ Φ }}))

/-- **The list half of the contract**: the reflect calls, the decoder's `DecodeListItem` and the
versioner's `UpdateList`. -/
def listContractOk (c : StoreCfg GF Obj) (L : ListSpec GF Obj) : IProp GF :=
  iprop(listContractOk' c.S L ∗
    □ (∀ (ctx : GoInterface) (dsl : GoSlice) (d : GoString) (rev : w64) (nf : GoFunc) (Φ : val → IProp GF),
      dsl ↦*□ d -∗ newItemOk c.S nf -∗
      ▷ (∀ (x err : GoInterface),
          (match c.S.decode d with
            | some o => ⌜err = GoInterface.nil⌝ ∗ c.S.objAt x o (c.S.fmtRV rev)
            | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err) -∗
          Φ (PairV #x #err)) -∗
      WP (App (App (App (App (Val #(methods c.di.ty go!"DecodeListItem" c.di.v)) (Val #ctx))
        (Val #dsl)) (Val #rev)) (Val #nf)) {{ Φ }}) ∗
    □ (∀ (pl : Loc) (os : List (Obj × GoString)) (rv rv' : w64) (cont cont' : GoString)
        (rem : Loc) (remV rem0 : Option w64) (Φ : val → IProp GF),
      L.listAtItems pl os rv cont rem0 -∗ remIs rem remV -∗
      ▷ (∀ err, ⌜err = GoInterface.nil⌝ ∗ L.listAtItems pl os rv' cont' remV -∗ Φ #err) -∗
      WP (App (App (App (App (Val #(methods c.vi.ty go!"UpdateList" c.vi.v))
        (Val #(interface.mkOk (go.GoType.PointerType L.listTy) #pl))) (Val #rv')) (Val #cont'))
        (Val #rem)) {{ Φ }}) ∗
    ⌜L.listTy ≠ k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.UnstructuredList.ty⌝)
```
(The `…` places are the translated expressions of `growSlice` and `processListItem`, copied at Prove;
the alternative is one premise per reflect call with an abstract `itemsAt`-preserving `Copy`, which
the review may prefer.)

**The driver's instance** (`Proof/.../examples/k8s/etcd3/Contract.lean`, proved):

```lean
def driverListSpec : ListSpec GF Obj :=
  { listTy := ObjList.ty, itemsRef := fun pl => structFieldRef ObjList go!"Items" pl,
    itemsAt := fun s os => iprop(∃ vs : List Obj, s ↦* vs ∗ ownSliceCap Obj s (DFrac.own 1) ∗
      ⌜os = vs.map fun o => (objBody o, rvString o.ResourceVersion')⌝),
    itemsAt_nil := …, itemsAt_len := …,
    metaAt := fun pl rv cont rem => iprop(structFieldRef ObjList go!"ResourceVersion" pl ↦ rv ∗
      structFieldRef ObjList go!"Continue" pl ↦ cont ∗ ∃ r, structFieldRef ObjList go!"RemainingItemCount" pl ↦ r ∗
      remIs r rem) }

theorem driver_listContractOk : isPkgInit … ⊢ listContractOk driverCfg driverListSpec
```
from #9 and #10 (the axioms at `Obj`), and the driver's proved `decoder.DecodeListItem`
(`k8setcd3.go:382-396`: `newItemFunc()`, the `*Obj` assertion, `decodeObj`, the revision set) and
`versioner.UpdateList` (`k8setcd3.go:331-340`):

```lean
abbrev decoder.DecodeListItem.spec : Prop :=
  ∀ (ctx : GoInterface) (dsl : GoSlice) (d : GoString) (rev : w64) (nf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      dsl ↦*□ d ∗ newItemOk driverSpec nf }}
    (App (App (App (App (Val #(methods decoder.ty go!"DecodeListItem" #(decoder.mk))) (Val #ctx))
      (Val #dsl)) (Val #rev)) (Val #nf))
  {{ (x err : GoInterface), RET (PairV #x #err);
      match decodeObjL d with
      | some o => ⌜err = GoInterface.nil⌝ ∗ objAtD x o (rvString rev)
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err }}

abbrev versioner.UpdateList.spec : Prop :=
  ∀ (pl : Loc) (os : List (Obj × GoString)) (rv rv' : w64) (cont cont' : GoString) (rem : Loc)
    (remV rem0 : Option w64),
  {{ isPkgInit … ∗ driverListSpec.listAtItems pl os rv cont rem0 ∗ remIs rem remV }}
    (App (App (App (App (Val #(methods versioner.ty go!"UpdateList" #(versioner.mk)))
      (Val #(interface.mkOk (go.GoType.PointerType ObjList.ty) #pl))) (Val #rv')) (Val #cont'))
      (Val #rem))
  {{ RET #GoInterface.nil; driverListSpec.listAtItems pl os rv' cont' remV }}
```
and the selector functions (`k8setcd3.go:651-711`, proved over #6): `fieldSel.Matches` on a
`fields.Set` (as `fields.Fields`) answers `fieldSelOk s` of the map; `labelSel.Matches` answers
`labelSelOk s`; `getAttrs(&o)` returns fresh maps `objLabels o`/`{name, namespace, node}`, read-only
after (persisted); `objLabels o` is `{"app" ↦ o.App}` if `o.App ≠ ""`, else empty. Together:
`predOk_driver` (§4.3). `listOut(l)` (`k8setcd3.go:1580-1588`) answers `listOutL`'s list fields from
`driverListSpec.listAt`.

## 7. The client specs as consumed (#16, #17) — hypotheses

**`kubernetes.Client.List.spec` (7e-1)**, the form 7e-2 needs (Q7e (a) of 7c's Scope):

```lean
abbrev Client.List.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ms : List (client.SrvAt GF)) (V : client.WEnv GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (prefix : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.ListOptions) (Q : w64 → KVState → IProp GF),
  prefix.length ≤ opKeyMax → opts.Continue'.length ≤ opKeyMax →
  0 ≤ sint.Z opts.Revision' → 0 ≤ sint.Z opts.Limit' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R, |==> □ [∧list] x ∈ ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"List"))
      (Val #(GoInterface.ok ci))) (Val #prefix)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) σ ∗
        ⌜σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev⌝ ∗
        listRespIs resp σ prefix true opts.Revision' opts.Limit'
          (if opts.Continue' = [] then prefix else opts.Continue')) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err ∗ rangeErrSound opts.Revision' Q err) }}
```
Requirements on 7e-1 found here: **(a)** the `Kvs` slice is owned (`↦*`, not `↦*□`): `appendChunk`
writes `kvs[i] = nil` (`store.go:1074`); **(b)** `Count` is the scope from the range start
(`client.go:60-65`, `nonissues/` as 7c's Scope found); **(c)** the error's future-revision soundness
at the call's revision, and its leaf, non-`APIStatus` type (§4.5); **(d)** (revision after the attack)
`uint.nat resp.Kvs'.len ≤ 2 ^ 41`, for `growSlice`'s `MakeSlice`.

**`kubernetes.Client.Get.spec` at a revision (7c-3)**, as 7c's Scope states it (no
`opts.Revision' = 0` premise; the answer `findKey key (σ.at (σ.readRev opts.Revision')).kvs`; the
error's `rangeErrSound`). `getList`'s non-recursive branch calls it with `Q' := fun R _ => Q R`.

## 8. The model relation (#24), stated for 7e-3c

The store's post feeds the driver's `mlistL` through 7e-3c's `refine_list`:

```lean
theorem refine_list (x : Input) (h : HSt) (σ : KVState) (γ…) (hrel : KRelH c h σ)
    (hk : prepareKeyM go!"/objs" x.ListKey' x.Recursive' = some k) (hn : parseRVD x.MinRV' = some n) :
    let R := listRevL (matchOptL x) x.Recursive' x.Limit' n
    let s := if uint.Z R = 0 then σ.store else σ.at (uint.nat R)
    let a := kListL driverSpec.dec (selOkL x) (limN x.Limit') (go!"/registry" ++ k) x.Recursive' s
    (if uint.Z R = 0 ∨ uint.nat R ≤ σ.rev then
      listOutDriver x (if uint.Z R = 0 then W64 (σ.rev : Int) else R) a = mlistL x h
     else tooLargeL = mlistL x h)
```
where `KRelH c h σ` is 7e-4's relation (`h.st = absK … σ`, `h.hist[r-1] = absK … (σ.at r)` for
`1 ≤ r ≤ σ.rev`, and `(histAtL h.hist r).rv = r`: the model's past store carries its revision, which
`listOutL`'s `st.rv` reads), and `listOutDriver` the driver's `listOut` of `listIs` (items encoded,
token, remaining count). Pure; proved in 7e-3c. `pastReadL x n = decide (uint.Z (listRevL …) ≠ 0)`
is the lemma linking the two notions of a past read (both from `interfaces.go:385-405`).

## 9. Closed theorems and interface files

- **Closed theorems re-proved** (text unchanged; programs and meanings change): `k8s_etcd3_safe`,
  `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe` (7e-4). 7e-2 itself closes none: its results
  are linked (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Link.lean` gains `store.wp_GetList` and the
  callees; `etc/link-lean-first-*.txt` lists the new specs).
- **Statements changed** by 7e-2: `respIs` (`.tooLarge`), `validateMinimumResourceVersion.spec`'s post,
  `NewTooLargeResourceVersionError.spec`'s post, `HasStatusCause.spec` (restated), `reflect.Value.Set.spec`,
  `reflect.ValueOf.spec`, `base64Init`, `encL` (definition), `isStore` (definition, #15). Users
  (`etc/importers.py --uses`, run 2026-11-08): `respIs`: 13 modules (the store's `Create`, `Get`,
  `updateOnce`, `deleteOnce`, `conditionalDelete`, `GuaranteedUpdate`, `Steps`, the driver's `Calls`);
  only `Get`'s proof and `Calls` reach the `.tooLarge` case. `ValueOf`: `txn.isNil` (ignores the new
  conjunct). `Value.Set`: `runtime.SetZeroValue`'s proof. `NewTooLargeResourceVersionError`: the
  etcd3 and cacher `Link.lean`s (weaker use, implied). `HasStatusCause`: the DaemonSet's
  `createPods` (weaker use, implied).
- **`isStore` (#15)** gains `structFieldRef store "listErrAggrFactory" sp ↦□ f` with `aggrFactoryOk
  f` (`defaultListErrorAggregatorFactory` or `corruptObjErrAggregatorFactory`'s closure, as
  `New` picks by `Enabled(AllowUnsafeMalformedObjectDeletion)`, `store.go:201-204`: each makes an
  aggregator whose `Aggregate()` is `nil` before any `Append`), and `collectorMux`'s reader pool with
  the invariant `resourceSizeEstimator ↦ null` (nothing in the verified programs calls
  `EnableResourceSizeEstimation`, `store.go:677`). `New.spec`'s text is unchanged; its proof builds
  them (`init_RWMutex_threadPool`).
- **Interface files**: none (`etc/api/` lists raft, backend, bbolt, etcdstart; the store, client/v3,
  reflect, apimachinery are unlisted). 7e-2 touches nothing `etcdstart` exports. Regenerated at the
  Freeze to confirm.
- **Trust base**: `etc/tcb-baseline.txt` and `etc/tcb-collections/{k8s,k8setcd3}.txt` gain the §5
  axioms (13 new, 3 restated), B5's as B5 lands them.

## 10. Questions for etcd-grove-81 (recommendations)

- **Q7e-2-1. Generic store, list contract.** `GetList.spec` stays generic in the object type (D30b)
  and takes the list half as a premise (`listContractOk`), with the reflect axioms specialized to
  the driver's `Obj` (as approved) and discharged by the driver. Alternative: state the
  element-touching reflect axioms generic in `(T, V)` with `IntoValTyped V T` (as the existing
  `Value.Set` is) and drop `listContractOk'`. *Recommended: the contract* (one element type per
  axiom, as the scope chose).
- **Q7e-2-2. `Q` and `P`.** The first page fires `Q` (prophesied), later pages `P`, with the
  premise that their states share a history. *Recommended: yes*; producer 7e-4 (`readQ` + `γ.r`).
  The alternative (one `Q` at every page) makes the driver's commit fire several times.
- **Q7e-2-3. `HasStatusCause` and `IsTimeout` become axioms** (the former a named hypothesis
  today). *Recommended: yes*, in the post-wand shape that keeps the DaemonSet's use.
- **Q7e-2-4. Translate `fields.Set.Get`, `labels.Set.{Get,Has}`** (a k8s-apiserver
  re-translation) instead of three axioms. *Recommended: translate.*
- **Q7e-2-5. `threadTok` in `GetList.spec`** and a reader pool in `isStore` for
  `collectorMux.RLock` (bounds plan). *Recommended: yes*; the token comes from lintest's
  `applySpec`.
- **Q7e-2-6. 410 as a failed read**, not proved unreachable (`listErr`): no no-compaction fact is
  needed in 7e-2. *Recommended: yes* (the model accepts any `EOther` read).
- **For 7c-3 and 7e-1** (to pass on): the client's errors must be `apiErrAt err .plain` (a leaf
  type outside `APIStatus`'s type set, `leafErrTy`); `Client.List`'s `Kvs` owned and at most 2^41 long
  (revision after the attack).
