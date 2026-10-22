# Plan: the Kubernetes etcd3 storage backend (`k8s.io/apiserver/pkg/storage/etcd3`)

Status: started (2026-10-22, branch `k8s-etcd3`: `lean` with `k8s-etcd3-goose` merged). Decisions:
D30 in `notes/decisions.md` (D30a-k; D30h-j proposed). The translation survey is branch
`k8s-etcd3-goose` (`notes/k8s-etcd3-goose.md`): the store translates and builds with the pinned
translator except six functions left names-only; its gaps G1-G3 are under "What blocks where", and
the Perennial changes they call for in `notes/perennial-changes.md`. Done so far (`notes/STATUS.md`
has the details): phase 1's contract, phase 2's model, phase 3's client (`Get`, `OptimisticPut`,
`OptimisticDelete`; one `sorry`, `kvIs_ne_null`: request 3 below), and phase 4's `store.Get` and
`store.Create`, linked.

Next steps: phase 4's `Delete` and `GuaranteedUpdate`, then `Get`'s minimum resource version.
Merging `k8s-etcd3` into `lean` waits on an OK from the etcd client proof's owner (the survey
changes the etcd project's configuration: it translates `client/v3/kubernetes` and owns only
`k8s_io/utils/third_party`).

## Goal

Rule out, by proof, the class of bugs Kubernetes' storage correctness test finds in the etcd3
store (`test/integration/apiserver/storage/`, `TestCorrectness`; its README lists the bugs). The
store's own: #43152, #48394, #54780, #77619, #94002; shared with the watch cache: #35415, #89828
(deleted object), #113380, #135452, #138724, #142591. The watcher (`watcher.go`) and the watch
cache (`cacher`) come later.

Two results:

1. **Generic method specs.** A logically atomic triple for each `storage.Interface` method of
   `*store` (`Create`, `Delete`, `GuaranteedUpdate`, `Get`, `GetList`, `Stats`,
   `GetCurrentResourceVersion`, ...), stated with a Lean copy of `correctness.Model`
   (`staging/src/k8s.io/apiserver/pkg/storage/testing/correctness/model.go`), for **any** codec,
   versioner and transformer meeting a contract (a premise, not an axiom).
2. **A closed driver theorem** (`k8setcd3_porcupine_safe`, as `kv_porcupine_safe`): a Go program
   in `examples/` runs `TestCorrectness`'s traffic and checks against the store over in-process
   etcd members, with a simple concrete codec, and never panics. Its trusted spec is then the
   Kubernetes maintainers' `Model` and porcupine (verified here), not our Lean spec.

## How the store works (what the spec is about)

- An object (`runtime.Object`; in the test `*api.Pod`) lives at one etcd key
  (`/registry/pods/<ns>/<name>`); the value is the object's encoding (`runtime.Codec`) passed
  through a transformer (`value.Transformer`, encryption at rest; identity in the test).
- The resource version is not stored: `PrepareObjectForStorage` clears it before encoding, and
  every read sets it to the etcd `ModRevision` (`decoder.Decode` -> `versioner.UpdateObject`).
  Preconditions and optimistic updates are `ModRevision` compares in etcd transactions
  (`client/v3/kubernetes`: `OptimisticPut`, `OptimisticDelete`).
- `GuaranteedUpdate` and `Delete` may start from a caller's possibly stale
  `cachedExistingObject`, check preconditions, run `tryUpdate`/`validateDeletion`, refresh on an
  error (`refreshOnError`), re-read on a no-op from a non-current state, and retry on a
  `ModRevision` mismatch. `Model.update` ignores the cached object: the spec says the outcome is
  the Model's at one linearization point whatever the suggestion was, exactly the class of
  #35415, #43152, #48394, #54780, #77619, #82303, #89828, #113380, #138724.

## The codec contract (and why the driver's codec is non-canonical; D30g)

The specs quantify over a codec, versioner and transformer with a contract. It must be weak
enough to hold of the real ones:

- decoding fails or gives some object; decoding what the store encoded gives that object back
  (up to the resource version, which `UpdateObject` sets);
- **encoding is not canonical**: stored bytes `b` may differ from `encode(decode(b))`, and the
  transformer may report a stored value `stale`. #48394 (`GuaranteedUpdate` skipping the write
  when the stored data is not canonical) lives exactly there, and `GuaranteedUpdate`'s no-op
  check compares bytes (`bytes.Equal(data, origState.data)`).

**`correctness.Model` is wrong on that path (2026-10-22, D30g).** On a no-op update of
non-canonical or stale data the store rewrites the object at a new resource version, as its
own unit test requires, while the Model skips the write and rejects the response
(`issues/k8s-correctness-model-noop-rewrite.md`, reproduced). Decided (D30g):
- The Lean model's items carry a bit `canon` (the stored value is the codec's current encoding
  and not stale), and `update` writes unless the object is unchanged and `canon` holds. This is
  the store's rule, and the generic specs are stated with it. On states whose items are all
  canonical it is `correctness.Model`.
- **The driver's codec stays non-canonical** (D30b), for example a decoder that accepts several
  encodings of one object (a field order, optional padding or a version tag). The driver seeds
  some keys in a non-canonical encoding before the traffic starts, as an older API server or a
  different serializer would have left them, and its transformer sometimes reports `stale` (a
  function of the stored value). It checks against a **fixed `correctness.Model`**: a patched
  copy of the package in `examples/k8setcd3/`, whose items carry their stored form, so that
  `update` compares as the store does. That copy is trusted until upstream fixes the Model. The
  contract's proof for the driver's codec is a real proof (no axiom).

## The driver and failed writes

`correctness.Model.Step` panics on any write error, and a faithful client spec lets any RPC
fail. First version: **a failed write stops the run without checking.** Each client stops at
its first failed write and sets a flag; after all clients finish, `Main` returns without
running porcupine if the flag is set. Failed reads are dropped from the history (a read has no
effect, so dropping it keeps a linearizable history linearizable).

Not "check the history up to the failure": a write that errored may still have taken effect,
and a concurrent read may have seen it, so the checker could reject a correct store and the
theorem would be false.

What this costs: the driver theorem says nothing about runs with a failed write (bugs in
recovery after one); the method specs still cover them (a failed write fired at most once).
The driver's Go test should show that runs reach the check in practice.

Upgrade, later: linkvtxn's model already checks over configurations with pending failed writes
(`examples/linkvtxn/linkvtxn.go`, "The model", `TxnModel.lean`'s `mStep`): a failed write may
take effect at any later time or never. Wrapping `correctness.Model` the same way needs a
write's effect to be a function of its input; the test's `randomUpdate` fixes its random choices
when the update function is made, so it is.

## Phases

0. **Setup.** The translation survey (branch `k8s-etcd3-goose`): Goose configuration, the gaps
   and their workarounds. Pin `k8s.io/apiserver` (the mirror at kubernetes master `d9cafe4`) with
   etcd replaced by this repo's fork pin. Fixed configuration for the proofs and the driver:
   `EtcdRangeStream` off (lists use paginated `Range`s, not `GetStream`), no compactor
   (`CompactionInterval` 0, and `ListFromCacheSnapshot` off: either starts a compactor
   goroutine in `NewCompactor`, the second its watch loop, which reaches G1's
   `fromWatchResponse`), `ttl = 0` (no leases), `AllowUnsafeMalformedObjectDeletion` off.
1. **Object boundary.** The contract above for `runtime.Codec`, `storage.Versioner` and
   `value.Transformer`; the store's `reflect`/`conversion.EnforcePtr` uses (from the survey:
   trusted models or Perennial support). The store invariant: every value under the prefix
   decodes (written by a store with this codec, or seeded by the driver).
2. **Pure Lean model.** `correctness.Model`'s create, delete, update, get and list over items,
   resource version and compaction revision; an abstraction from etcd's `KVState` (the etcd
   specs' state) under the prefix; lemmas that each transaction the store sends moves the
   abstraction as the Model's operation. No new ghost state: the store's specs take atomic
   updates over the etcd specs' `etcdKV` through the abstraction.
3. **`client/v3/kubernetes`.** Specs of `Get`, `List`, `Count`, `OptimisticPut` and
   `OptimisticDelete`, proved from `kv.Get`/`kv.Txn`'s (a new package of the etcd project; tell
   the client proof's owner).
4. **Unary methods.** Helpers (`prepareKey`, `getStateFromObject`, `stateFromEtcdResponse`,
   `updateState`, `refreshOnError`, `txnError`, `validateMinimumResourceVersion`), then `Get`,
   `Create`, `Delete` (`conditionalDelete`, `deleteOnce`; preconditions and `validateDeletion`
   as callback specs), `GuaranteedUpdate` (`updateOnce`; `tryUpdate` with a repeatable spec: it
   may run on stale states, only the run at the linearization point counts). An RPC error needs
   only "some error, the write fired at most once": no dependence on error identity.
5. **`GetList`.** `pagedChunks` (an `iter.Seq2`), continue tokens, predicate filtering, limits,
   the resource-version modes (#94002). Needs error identity: `ErrFutureRev` ->
   `TooLargeResourceVersion`, `ErrCompacted` -> 410.
6. **Driver.** `examples/k8setcd3`: in-process etcd members (as linkv3p), the etcd3 store with
   the driver's codec, `RunUnaryTraffic`-style traffic (reused from the test, `math/rand` choices
   nondeterministic), porcupine with `correctness.Model`, `Replay.Validate`; failed writes as
   above. Then faults: partitions and client cuts from linkv3p's schedule.

## What blocks where

**Error identity (`Range`'s errors).** Only the list and watch paths branch on which etcd error
came back: `store.listReadError` (`store.go:923`, `errors.Is(err, ErrFutureRev)` ->
`TooLargeResourceVersion`), `interpretListError` (`errors.go:66`, `err == ErrCompacted` -> 410,
by interface equality, so the client must return rpctypes' own value) and `interpretWatchError`
(the watcher). `Get`, `Create`, `Delete`, `GuaranteedUpdate`, `Stats` and
`GetCurrentResourceVersion` return etcd's errors unchanged, and `Get`'s
`TooLargeResourceVersion` comes from a local comparison (`validateMinimumResourceVersion`).
So phases 1-4 never wait on it; phase 5 does, in two strengths:
- *soundness* (`ErrFutureRev` returned only when the revision is above the current one,
  `ErrCompacted` only when below the compaction revision): without it a valid list may come back
  `TooLargeResourceVersion` or 410, which the Model rejects. Needed by the driver once its
  traffic has lists (25% of `TestCorrectness`'s).
- *completeness* (such a revision gives that error): needed only for the generic spec to say a
  future-revision list returns `TooLargeResourceVersion` (and a compacted one 410); the driver
  can treat any other error as a failed read.

A driver without list traffic (phase 6 first, then lists) does not need it at all.

**Translation (the survey).**
- G2, range over a function: `store.GetList` loops over an `iter.Seq2` (`store.go:825`) on
  every path, the ordinary `pagedChunks` included. Goose does not translate it, so phase 5 is
  blocked on it before error identity: Goose support (the general fix, a Perennial change), a
  Goose fork of k8s.io/apiserver rewriting the loop (as the etcd fork), or a trusted model.
- G1, field selection through a type alias (`clientv3.Event = mvccpb.Event`): blocks
  `parseEvent` and the compactor's watch loop, so the watcher, not phases 1-6 (with the compactor
  configured off, phase 0); a one-line Goose fix (`types.Unalias` in `getStructInfo`), tried on a
  scratch translator; needed before the watcher.
- G3, a type of a package the file does not import: worked around in configuration, except
  `storage.InvalidError.Error` (names-only), which nothing on the store's paths calls
  (`ParseResourceVersion` builds an `InvalidError` for a malformed resource version, but only
  its type is used); not blocking.
- `reflect` is on every unary path (`conversion.EnforcePtr`, `reflect.New(v.Type())` in `Delete`,
  `GuaranteedUpdate`; `MakeSlice`/`Append` in lists) and Perennial's `reflect` has no specs:
  phase 1 needs them, either as an independent Perennial change or as local trust-boundary specs.
- No specs yet for `strconv`'s parse/format functions, `encoding/json`, `encoding/base64` and
  `path` (continue tokens, `prepareKey`), or for the names-only apimachinery functions the unary
  path calls (`meta.Accessor`, `runtime.Encode`, the error constructors; klog, metrics, tracing
  and feature gates as no-ops).

## From the etcd client proof (coordinate with its owner)

1. `Range`'s error side: `ErrFutureRev` exactly when the revision is above the current one,
   `ErrCompacted` exactly when below the compaction revision (the compaction revision in the
   model), as rpctypes' own error values (`interpretListError` compares with `==`). Needed by
   phase 5, and by the driver once it lists: soundness first ("What blocks where").
2. `Txn`/`DeleteRange` errors: what the caller learns about whether its update fired (at most
   once already holds: `kvOpAu1`). Needed by phase 4's error cases.
3. (2026-10-22) `txn.kvIs l v` (a response's key-value, `server/v3/etcdserver/txn/Requests.lean`)
   should carry `⌜l ≠ null⌝`. The store branches on `getResp.KV == nil`, so
   `kubernetes.Client.Get`'s spec needs a found key's pointer non-nil. Its one `sorry` is
   exactly that. The fix: `txn.kvAt_persist'` takes it from the struct's typed points-to
   (`typedPointsto_not_null`), and the dozen destructuring sites gain a pattern.
4. For the watcher, later: `prevKV` (the watch contract fixes it false), compaction cancels,
   watches under any prefix (the contract's `V.pfx` is fixed).

## Open

- How `reflect` is specified (Perennial change or local specs); how G2 is resolved.
- Whether `correctness.Model` translates (it uses `reflect.DeepEqual` on objects); if not, the
  driver needs a translatable copy of its checks, which then becomes trusted.
- Which in-process etcd setup the driver starts from (linkv3p's three members, or one member
  first).
