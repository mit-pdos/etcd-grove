# Watches across a compaction (2026-11-01)

etcd's watchable store (`server/storage/mvcc`) sends a watcher whose next revision was compacted
one response with `CompactRevision` set and drops it (`watcherGroup.chooseAll`); the server forwards
it canceled, the client's watch channel delivers it as an error (`ErrCompacted`) and closes. M2 had
excluded watchers on a compacting store (a "no compactor" fact in the watch-create token, the
user's F1). The user lifted F1, kept the client's `watcher.Watch.spec` (a compaction response is
`watchStateRespOk`'s error arm), and asked for the specs below it. Plan:
`notes/watch-compaction-plan.md`.

## The first version (candidate 1), in short

- `RespM` gains `compactRev`; `respIs`/`respOk` read it.
- The create token loses `noCompactor`; the lock body's "no watcher, or frozen" goes.
- `rangeEvents` takes a share of the compaction revision's authority `crevUB γ.idx q c` with
  `c ≤ minRev`, in place of `crevFrozen` ("compaction keeps every revision at or above `c`").
- `chooseAll`/`choose` drop "every member at or above `compactRev`", add `0 ≤ compactRev`, and send
  the compaction response "as `watcher.send` does for a response without events".
- v3rpc's `mvccResp` is canceled exactly when it carries a compaction; the client's member facts
  lose `noCompactor`.

## Review round 1 (spec-reviewer), and what it changed

- **`rangeEvents` was false at `minRev = c`**: compaction keeps, of each key, its latest change at
  or below `c`, so when revision `c` changes one key twice the earlier change is deleted, and a watch
  from `c` misses it (reproduced; `issues/etcd-compaction-delete-then-put.md`, a second symptom).
  The candidate's appeal to `NoDelPutAt` was stale: that premise had been dropped in M2.
- **`0 ≤ compactRev` was unsatisfiable** by the one caller on a never-compacted store (`-1`).
- **No channel invariant admitted the compaction response**: `respCov` demanded a coverage and a
  notified-log revision that a response with `Revision = 0` cannot have. → a compaction arm.
- **`choose`'s copy branch leaves the compacted members in the source group**: a Go bug
  (`issues/etcd-watch-compacted-resent.md`): the post says so, and the state model admits a
  compacted watcher still unsynced, resent the response.
- The client's proof of `run` uses `canceled = false` of forwarded responses: listed for W3.

## The user's first decision, and why it was reversed (round 2)

Candidate 2 put "revision `c` changes each key at most once" on the compaction's producer,
`store.Compact`; the user chose it over a weaker watch guarantee and a premise on the watch path.
Round 2 showed the premise unprovable by its supplier: through gRPC at the fork pin a revision can
put a key and then delete it (`checkIntervals`' sibling bug, now with this consequence reproduced),
and the server cannot know at compaction time what earlier writes did. A fact about the history is
the writers' (or whoever already reasons about them), not the compaction request's.

The candidate offered next, "reuse the client's `srvNoDupKeys`, which every watch client already
carries", was wrong: it was an unused definition. The user chose, with the corrected cost: **the
create token carries, gated by the mode, "no revision of the logs a watch reads writes a key
twice"**; the non-compacting examples are untouched, and the compacting example proves it from its
puts-only workload.

## Round 3, and the approved spec (candidate 4)

Round 3 found an import cycle (`txn.NoDupKeysPerRev` cannot be named in mvcc: an mvcc predicate and
a bridge law), and that the gate is better stated over `mvcc.evLog` (the client's watch vocabulary,
same strength). The approved statements:

```lean
-- mvcc, `Compact.lean` (pure)
def oneChangePerKeyAt (log : Log) (c : Int) : Prop :=
  ∀ cs, 0 ≤ c → log[c.toNat]? = some cs → (cs.map Change.key).Nodup
def oneChangePerKey (log : Log) : Prop := ∀ c : Int, oneChangePerKeyAt log c

-- mvcc, the create token and the lock body
def noDupKeys (γ : StoreNames) : IProp GF :=
  iprop(□ ∀ log : Log, evLog γ log ={⊤}=∗ ⌜oneChangePerKey log⌝)
  T := iprop(watchTok γ ∗ (⌜γ.st.cm = true⌝ → noDupKeys γ.st))
def wsWatchNoDup (γ : WsNames) (σ : WsState) : IProp GF :=
  iprop(⌜σ.M = ∅⌝ ∨ (⌜γ.st.cm = true⌝ → noDupKeys γ.st))

-- mvcc, `rangeEvents`: `crevFrozen γ` replaced by
      mvcc.crevUB γ.idx qc c ∗ …
      ⌜… ∧ -1 ≤ c ∧ c ≤ sint.Z minRev ∧ (c = -1 ∨ oneChangePerKeyAt log c)⌝
  -- the share given back in the post

-- mvcc, the response
structure RespM where … compactRev : w64 := W64 0
-- respIs: v.CompactRevision' = r.compactRev
-- respOk: … ∧ (r.compactRev ≠ W64 0 → r.evs = [] ∧ r.id = rr.id ∧ r.id ≠ W64 (-1) ∧ r.rev = W64 0)
def respCov (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (x : RespM) : IProp GF :=
  iprop(respCompl γc x ∗
    (if x.compactRev ≠ W64 0 then iprop(⌜x.cov = [] ∧ x.regs = [] ∧ x.evs = []⌝)
     else iprop((□ ∀ w' : Loc, ⌜w' ∈ x.cov⌝ -∗ covFact γ γc pre w' x.rev) ∗
       ⌜x.evs = [] → x.w ∈ x.cov⌝ ∗ respRev γ pre x)))

-- v3rpc
def mvccResp (r : mvcc.RespM) (h : HdrM) : WatchRespM :=
  { hdr := h, watchId := r.id, created := false, canceled := decide (r.compactRev ≠ W64 0),
    compactRev := r.compactRev, cancelReason := [], fragment := false, evs := r.evs,
    src := some r }

-- client
def watchMemberFacts (V : WEnv GF) : IProp GF :=
  iprop(mvcc.watchTokPool V.R.γ ∗ srvLogsSmall V.R ∗ ⌜V.R.γ.st = V.R.E.γ⌝ ∗ watchLaws V ∗
    srvKVFacts V ∗ (⌜V.R.γ.st.cm = true⌝ → mvcc.noDupKeys V.R.γ.st))
```

`chooseAll`/`choose` (internal, `syncWatchers` their only caller) take `0 ≤ st.minRev` and, for
each member below `compactRev`, a `cmpSendPre` (the channel's access, liveness and the range's
`id ≠ -1`); they return the compacted set `Cm` with `cmpSendPost`, and `choose`'s copy branch keeps
`Cm` in the source group. `watcher.Watch.spec`, `store.Compact.spec`, `syncWatchers.spec` and every
exported result: unchanged. Margins (docstrings): the gate covers every revision where only
compaction revisions matter, and keys on the mode, not on the store being frozen.

## What it teaches

- A premise on an operation must be provable by that operation's callers from what they hold: a
  property of the whole earlier history (every write so far) is not the compaction's premise but
  the writers', or that of whoever already reasons about them (here the watch client's workload).
  (`PRINCIPLES.md`, "A workload premise about a resource's later operations goes on the resource's
  only producer", sharpened.)
- Before offering "reuse X, clients already carry it", check that X has a consumer.
- Run the reviewer again after each repair: rounds 2 and 3 each found a hard-rule break that the
  previous repair introduced or exposed.
