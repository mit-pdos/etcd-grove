# Plan: Kubernetes' etcd compactor (`k8s.io/apiserver/pkg/storage/etcd3/compact.go`)

Status: approved 2026-11-04 with the recommendations (Q1 (a) then (c), Q2 (i), Q3 in rounds). K1
done (2026-11-04): the compactor's slot `v3compactor.bootCfg`, admitting compaction with the
compactor off (`notes/decisions.md`, "The compactor's slot"). Its client-only case allows any `cret`
and is covered by `bootCfg_off`, not the `cret = 0` and `bootCfg_clientOnly` K1 below first said.
K2's Draft 2 approved with U1-U4 (2026-11-04), its specs written
(`Spec/k8s_io/apiserver/pkg/storage/etcd3/`, `CompactorDefs.lean`; `notes/decisions.md`,
"Kubernetes' compactor: the specs"), and U2's `strconv` specs. U1 done (2026-11-04: `txn.Commit.spec`'s `txnRevLb`). G1 done on a Perennial branch,
waiting for the user's push (`notes/perennial-changes.md`). K3 done (2026-11-04, below). K4 done (below). Next: K5. It follows the phases of
`notes/spec-first-plan.md`: scope, a spec skeleton, testing the specs against Go, freeze, proofs.
Its server step follows the slot convention there, "The slot convention" (the user's advice,
2026-11-04).

## What the compactor is

Kubernetes, not etcd, compacts a Kubernetes cluster's etcd: kube-apiserver runs with etcd's
auto-compactor off and starts its own (`storagebackend/factory/etcd3.go:434`,
`StartCompactorPerEndpoint`, every 5 minutes by default). Every apiserver of a cluster runs one, and
they coordinate through one etcd key, `compact_rev_key`. A round of `Compact(ctx, client,
expectVersion, rev)` (`compact.go:216`) works like this:

- It runs one transaction: if the key's version is `expectVersion`, put `FormatInt(rev)` to the key;
  otherwise get the key.
- **The put wins** (one apiserver per round). The winner's version becomes `expectVersion + 1`, and
  it compacts etcd at `rev`, the header revision it read in its previous round, one interval ago
  (unless `rev = 0`, its first round).
- **The compare fails.** The loser adopts the key's version and its value, the revision the winner
  recorded.
- **Either way,** the apiserver keeps the transaction's header revision as the `rev` of its next
  round.

So a compaction always lands at a revision the cluster had reached at least one interval earlier:
watchers and lists get at least one interval of history. That is the property operators rely on.

`compact.go` is 14 functions and about 170 lines of Go code: `StartCompactorPerEndpoint`,
`NewCompactor`, `Stop`, `CompactRevision`, `UpdateCompactRevision`, `runCompactLoop`, `Compact`,
`runWatchLoop`, `getCompactRev`, `fromWatchResponse`, `init`, and three closures. It is translated
(`Code/k8s_io/apiserver/pkg/storage/etcd3.lean`), except `fromWatchResponse`, which is names-only
(below). None of it is specified. The `k8s/etcd3` example runs the store with `noCompactor{}`, and
the k8s plan's phase 0 configures the compactor off (`notes/k8s-etcd3-plan.md`).

## Found while planning

Both are recorded in `nonissues/`:

- **`k8s-apiserver-compactor-missing-key-panic.md`.** `Compact` panics when `compact_rev_key`
  disappears after a compactor has written it: the else branch reads `Kvs[0]` of an empty get. It is
  known upstream (kubernetes#139252, fix #139254 open). The specs take the invariant that nothing
  deletes the key (K2).
- **`k8s-apiserver-compactrevision-ahead-of-etcd.md`.** `CompactRevision()` is the latest revision
  *recorded* in the key, not one etcd has compacted: the winner records it before compacting, and
  its compaction can fail. It is documentation only and errs on the safe side. The spec says
  "recorded".

## What exists underneath

- **The etcd client.**
  - `kv.Txn` handles a `Version` compare (`InvCmp.lean`; `etcd/txnlin` uses one).
  - `kv.Compact` is specified and linked (`Spec/go_etcd_io/etcd/client/v3/kv__Compact.lean`). It
    requires `1 ≤ rev`, a compacting cluster (`γ.cmp = true`) and `kvRevLbZ γ (rev + γ.cret)`: the
    revision reached, `cret` behind.
  - `Client.Endpoints` and `Watch` (the watch loop) have specs.
- **The standard library and apimachinery.**
  - Perennial specifies `time.After`, `strconv.ParseInt`/`FormatInt` and `sync.Once`.
  - `k8s.io/utils/clock`'s `RealClock.After` and apimachinery's `wait` are specified here.
  - To check: `wait.ContextForChannel`.
  - `WaitGroup` follows the bounds plan (`notes/bounds-plan.md`): the compactor owns its wait group,
    backed by thread tokens.
- **The server.** Today, compaction mode means etcd's own compactor is on. `NewServer.specG on cmp`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServer.lean:143`) states the mode inline:
  - `ρ.rd.kv.cmp = cmp` and `E₀.cmp = cmp`;
  - `if cmp then (revision mode, 0 < retention, cret ≤ retention) ∨ (periodic mode, 10 ≤ retention,
    cret = 0) ∧ on = false else AutoCompactionRetention = 0`.

  A cluster whose compactions all come from clients, with the auto-compactor off, is Kubernetes'
  deployment, and it is not among these modes. `etcd/compactwatch` issues client compactions, but on
  a server whose compactor is also on (`StartCompactingServer`).

## Scope questions for the user

**Q1. Which loops.**
- **(a)** `runCompactLoop` and `Compact` (the CAS protocol), with `NewCompactor` (interval nonzero,
  the `ListFromCacheSnapshot` gate off), `Stop`, `CompactRevision` and `UpdateCompactRevision`.
- **(b)** Adds `runWatchLoop`, `getCompactRev` and `fromWatchResponse`. They need goose's fix for
  field selection through a type alias (G1, `notes/perennial-changes.md`: small, tried; an
  independent Perennial change) and the watch spec at one key with `WithRev`.
- **(c)** Adds `StartCompactorPerEndpoint`, the production entry point: a global map under a mutex,
  keyed by `client.Endpoints()`.

*Recommended: (a) then (c); (b) after G1 lands.*

**Q2. Which program.**
- **(i)** A new example, `examples/k8s/compactor`: one etcd member with the auto-compactor off, two
  or three compactors (one per simulated apiserver, each with its own client, a short interval),
  and concurrent writers. When it stops, `Main` checks the guarantee:
  - each compaction revision is one a compactor recorded;
  - it is at most the revision the cluster had reached when the recording compactor's previous round
    returned;
  - `CompactRevision()` only grows, and is at most the key's value;
  - nothing panics.
- **(ii)** Compaction steps in `k8s/etcd3`'s traffic, as `TestCorrectness`'s `OpCompact`. That only
  matters to the store's list and watch paths, which are not verified yet (G2, phase 5). The Model's
  compact step is also atomic where Go's is two steps: the key's put (resource version + 1), then the
  compaction. A read between the two sees the new resource version uncompacted, which no
  linearization of the Model's step allows. The traffic would have to run compactions alone, or the
  Model would have to split the step; that is a question for later.

*Recommended: (i) now, (ii) with phase 5.*

**Q3. What a round guarantees.** The loop sleeps on `clock.After(interval)`, and the logic has no
time. The statement is in rounds:

> every compaction is at a revision `r` with `0 < r`, recorded in `compact_rev_key` by the winner of
> a round, where `r` is the header revision of the winner's previous round.

So at least one of its intervals separates reaching `r` from compacting it. "History for at least
the interval" is then a fact about the loop's structure (one `After` between the rounds), stated in
the spec's text and checked by the Go test, not by the proof.

*Recommended:* that, as etcd's periodic compactor's C1 was stated (`notes/compactor-pilot-plan.md`).

## Stages

**K1. The server's compaction mode into slots, then the client-only mode.** This changes the
server's statements, so it goes through the slot convention.

1. *The slots.* Move the compaction mode out of `NewServer.specG`'s text into the compactor
   subsystem's slot:
   - `v3compactor.bootCfg cfg γc` (sealed; its API module beside `v3compactor/New.lean`) reads the
     configuration's mode and retention and the compaction fields of the KV names (`cmp`, `cret`).
   - The KV invariant's relation to the compactor's configuration (`cret ≤ retention`) is a coupling
     the compactor owns: a law of its API that the KV side consumes, as `rafthttp.bootCfg dir ps`
     takes raft's peers.
   - The auth coupling (`cmp → on = false`) stays inline until auth converts, or becomes a named
     cross-slot predicate. That is for the hub's review to decide.
   - `E₀.cmp = cmp` and `ρ.rd.kv.cmp = cmp` become the agreement of one `cmp` carried by the slot's
     names, not three copies.
   - Laws for today's callers: `bootCfg_off` (retention 0, `cmp = false`), `bootCfg_revision` and
     `bootCfg_periodic`.
   - The starters (`StartServer`, `StartCompactingServer`, `StartPeriodicServer`, `newServerMode`)
     change once, to pass the slot.
   - A Draft of the hub alone, then a Review (the convention's step 1 procedure). The user approves
     the new `NewServer.specG` text.
2. *The client-only mode,* inside the sealed body: `cmp = true` with `AutoCompactionRetention = 0`
   and `cret = 0`. It comes with a law `bootCfg_clientOnly`, and the hub's text is unchanged
   ("Modes generalize, no twins").
   - To check in the proof: `run`'s compactor arm at `cmp = true` with a nil compactor
     (`compactorOk` already admits nil).
   - The examples get a starter at that mode: a mode parameter of an existing starter, not a new
     copy.

**K2. The specs (Draft, for review with the `spec` skill and the `spec-reviewer` agent).**

- **The key's invariant** `compactKeyInv γ` (new client-owned ghost state over the client's
  `etcdKV`: the user's decision, per the spec skill):
  - every version of `compact_rev_key` holds `FormatInt r` with `0 ≤ r` and `r` reached when written;
  - nothing deletes the key;
  - only compactors write it.

  The workload premise is that the other writers' keys exclude it (the store's prefix does).
- **`Compact.spec`.**
  - *Precondition:* the client (`isKv`, at `cmp`, `cret = 0`), `compactKeyInv`, `kvRevLbZ γ rev` (or
    `rev = 0`), and the round's own fact for `expectVersion`: 0, or a version this compactor saw.
  - *Postcondition:*
    - `currentRev` is reached (`kvRevLbZ`) and is the next round's `rev`;
    - `currentVersion` is a version of the key;
    - `compactRev ≠ 0` means it was recorded in the key; on the winning arm, etcd compacted at it,
      or the call returned `kv.Compact`'s error.
  - The else branch's `Kvs[0]` is safe because `expectVersion ≥ 1` means the key exists, which
    follows from the invariant.
- **`compactor`'s predicate** `isCompactor c γc` (mutex, `compactRevision`, the stop channel, the
  wait group):
  - `CompactRevision` returns a recorded revision, monotone (a lower-bound token);
  - `UpdateCompactRevision` keeps the max;
  - `Stop` is idempotent (`sync.Once`) and returns the loop's thread tokens.
- **`runCompactLoop`.** Each round's `Compact` gets its `rev` from the previous round. It returns
  once the stop channel closes.
- **`NewCompactor`.** At interval nonzero and the gate off, one goroutine, and `isCompactor`.

**K3. Test the specs against Go** (spec-first phase 2):
- The example of Q2 (i), and Go checks of each post's claims.
- Its failing-key variant: delete the key mid-run and see the panic. If it reproduces at the pinned
  apiserver, the finding moves to `issues/` with that test.

*Done (2026-11-04).* `examples/k8s/compactor`, a Go module of its own (project `k8s-compactor` of
`etc/goose.py`, translated; `k8s/etcd3`'s pins, checked by `GO_MOD_PINS` and `CLIENT_GO_PINS`):
- `Main`: one member started by `StartCompactingServer` at retention 0 (its spec's premise now
  `0 ≤ retention`: the client-only mode, `bootCfg_off`, a mode of the existing starter), a readiness
  Get, `DisableSnapshotList` (U3's trusted spec, `Proof/.../examples/k8s/compactor/DisableSnapshotList.lean`:
  `gateOff`), a writer, three API servers each with a client and a compactor (interval 20ms, a
  `RealClock`, no `onClose`) sampling `CompactRevision` ten times, `Stop`, then checking: the samples
  never decrease; the last is at most a later latest Get's revision; `compact_rev_key` parses to a
  revision at most that one. Each check follows from K2's specs (`compactRevLb`, `recRevOk`, the
  caller's `recorded`, the `ParseInt` read-back); K4 proves them.
- The Go test: `TestCompactor` runs `Main`; `TestHistory` runs its workload with a watch of the key
  and checks what the specs do not state: the key's values increase, each the revision of the
  previous put (so below its own), successive puts at least an interval apart (Q3), the store
  compacted at one of the values. A run: `0@80 80@173 173@274 274@363 363@406 ...`, compacted at
  the last value.
- The failing-key variant (`TestMissingKey`, a child process): the key deleted after the first put,
  the compactor's next round panics (index out of range in `Compact`). It reproduces at the pinned
  apiserver as an upstream test (`TestCompactMissingKey`), so the finding moved to `issues/`
  (`issues/k8s-apiserver-compactor-missing-key-panic.md`; still `blocks-proof: no`).
- Found while testing: a member's first second is its election (a compactor's rounds before it
  fail, with nothing compacted), and a watch from an old revision is cancelled by a compaction that
  passes it before it syncs (the history watch starts at the store's revision).

**K4. Freeze, then prove:** `Compact`, then the compactor's methods, `runCompactLoop` and
`NewCompactor`. Link them (`etc/gen-link.py`: a new `--k8s` table entry). Then the example's
`Main` and its adequacy theorem `k8s_compactor_safe`: no panic, and the checks hold. Add a
collection, `etc/tcb-collections/k8s-compactor.txt`.

*First part done (2026-11-04).* The six functions are proved and linked (`notes/decisions.md`,
"Kubernetes' compactor proved"), with the collection.
- **The context.** `runCompactLoop`'s `wait.ContextForChannel` needed `ctxOk`'s third case, the
  user's choice.
- **Found while proving.** `Compact.spec` and its callers take the client's KV handle (`clientKvOk`, its `isKv`);
  `NewCompactor.spec` drops `threadTok`; `klog.Errorf` is a new logging axiom; `RealClock.After`
  is a named hypothesis.
- **Left:** `Main` and `k8s_compactor_safe`.

*Second part done (2026-11-04).* `k8s_compactor_safe` (`Results.lean`), closed, no `sorry`
(`notes/decisions.md`, "Kubernetes' compactor example proved"):
- The example's invariant (`Inv.lean`) owns the clients' KV state and `compact_rev_key`'s protocol;
  from it the compactors' contract (`casOk_of_cinv`: `Seen` a flag, `recorded := True`), the writer's
  put and `apiserver`'s reads (`Aus.lean`, over `CasModel.lean`'s model facts).
- The example's Go changed: `apiserver` checks the key's value against a second, later `Get`.
- New trust: `strconv.Itoa`'s axiom (the user's approval); the closed theorem takes
  `clock.RealClock.After`'s contract as a named hypothesis.
- Shared: `etcdstart/OneMember.lean` (one-member `BootFacts`, `premises`, `kvModel_boot`), first user.

**K5 (later).**
- Q1 (b) after G1 (the watch loop: a watch of one key from a revision; compaction cancels its watch,
  `notes/k8s-etcd3-plan.md` item 4).
- Q1 (c).
- Three members and partitions, as `etcd/partition`.
- Q2 (ii) with the store's phase 5.

## Risks

- K1 touches the hub other sessions edit most (`NewServer.specG`). Land it alone, at a quiet moment,
  as the slot convention intends.
- `compactKeyInv` is a protocol on the etcd KV's history, the first one a client package here owns:
  where its ghost state lives, and how other writers are kept off the key, is the Draft's main design
  question.
- Errors: `Compact`'s error arms need only "some error, the CAS fired at most once" (`kvOpAu1`), as
  the store's phase 4 did.
