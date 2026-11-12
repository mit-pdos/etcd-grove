# Batch 1d (client/v3/concurrency): provability review, round 1

Reviewer: provability. Read before forming findings: `README.md`, `review-brief.md`, PRINCIPLES.md,
`concurrency/Api.lean` and the specs, the snippets, the `## from 1d` requests, W0's `Model.lean` /
`State.lean` / `client/v3/Api.lean`, 1b's `ApiWatch.lean` (`watchStep`), Perennial's
`GooseLang/Threads.lean` and `Lifting.lean` (fork rules), the Go code (`.lake/src/client/concurrency/*.go`,
`client/watch.go`, `client/retry.go`, `server/etcdserver/api/v3election/election.go`).
`batch-1d.md` read only after the findings below, to mark which ones it already raises.

Line numbers: `mutex.go`, `key.go`, `election.go`, `stm.go`, `session.go` are in `.lake/src/client/concurrency/`;
`Api.lean` is `SpecPlan/Spec/go_etcd_io/etcd/client/v3/concurrency/Api.lean`.

## First tier

### F1. The thread tokens are not needed, and taking them for good makes callers unprovable
`NewSession.lean:69`, `NewSTM.lean:61` (and `NewSTM{Repeatable,Serializable,ReadCommitted}`,
`runSTM`), `Election__Observe.lean:52`.

Perennial's fork rule takes no token from the forking thread: `wp_fork` (`Lifting.lean:1977`) is
`▷ WP e {{ ¬panic }} -∗ ▷ Φ #() -∗ WP (Fork e) {{ Φ }}`. `wp_fork_tok` gets the forked thread's token
**from the fuel** and the thread returns it at its `ThreadExit` (`Threads.lean`, header: "`Fork` takes
one token out of the fuel and hands it to the forking thread"). The bounds plan says the same ("`threadTok`
(each goroutine has one; Fork provides it)"). So the goroutines at `session.go:68`, `stm.go:143` and
`election.go:169` need nothing from the caller. Batch-1d's open question 3 thinks the token must be paid
because the goroutine outlives the call; it does not have to be paid at all.

The premise is also harmful. A thread proved with `wp_fork_tok` has to hand back `threadTok` when it
ends, so a goroutine that calls `NewSession`, `NewSTM` or `Observe` once cannot be proved. That covers
v3election's and v3lock's gRPC handlers, leasing's monitor goroutine (`client/leasing/kv.go:147`, a
session per round) and every STM user that runs in a goroutine. The main thread holds one token, so it can make only
one such call. **`ReqSTMLevels` (7 `NewSTM` calls in one body) cannot be proved as written.**
`ReqSessionDone`/`ReqSessionClose`/... each make one call, which is fine only on the main thread.

Fix: drop `threadTok` from the seven specs and the sketches (use `wp_fork`). Open question 3 is then
moot.

### F2. `applyOk` quantifies over every starting attempt, so no closure can establish a useful `Rel`
`Api.lean:494-500`: `□ ∀ iv iso (a : Attempt), {{ stmAt iv γ who iso a ∗ ∃ b, F b }} apply iv {{ … Rel a' }}`.

`runSTM` always calls the closure right after `reset` (`stm.go:156-157`), on `Attempt.empty`. The
`WithPrefetch` wrapper (`stm.go:97-99`) calls it after a `Get`, so reads are present but there are
still no writes. With an arbitrary `a`, `a.writes` may already hold puts of any keys. `Get(k)` then
returns the buffered write's value, not a read (`GetPost`'s `find?` branch), and every pre-existing
write is committed as well. So `Rel a'` cannot constrain the writes. **`ReqSTMTransfer` cannot be
proved**: its `T`-stability needs `Rel` to say "the writes are exactly `a := x-amt`, `b := y+amt` for
the values read". The closure cannot ensure that from an attempt that already writes `c`, or writes
`a` (then `Get(a)` reads no balance at all).

Fix: quantify over attempts without writes, `∀ a, ⌜∀ k, a.writes k = none⌝ → {{ … }}`. Then `runSTM`
(from `Attempt.empty`) and the prefetch wrapper (`GetPost` keeps `writes`) still discharge it. An
alternative is `Rel a a'` relative to the start.

### F3. `Election.Proclaim.spec`'s success post is false when `leaderRev = 0`
`Election__Proclaim.lean:59`: on `nil`, `∃ r, σ.kv.store st.leaderKey = some r ∧ r.createRev = sint.Z st.leaderRev`.

`Proclaim` fences with `Compare(CreateRevision(leaderKey), "=", leaderRev)` (`election.go:115`). On an
absent key that compares the zero key-value (`Model.lean`'s `Compare.holds`, `KV.zero`, create
revision `0`), so at `leaderRev = 0` the comparison holds. The put then **creates** the key
(`election.go:117`), and `Proclaim` returns `nil` while the key was absent at `σ`. `leaderRev` is
arbitrary: `ResumeElection(s, name, key, rev)` takes it from the remote client in v3election
(`server/etcdserver/api/v3election/election.go:68,118`), and `ReqResumedProclaim` passes any `rev`.
`ResumeElection.spec` admits it and `Proclaim.spec` has no premise against it, so the spec is unsound.
The notLeader arm is fine. `Resign`'s post holds at `0` too: the key is absent afterwards.

Fix: state the fence as the comparison itself. Success: `⌜(ownerCmp st.leaderKey st.leaderRev).holds σ.kv.store⌝`.
NotLeader: its negation. For `leaderRev > 0` (after `Campaign`), a key present with create revision
`leaderRev` is then a pure consequence. Do not add a `0 < leaderRev` premise, because v3election
passes whatever it receives. (Go side: a remote `Proclaim` with `Rev = 0` and a fresh key creates a
leader key under the caller's lease. That is a precondition the API does not state; the author should
decide whether it belongs in `nonissues/`.)

### F4. `Campaign`'s sketch cannot call `Resign.spec`: the permission's lease does not match
`Election__Resign.lean:49` requires `effIn (keysEff (· = st.leaderKey) 0) T`. That relation includes a
put of the leader key **with no lease** (`keysEff`'s `putKey σ k v 0`, `Api.lean:189`), which `Resign`
never does: it only deletes (`election.go:138`). `Campaign` holds only `keysEff (pfx <+: ·) (sint.Z id)`
(`Election__Campaign.lean:58`). That relation does not contain lease-0 puts unless `id = 0`, so
`Campaign` cannot discharge `Resign`'s premise on either of its cleanup paths (`election.go:87, 98`).
For the same reason any caller of `Resign` must tolerate a write the code never makes.

Fix: give `Resign` its exact effect, `fun σ σ' => σ' = σ ∨ σ' = delKey σ st.leaderKey`. Optionally
narrow `Proclaim` to `σ' = σ ∨ ∃ v, σ' = putKey σ st.leaderKey v id`, since it never deletes.

### F5. `ReqObserve`'s header order rests on a request 1b has not granted, and it is probably false
`observeAt_recv.spec` (`Api.lean:659`, `R ≤ sint.Z hm.revision`). `observe` forwards each put event of
the leader key with the watch response's header (`election.go:240-242`). Two successive responses'
headers are ordered only if the watch's headers are non-decreasing. 1b's `watchStep`
(`ApiWatch.lean:230-253`) gives `header ≥ last event's mod revision` and `header ≤ a reached
revision`, not monotonicity: request 3 of `req/go_etcd_io_etcd_client_v3.md` is not met at `HEAD`. It
is also likely false of etcd. After a reconnect the client resumes on another member
(`client/watch.go:870-877` resumes from `nextRev`). A lagging member answers catch-up events with its
own current revision as the header, which can be below the header a more advanced member sent earlier.
I did not run this, so mark it uncertain; the dependency gap itself is certain.

Fix: drop `R ≤ …` from `observeAt_recv` and the order check from `ReqObserve`, as the request already
offers. `v.modRev ≤ hdr ≤ σ.rev` and `ObservedAt` stay. Within one round the values' mod revisions do
increase, which 1b's gap-free `watchEvents` gives, if a user needs an order.

### F6. `ReqSTMRepeatable`'s second check cannot be proved: the STM never exposes what its reads are
`if v1 != "" && r1 == 0 { panic }` needs "a read present key has mod revision ≥ 2". `GetPost` and
`RevPost` (`Api.lean:336-348`) relate the attempt's `ReadM`s only to each other. Nothing about
`stmAt` ties a read to the history during the closure (`readOf` lives inside `readSetAt`'s realization,
and `stmCommitted.readsSeen` arrives only after a commit). A `ReadM` with `kv := some {value := "a",
modRev := 0}` satisfies every law.

Fix: a law `stmAt iv γ who iso a ⊢ ∃ σ, etcdLb γ σ ∗ ⌜a.readsSeen σ.kv⌝`, or the same conjunct in
`GetPost`/`RevPost`'s results. With `etcdLb_init` (below) the check then follows. Otherwise weaken the
snippet.

### F7. `ReqSessionLease`'s `s.Client() != cli` cannot be proved
`NewSession`'s post is `isSession s γ who id`, which does not name the client.
`Session.Client.spec` returns `∃ c, isClient c γ who`, and `isSession_client` has the client under
`∃ c`. Nothing ties it to `NewSession`'s argument `c`, although the code stores it (`session.go:63`,
returned at `:83`). Fix: index `isSession` by the client (`isSession s c γ who id`), or add
`s.[Session, "client"] ↦□ c` to `NewSession`'s post, and make `Session.Client` return that `c`. 1f's
`sessionAt` would follow.

### F8. The permission never ends, so `ReqCampaignProclaim`'s "value lost" check cannot be proved
`etcdPerm γ T` (`Api.lean:434`) is a persistent update, and no spec promises that the package stops
firing it when the call returns. After `Campaign` (`keysEff (pfx <+: ·) id`) and `Proclaim`
(`keysEff (· = k) id`) the specs therefore allow a later put of `k` with **any** value, at **any**
time. Such a put keeps the create revision, because the key is present. So `Get(e.Key())` after a
successful `Proclaim("b")` can see create revision `c` and a value other than `"b"`: the panic is
reachable under the specs. The snippet's assumption ("only this election writes its own key") does not
help, because the election itself holds the permission.

In Go this happens for real only through a pending write: an earlier call that ended with an
indefinite error and lands later. A precise spec would say "after a definite return this call fires
nothing more". This is what batch-1d's open question 1 is about, but the question as posed there
("ghost work at a commit") misses the consequence. Every caller, not only the linearizability-log
ones, loses all facts about the contents of keys under the prefix (and about a revoked or granted
lease id, since `grantEff` may re-grant it) after the call.

Fix: choose and put to the user either (a) a permission lent per call and returned on definite
outcomes (an exclusive token the caller's update checks, kept by the call only on indefinite errors),
or (b) keep the design and restate `ReqCampaignProclaim` (and every snippet like it) so it relies only
on facts at the returned states. The fenced snippets (`ReqFencedWrite`, `ReqLeaderFenced`) are
unaffected: a late put keeps the create revision, and a late re-creation fails the fence.

## Second tier

- **S1. `etcdLb_init` is not in W0 at `HEAD`** (`State.lean` has no such law; it is `req/go_etcd_io_etcd_api_v3.md`,
  "from 1d"). Every `Mutex`/`Election` sketch needs it: `CreateRevision = 0` means absent, and
  `myRev - 1 > 0` (`mutex.go:89`, `election.go:93`; at `0`, `WithMaxCreateRev` is off). So do the
  STM's `isKeyCurrent` (`stm.go:365-370`: equal mod revisions mean equal records, which needs a
  well-formed history), `ReqSessionLease`'s `Lease() != 0`, and F6's fix. This is fine as a request,
  but the batch is not provable until W0 grants it.
- **S2. The header's claim about `Txn(If(m.IsOwner()))`** (`Api.lean:20-23`) is true of writes and of
  linearizable reads. A read-only transaction of serializable ranges is answered at a member's view
  (`Model.lean:883`), which may predate the lock state, so its fence proves nothing. Say "a write (or
  a linearizable read) fenced by…".
- **S3. `ReqLocker`'s `r.(error)` check.** `lockerMutex.Lock`/`Unlock` give `PanicV #err` with
  `err ≠ nil` only. Asserting `error` needs the dynamic type's method set, which nothing states
  (W0's `callErr .other` says only "not nil"). Uncertain: either state that client errors are `error`
  values or drop the check.
- **S4. `Proclaim`'s relation includes deletes it never makes** (see F4). That is harmless for
  `Campaign` (`keysEff pfx id` contains it), but it over-asks `ResumeElection` callers.
- **S5. `ReqSTMTransfer` and `ReqSTMAbort` also need F1** if they run off the main thread.

## (a)–(f) as asked

**(a) Fence and Lock.** `fence.spec` (`Api.lean:599`) is a true pure fact of W0's model, for any `σ`,
not only reachable ones. Writes take place only at `σ.kv` (`Model.lean:883`: only read-only
serializable transactions use a view). A put on an absent key records create revision `R = rev+1`
(`PutReq.record`, `Model.lean:622`), and a present key keeps its create revision. Revocation deletes;
compaction leaves the store alone. So a key under the prefix with create revision `< c ≤ σ.rev` at a
later state was present at `σ` with the same create revision, which contradicts `noOlder` at `σ`.

`Txn(If(m.IsOwner()))` succeeds exactly when the key has create revision `myRev`. `Compare.holds`
over the single key compares the zero key-value when the key is absent, and that fails because
`c > 0` (`waitedFor`). With `c < 2^63` from `etcdState_revFits` and `Reach` monotone,
`sint.Z (W64 c) = c`.

`lockedSince` is what `Lock` really gives. Fast path: `firstCreate` at the transaction's state
(`mutex.go:81-84`). Slow path: the empty filtered `Get` of `waitDeletes` (`key.go:55-60`) gives
`noOlder`, which lasts until the final `Get` (`mutex.go:97`) by the fence argument, and the key is
present there with create revision `≥ c`: equal to `c`, or re-created later. In the re-creation
scenario of `issues/mutex-lock-recreated.md`, the other session's key has create revision `> c`, so
`noOlder pfx c` still holds and the fence fails, as the header says. `ReqFencedWrite` is provable
(the counter is outside the prefix, so the transaction's inner `Get`s see the prefix unchanged).

**(b) Election.** `Campaign`'s post is right on all paths (`election.go:73-106`). The header is the
transaction's, `c ≤ hdr ≤ σw.rev`. `σv` is the transaction's or `Proclaim`'s `putKey` state (create
revision kept). Its sketch fails only through F4. `Proclaim`: F3. `Resign`: correct (`hdr = σ'.rev`
in all three cases). `Leader`: correct (`firstCreate` gives `holdsAt`). `Observe`/`observe`: in the
`waitDeletes`-like path A (`election.go:186-211`) the first put event after an empty prefix at `R0`
is a key created at `m > R0`. All keys present at `m` were created at `m`, so `ObservedAt` holds with
`r = m`. Overwriting the header (`:206`) is safe because responses with events own their headers and
are unicast (`client/watch.go:735-752`; only progress notifications are broadcast). In the key-watch
path, puts before the first delete are of the same key, never deleted meanwhile, so `ObservedAt`
holds by the fence argument. The per-round headers are ordered against the previous round's (each
`Get` is linearizable after a reached revision). Across watch responses within a round they are not
(F5).

**(c) STM.** `stmCommitted` matches the code at each level, given `etcdLb_init`:
- **SerializableSnapshot and Serializable**: every read is compared by mod revision (`stm.go:113,121,365`).
  The commit has a put, or an `Else` of linearizable gets, unless the attempt is empty, so it runs at
  `σ.kv` and `readsAgree σ.store`.
- **SerializableSnapshot's write compares**: `first()` is the minimum header over the read set,
  prefetched reads included, and `ModRevision < first+1` is exactly `∀ read, modRev ≤ e.hdr`.
  `first()+1` cannot overflow (`stm.go:199`).
- **RepeatableReads**: with writes, linearizable at `σ`. With none, `Txn().If(cmps).Then()` is
  read-only and vacuously serializable (`Model.lean:738`), so it is answered at a view: the stated
  `r ≤ σ.rev`.
- **ReadCommitted**: `readsSeen` only.
- **Prefetch**: prefetched reads (from the failed commit's `Else`, all at one revision) and later
  reads at another base or at the current revision (`stmSerializable.Rev` reads through `stm.fetch`
  without setting `getOpts`, `stm.go:332-334`) can mix revisions inside an attempt. The commit's
  comparisons still validate every read against `σ`, so serializability holds.
- **`applyOk`**: F2.
- **`GetPost`, `RevPost`, `fetch`**: match `stm.go:246-330` (first key already read returned, reads
  only extended, `Get()` of no key is `""`).

**(d) Permission soundness.** Each spec's effects are within its relation on every path:
- **tryAcquire, Campaign**: `putKey` of the key with the session's lease, or identity.
- **TryLock, Unlock**: `delKey` (`Unlock` checks the prefix, `mutex.go:139`).
- **Reads and refusals**: identity.
- **Grant**: `grantEff`.
- **Revoke**: `revokeEff`.
- **STM commit**: identity or `stmCommitted`.
- **Indefinite errors**: these land later, which the persistent permission covers.
- **Retried mutable RPCs**: `LeaseGrant` and `LeaseRevoke` are retried with the repeatable policy
  (`client/retry.go:150-156`). A lost-reply grant can therefore apply twice; a persistent `grantEff`
  covers that, where a one-shot update could not. That is a point in the design's favour.

What a caller can still prove: facts at the returned states (fence-based exclusion,
`lockedSince`, `waitedFor`, `holdsAt` at `Leader`'s state, `stmCommitted`). It cannot prove anything
about key contents or lease ids after the call (F8), and the `Resign` relation over-asks (F4).

**(e) Thread tokens.** They are not needed (F1).

**(f) Snippets.**

Provable as written (given `etcdLb_init` and `etcdState_revFits` from the caller's invariant):
- `ReqSessionResumeLease`, `ReqSessionDone`, `ReqSessionClose`, `ReqSessionTTL`;
- `ReqFencedWrite`, `ReqV3LockPattern`, `ReqTryLock` (with its stated assumption), `ReqLockUnlock`;
- `ReqLeader`, `ReqLeaderFenced`;
- `ReqSTMPrefetch`, `ReqSTMAbort` (`Rel := False`).

Not provable:
- `ReqSTMTransfer` (F2);
- `ReqSTMRepeatable` (F6);
- `ReqSTMLevels` (F1);
- `ReqSessionLease` (F7);
- `ReqCampaignProclaim` (F8);
- `ReqObserve` (F5);
- `ReqResumedProclaim` relies on the unsound `Proclaim` (F3). It becomes provable once F3 is fixed.

Uncertain: `ReqLocker` (S3).

## What is good

- **`lockedSince` and the pure `fence` law**: a precise, true statement of `Lock` that copes with the
  known re-creation bug without a disjunction. Exclusion comes out as a model fact.
- **`stmCommitted`**: per-level semantics that are correct in detail, including the empty read-only
  transaction answered at a stale view and the SerializableSnapshot write check.
- **`ObservedAt`**: robust, even to same-revision put and delete.
- **The permission**: handles the retried grant and late indefinite effects soundly.
- **Constructors take no client premises.**
- **Callee requests are explicit** (`etcdLb_init`, `ctxPrin` of `Client.Ctx`, events owning their
  headers).

## Targets ranked by need of revision

1. **STM**: `applyOk` (F2), the reads' facts (F6), tokens (F1).
2. **Election**: `Proclaim` is unsound at `rev = 0` (F3), the `Resign` relation (F4), `Observe`'s
   order (F5).
3. **Session**: tokens (F1), the client not named (F7).
4. **The permission design** (F8): a decision for the user.
5. **Mutex**: sound and provable; only S2 and S3.

## Verdict

Not done. Eight first-tier findings:
- **Unsound spec**: one (F3, `Proclaim` at `leaderRev = 0`).
- **Sketch that fails against its callee's spec**: one (F4).
- **Unprovable snippets**: six (F1, F2, F5, F6, F7, F8), one of which (F5) rests on a callee request
  that is not granted and is probably false.

The core guarantees (`fence`, `lockedSince`, `stmCommitted`, `ObservedAt`) are sound. The repairs
are local except F8, which needs the user's decision on the permission's lifetime. A second round is
needed.
