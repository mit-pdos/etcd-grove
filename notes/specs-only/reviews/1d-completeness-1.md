# Batch 1d (client/v3/concurrency): completeness review, round 1

Reviewer: completeness (independent of the author). Read: `notes/specs-only/README.md`,
`review-brief.md`, `.claude/skills/spec/PRINCIPLES.md`; every spec of
`SpecPlan/Spec/go_etcd_io/etcd/client/v3/concurrency/` (the vocabulary in full, the exported functions'
triples), the four snippet files, the Go code (`.lake/src/client/concurrency/{session,mutex,election,stm}.go`)
and every user found below. `batch-1d.md` read only after the findings were formed (its open
question 3 is my finding C1, with a different answer). Snippets: `cd examples && go vet
./specreq/concurrency/` is clean.

Paths: `C/` is `.lake/src/client/` (client/v3 @ `a4d2bb17`), `S/` is `.lake/src/server/`, `T/` is
`/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/tests/v3@v3.0.0-20261103162249-673da07c8fab/integration/`.

## Users and patterns

Users of the package outside it (`grep 'etcd/client/v3/concurrency"'` over the pinned module cache
and `examples/`): `S/etcdserver/api/v3lock/lock.go`, `S/etcdserver/api/v3election/election.go`,
`C/leasing/kv.go`, `S/proxy/grpcproxy/register.go`, `C/experimental/recipes/{key,rwmutex,double_barrier}.go`,
etcd's integration tests (`T/clientv3/concurrency/*`, `T/v3_election_test.go`, `T/v3_stm_test.go`,
`T/v3lock_grpc_test.go`, `T/v3election_grpc_test.go`, `T/clientv3/experimental/recipes/v3_lock_test.go`,
`T/clientv3/lease/leasing_test.go`), and this repository's `examples/specreq/{concurrency,recipes}`.
Kubernetes: nothing under `/home/ubuntu/go/pkg/mod/k8s.io/` imports it. etcdctl is not in the
module cache. No production user of the STM (tests only).

| # | pattern | relies on | example call site | snippet | verdict |
|---|---|---|---|---|---|
| P1 | a session per RPC over the remote client's lease (`WithLease(req.Lease)`, `WithContext(rpcCtx)`), `Orphan()` at once; lease `0` grants one, `-1` for `Leader`/`Observe` | no panic; `Lease()`/`Client()` usable after `Orphan` | `S/.../v3lock/lock.go:36-44`, `v3election/election.go:125-135` | `ReqSessionResumeLease`, `ReqV3LockPattern` | pre not establishable: C1 (token), C5 (principal) |
| P2 | sessions made **again and again** in a loop, each waited on with `Done()` | no once-only resource per session | `C/leasing/kv.go:129-157` (`monitorSession`), `S/proxy/grpcproxy/register.go:42-58` | none | **uncovered**, and unprovable: C1 |
| P3 | `Done()` in a `select` (blocking or with `default`) | a receive never yields a value | `C/leasing/kv.go:133,484`, `register.go:48-56` | `ReqSessionDone` | covered |
| P4 | `WithTTL(ttl)`, `Lease()` on an endpoint key, `Close()` on error/shutdown | lease id usable in a put; Close returns | `register.go:65-79` | `ReqSessionLease`, `ReqSessionClose`, `ReqSessionTTL` | covered (S2 on the snippet) |
| P5 | recipes: `Client()`, `Lease()` from any goroutine | persistent handle | `C/experimental/recipes/key.go:142` | 1f's snippets | covered (1f's req answered) |
| P6 | `Mutex.Lock` then `Key()`/`Header()` returned to a remote client, which unlocks by deleting the key | header non-nil, positive revision; key under the prefix | `v3lock/lock.go:45-49` | `ReqV3LockPattern` | covered; freshness missing: C3 |
| P7 | fenced write `Txn(If(m.IsOwner()))` | exclusion of revisions | `T/clientv3/concurrency/example_mutex_test.go`, top-level story | `ReqFencedWrite` | covered |
| P8 | `TryLock` / `ErrLocked`; `Unlock` / `ErrLockReleased`; `NewLocker` | error identities | `T/clientv3/experimental/recipes/v3_lock_test.go:143`, `T/clientv3/concurrency/mutex_test.go:63-91` | `ReqTryLock`, `ReqLockUnlock`, `ReqLocker` | covered |
| P9 | `Campaign`, then `Header()`, `Key()`, `Rev()`, `s.Lease()` as the remote leader key | key under prefix, `c` its create revision, header | `v3election/election.go:40-57` | `ReqCampaignProclaim` | covered; C3, C4 |
| P10 | **resume by leader key**: `ResumeElection(s, name, req.Leader.Key, req.Leader.Rev)` then `Proclaim`/`Resign`, all fields remote-chosen | no panic whatever the key and revision; the fence decides | `v3election/election.go:60-73,110-123` | `ReqResumedProclaim` | covered by a snippet, but the spec is false at `Rev = 0`: C2 |
| P11 | `Leader()`: `l.Header`, `l.Kvs[0]` | one key-value, a header | `v3election/election.go:98-108` | `ReqLeader` | covered |
| P12 | `Observe()` consumed **in a `select` with `ctx.Done()`**, `resp.Header`, `resp.Kvs[0]` forwarded | one key-value, a header | `v3election/election.go:81-94` | `ReqObserve` uses `for range` | **uncovered**: C4 |
| P13 | Header order across two RPCs (`l1.Header.Revision < l2.Header.Revision` after `l1` unlocked/resigned) | the returned state is after the call began | `T/v3lock_grpc_test.go:49`, `T/v3election_grpc_test.go:52` | none | **uncovered**: C3 |
| P14 | STM transfer keeping a sum (default level and `RepeatableReads`), concurrent `NewSTM`s | serializability of the committed attempt; closure's captured state | `T/clientv3/concurrency/example_stm_test.go:53-81`, `T/v3_stm_test.go:52-80` | `ReqSTMTransfer` | covered (C1 for concurrent callers) |
| P15 | STM retries with closure side effects (`try++`), closure's own error | frame `F`; error returned | `T/v3_stm_test.go:245-266, 286-300` | `ReqSTMAbort`, `ReqSTMTransfer` | covered |
| P16 | `Serializable` read-only attempt checks its reads agree | one-revision view inside an attempt | `T/v3_stm_test.go:199-216` | none | correctly **not** served: false of the code (`issues/stm-serializable-snapshot.md`) |
| P17 | `WithAbortContext` + cancel inside the closure, then "nothing committed" | an already-cancelled request is never sent | `T/v3_stm_test.go:141-160` | `ReqSTMLevels` (no check) | test-only; W0's matter (S6) |
| P18 | `Session.Ctx()` cancelled after `Orphan` | liveness | `T/clientv3/concurrency/session_test.go:87` | none | test-only, margin stated |

## What is good

- The **fence** design (`lockedSince`/`waitedFor` + the pure law `fence.spec`, `Api.lean:599`) is
  the right abstraction without time: it serves P7 and the election's fenced writes, and it stays
  true under `issues/mutex-lock-recreated.md`. `ReqFencedWrite` and `ReqLeaderFenced` rely on
  exactly it.
- Constructors take no client premise and no prefix bound; one spec per function, the deprecated
  STM constructors are instances. Every function of the package has a spec.
- Effects stated in the model (`keysEff`, `grantEff`, `revokeEff`, `stmEff`) through one
  persistent permission: a caller's invariant only has to be stable under them, which serves
  v3lock/v3election (their effects are the remote principal's writes) and leasing (1e's
  `protoUpd`). `grantEff` matches W0's `leaseStep` grant exactly (`Model.lean:897-903`).
- `applyOk`'s attempt-indexed frame `F` serves the tests' captured variables and retry counters.
- The STM's in-attempt view is promised nothing on failed attempts, which is right
  (`issues/stm-serializable-snapshot.md`; P16 is a pattern the code does not support).
- `Session.Done` as Perennial's broadcast channel serves every `select` use (P3), including
  leasing's non-blocking one.

## First tier

### C1. The `threadTok` premise of `NewSession`, `Election.Observe`, `NewSTM*`, `runSTM` is unneeded, and it makes the looping and per-RPC users unprovable

Principle: "No unneeded premise"; "Complete"; "A once-only resource is not spent per call".

Evidence. Perennial's `wp_fork` forks **without** a token (`.lake/packages/perennial/Perennial/GooseLang/Lifting.lean:1977`:
`▷ WP e {{ ⌜¬panic⌝ }} -∗ ▷ Φ #() -∗ WP (Fork e) {{ Φ }}`): `Fork` draws the forked thread's token
from the thread fuel and the thread returns it at `ThreadExit` (`Threads.lean`'s header,
"Accounting"); the bounds plan says the same for clients: "`threadTok` (each goroutine has one;
Fork provides it)" (`notes/bounds-plan.md:67`). The goroutines of `NewSession` (`session.go:68-76`),
`Observe` (`election.go:169`) and `runSTM` (`stm.go:143`) need nothing else of a token. As stated,
each call consumes one token for good (`Session.Orphan`/`Close`/`Done` and `stmResult` give none
back).

Callers affected: leasing's `monitorSession` (`C/leasing/kv.go:129-157`: a new session every time
the last one is done, for the life of the KV; 1e asked for "nothing once-only per call",
`req/go_etcd_io_etcd_client_v3_concurrency.md`, "from 1e"); the grpc proxy's `Register`
(`register.go:42-58`, a new session per expiry); v3lock and v3election (a session per RPC,
`lock.go:36`, `election.go:126`, plus an `Observe` goroutine per Observe RPC); concurrent
`NewSTM` callers. None of them has an unbounded supply of tokens, so none of these loops is
provable. The author's open question 3 proposes to accept this ("a run makes at most
`threadBound` of them"); it need not be accepted, because the premise is not needed at all. No
snippet makes sessions in a loop (pattern P2 uncovered), which is why the snippets did not show it.

Restatement: drop `threadTok` from the pres of `NewSession.spec` (`NewSession.lean:69`),
`Election.Observe.spec` (`Election__Observe.lean:52`), `NewSTM.spec`, `NewSTMRepeatable`,
`NewSTMSerializable`, `NewSTMReadCommitted`, `runSTM.spec`; their sketches use `wp_fork` (as the
old specs did). Add a snippet `ReqSessionLoop` (leasing's/register's shape: `for ctx.Err() == nil {
s, err := NewSession(cli); if err != nil { continue }; select { case <-s.Done(): case <-ctx.Done():
s.Close(); return } }`). Reply to 1e that the session costs no token.

### C2. `Election.Proclaim.spec` is false at a leader revision `0` (reachable from v3election's resume path)

Principle: "Sound" (found while checking P10's pre against the values v3election passes).

Evidence. v3election builds the election from the remote request: `ResumeElection(s, name,
req.Leader.Key, req.Leader.Rev)` (`election.go:68`); `Rev` is a protobuf `int64`, `0` when the
remote client omits it. `Proclaim` sends `If(CreateRevision(leaderKey) = leaderRev)
.Then(OpPut(leaderKey, val, WithLease(...)))` (`election.go:115-118`). A comparison on an absent
key compares the zero key-value: W0's `Compare.holds` (`Model.lean:677-679`: `l = [] → c.holdsOf
(KV.zero c.key)`), i.e. `CreateRevision = 0` holds of an absent key, as in etcd. So with
`leaderRev = 0` and the key absent, the transaction succeeds and creates the key, and `Proclaim`
returns `nil`. The spec's success disjunct claims `∃ r, σ.kv.store st.leaderKey = some r ∧
r.createRev = sint.Z st.leaderRev` at the pre-state `σ` (`Election__Proclaim.lean`, post, first
disjunct): false there (the key is absent; and no present key has create revision `0`).

Caller affected: v3election's `Proclaim` handler (2e), any `ResumeElection` user with an unchecked
revision; `ReqResumedProclaim` passes an arbitrary `rev` and so exercises it.

Restatement: the success fact is the comparison as the code makes it: `Compare.holds (ownerCmp
st.leaderKey st.leaderRev) σ.kv.store` (or spelled out: `(∃ r, store k = some r ∧ r.createRev =
rev) ∨ (store k = none ∧ sint.Z rev = 0)`); the failure disjunct is its negation (already true as
stated). Check `Election.Resign.spec` the same way (its post is true at `rev = 0`, but state it as
`¬ Compare.holds …` after the delete, for symmetry). Mention in `ResumeElection`'s margin that a
revision `0` makes `Proclaim` create the key (v3election does not check the remote revision; a
candidate `nonissues/` entry: v3election's documentation says the leader key is the one `Campaign`
returned).

### C3. No result is ordered after the call began: callers cannot sequence a lock or an election after earlier events

Principle: "Complete: sufficient for every caller"; "Facts that can be combined" (a fact at an
unknown point unrelated to what the caller holds).

Evidence. Every result of the package is `etcdLb γ σ` with a pure fact at `σ` (`Mutex.Lock`,
`TryLock`, `Unlock`, `Election.Campaign`, `Proclaim`, `Resign`, `Leader`, `Session.Close`,
`NewSession`'s grant, `observeAt_recv`, `stmResult`). Nothing ties `σ` to the states the caller
already knows: W0's `etcdLb_ord` (`State.lean:103`) orders two lower bounds but cannot say which is
later, and `etcdLb_reach` needs `etcdState`, which the package only reaches inside the caller's
permission. The code is linearizable here (each result comes from a request sent after the call
began), and the Api header says "at a state `σ` the mutex reached after it began" (`Api.lean:16`),
but the triples do not.

Callers affected: v3lock's and v3election's RPCs (2e must answer a Lock/Campaign/Leader RPC with a
header no older than the request, the linearizability of the RPC); their integration tests rely on
it directly: `T/v3lock_grpc_test.go:49` and `T/v3election_grpc_test.go:52` (`l1.Header.Revision <
l2.Header.Revision` for a lock taken after `l1` was released); `ReqV3LockPattern` only checks
`Revision > 0`. Pattern P13 has no snippet.

Restatement: each spec that returns a state takes the caller's lower bound and orders the result
after it: add `etcdLb γ σ₀` (for any `σ₀`) to the pre and `⌜Reach σ₀ σ⌝` (for every returned `σ`)
to the post; the proofs have it from `etcdLb_reach` inside the permission's first firing after the
call starts. (Alternatively one law of the permission: its commit also gives `Reach σ₀ σ` for every
`etcdLb γ σ₀` the caller held, which is what `etcdLb_reach` inside the update gives; but it must
reach the caller, so it belongs in the triples.) Snippet: `ReqLockAfterUnlock` (lock, read the
header, unlock, lock again with another session, `panic` if the second header is not greater).

### C4. `Observe`'s channel has no `select` law, and v3election receives from it in a `select`

Principle: "Complete"; "A client does not unfold the spec's definitions" (a missing law).

Evidence. v3election's `Observe` handler receives in `select { case <-stream.Context().Done(): case
resp, ok := <-ch: … }` (`election.go:83-93`), forwarding `resp.Header` and `resp.Kvs[0]`. The only
law on `observeAt` is `observeAt_recv.spec` (`Api.lean:652`), a plain `chan.receive`. A `select`
needs the channel's receive atomic update (Perennial's `recvAu`), as W0 gives for watch channels
(`watchChAt_recvAu.spec`, `ApiWatch.lean:473`). `ReqObserve` uses `for range`, so P12 is
uncovered. Without the law, 2e's `Observe` handler must unfold `observeAt`.

Restatement: add `observeAt_recvAu.spec` in `watchChAt_recvAu`'s shape (`observeAt ch γ pfx R ⊢ ∃
γc, isChan ch γc … ∗ (£1 ∗ £1 -∗ (▷ ∀ p ok, <observeAt_recv's outcome> -∗ Φ p ok) -∗ recvAu γc … Φ)`),
and change `ReqObserve` to v3election's loop (`for ctx.Err() == nil { select { case <-ctx.Done():
case resp, ok := <-ch: if !ok { return }; … resp.Kvs[0] … } }`).

### C5. (cross-batch, W0/2e) v3lock and v3election use the in-process client, whose principal comes from the RPC context's incoming metadata; the cleanup paths run as nobody

Principle: "A premise inherited from a callee is checked against the value the caller's Go code
actually passes".

Evidence. etcd's v3lock/v3election servers get `v3client.New(s)` (`S/embed/serve.go:149-150`), a
`NewCtxClient(context.Background())` whose KV and Lease call the server's handlers directly
(`S/etcdserver/api/v3client/v3client.go:30-36`). The handlers' context is the gRPC request's, and
the server's auth reads the principal from its **incoming** metadata (`S/auth/store.go:1077-1096`,
via `S/etcdserver/v3_server.go:1206`). So every request of a v3lock/v3election call runs as the
remote user, not as a principal fixed by the client: `isClient c γ who` with one `who` (W0) does not
describe this client. Worse for 1d's specs: the cleanup paths use the client's own context,
`m.Unlock(client.Ctx())` (`mutex.go:92,99`) and `e.Resign(client.Ctx())` (`election.go:98`), a
background context with no metadata, so with auth on they run unauthenticated (`isOpPermitted`:
`ErrUserEmpty`, `auth/store.go:868-871`). The 1d sketches take `ctxPrin ctx who` for the call's
context and `Client.Ctx.spec`'s `ctxPrin (client.Ctx()) who` for the cleanup's, the same `who`:
no single `who` makes both true at v3lock's call site when the remote user authenticates.

The 1d statements themselves are principal-agnostic in their effects (`keysEff` holds of a refused
cleanup too), so the fix is mostly W0's (a vocabulary for the in-process client: `isClient` for
every principal, the principal taken from the context), but 1d's `isSession s γ who id` fixes one
`who` for both the call and the cleanup. Suggested: a `req/` to W0 and 2e describing the in-process
client; in 1d, let the cleanup's principal be any (the sketches need only that the cleanup's step
is in `keysEff`, which holds of a refusal), e.g. `isSession` giving `isClient c γ who'` for the
client's own principal separately from the call context's `who`. Uncertain how W0 will model it;
listed first-tier because P1's real call site cannot establish the pre today under auth.

Possible Go bug (not reproduced, not filed): with auth enabled, a v3lock `Lock` whose context is
cancelled while waiting leaves its waiter key `name/<lease>` behind (the cleanup delete is refused
as unauthenticated), and it holds the lock for nobody until the remote client's lease ends. Worth a
test before an `issues/` entry; nothing in `issues/` or `nonissues/` covers it.

### C6. `Election.Resign.spec`'s effect admits a put with lease `0`, which `Campaign`'s own cleanup cannot grant

Principle: "No unneeded premise" (and the sketch of `Campaign` fails on it).

Evidence. `Resign` only deletes (`election.go:138`), but its pre requires `effIn (keysEff (fun k =>
k = st.leaderKey) 0) T` (`Election__Resign.lean`), and `keysEff` includes a put of the key with
lease `0` (`Api.lean:189-190`). `Campaign` calls `Resign` on two paths (`election.go:87,98`) with its
own `T ⊇ keysEff (pfx <+: ·) id`, which contains puts with lease `id` only: unless the session's lease
is `0`, `Campaign`'s sketch cannot discharge `Resign`'s premise. v3election's `Resign` handler must
also tolerate a lease-free put of a remote-named key it never makes.

Restatement: `Resign`'s effect is a delete of its key or nothing: `effIn (fun σ σ' => σ' = σ ∨ σ' =
delKey σ st.leaderKey) T` (a `delEff k` beside `keysEff`).

## Second tier

- **S1. `ReqSTMRepeatable`'s second panic is unprovable.** `if v1 != "" && r1 == 0` needs a present
  read to have a positive mod revision; inside the closure, `GetPost`/`RevPost` relate the value
  and revision to one `ReadM` but nothing ties a `ReadM` to a reached state (the read set's
  realization does, `readSetAt`'s docstring, but no law gives it to the closure). Either a law
  `stmAt_reads` (`stmAt iv γ who iso a ⊢ ∃ σ, etcdLb γ σ ∗ ⌜a.readsSeen σ.kv⌝`, plus W0's positive
  revisions) or drop the check. No production user relies on it.
- **S2. `ReqSessionLease`'s checks need facts the specs do not give.** `s.Client() != cli`:
  `isSession s γ who id` does not record the client, and `Session.Client.spec` returns some `c`
  with `isClient c γ who`; no user compares them (drop the check, or index `isSession` by the
  client if a user needs it). `s.Lease() == NoLease`: needs "lease `0` is never live" at a reached
  state; W0's grant never picks `0` (`Model.lean:899`) but I found no law exporting it (1d's `req`
  to `api/v3` asks only for positive key revisions). Ask W0 for it or drop the check.
- **S3. No snippet for what a v3lock remote client can rely on with only the key and the header.**
  `LockResponse` carries `Key` and `Header`, not the create revision (`lock.go:49`). With
  `lockedSince`'s `c ≤ createRev` (the known gap), a remote fence on the key's existence or on
  `CreateRevision(key) ≤ Header.Revision` is not sound; that is the issue's consequence and 2e's
  contract to state, but a snippet showing what *is* provable from `(Key, Header)` would make the
  2e hand-off concrete.
- **S4. `Observe`'s and `Leader`'s states have no freshness either** (C3's restatement covers
  them); `ObservedAt` is otherwise what v3election forwards.
- **S5. `Mutex.Lock`'s `ErrSessionExpired` case**: tested only as `err != nil`
  (`T/clientv3/concurrency/mutex_test.go:52`); the stated fact (key absent at a reached state) is
  more than users need: fine.
- **S6. `WithAbortContext` + cancel ⇒ nothing committed** (`T/v3_stm_test.go:141-160`) relies on a
  cancelled context's request never being sent; `stmResult`'s error case promises nothing about the
  state (right for a context cancelled mid-flight). Test-only; W0's `indefCall` is where it would go.
- **S7. `Session.Close` folds `ErrLeaseNotFound` into the bare error case** (its margin). The grpc
  proxy ignores the error; fine.
- **S8. `etcdPerm`'s cost to callers** (open question 1): for v3election, whose remote clients'
  Proclaims a linearizability log would want to record, the facts-after shape is enough for the
  handler (it returns the header), so I see no completeness gap from the permission itself beyond C3.

## Targets ranked by need of revision

1. **Election** (`Election__{Proclaim,Resign,Observe,Campaign}`, `observeAt` laws): C2 (unsound at
   rev 0), C4 (missing `select` law, v3election's pattern uncovered), C6 (Resign's effect), C3.
2. **Session** (`NewSession`, `Session.*`): C1 (token; leasing, grpc proxy, v3lock/v3election
   unprovable), C5 (principal at v3lock/v3election), S2.
3. **STM** (`NewSTM*`, `runSTM`, `stmAt`): C1 (token), S1; otherwise complete for its (test-only) users.
4. **Mutex** (`Mutex.*`, `NewLocker`, `lockerMutex.*`): C3 (freshness), C5 (cleanup principal), S3;
   the fence design serves every pattern.
5. **Api.lean** vocabulary: carries the laws to add (C4's `observeAt_recvAu`, S1's `stmAt_reads`)
   and C6's delete effect.

## Verdict

Not done: six first-tier findings. C1 (drop the thread token, which Perennial's `wp_fork` does not
need: this also answers open question 3), C2 (Proclaim's success fact as the comparison), C4 (a
`select` law for `observeAt`) and C6 (Resign's delete-only effect) are local and mechanical. C3
(results ordered after the call) is a uniform addition to the state-returning specs. C5 needs W0
and 2e to model the in-process client's principal; 1d's part is to stop tying the cleanup's principal
to the call's.
