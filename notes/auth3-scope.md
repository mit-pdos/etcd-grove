# Scope: a three-member `etcd_auth_safe` (`etcd_auth3_safe`)

2026-11-14 · Scope agent for etcd-grove-81 · worktree `/shared/etcd-grove-auth3`, branch `auth3-scope`
(from lean `6b99efd348`) · notes only: no Lean edits, no builds. Go evidence (run at the etcd fork pin
`2eaeb872b`, clone `/shared/tmp/auth3-scope/etcd`, `GOWORK=off`, 32G cap):
`notes/auth3-scope/zz_auth3_token_replicated_test.go` (§2.2) and
`nonissues/etcd-watch-lagging-member-auth-off/lagging_member_watch_test.go` (§3). Both pass.

## 0. Summary

- **Recommendation: variant A first, in two steps.**
  - **A1** is putget3's shape: three members started with auth on, and every client on member 1,
    the only member that serves gRPC. It adds the three-member auth-on boot and the followers'
    applies with auth on. It needs no new server law and no change to the token contract.
  - **A2** then serves gRPC on every member, gives each principal its own member, and adds a
    barrier after `SetUp` (§3).
  - **B** is partition's shape plus auth. It comes after A2. It is the only variant whose
    schedules send snapshots and fail clients over between members.
- **The token correction is confirmed** (§2.2). A simple token is replicated through the log: the
  entry carries the prefix, and every member assigns `prefix.<consistent index>` at apply. The
  consistent index there is the same on every member: it is the previous entry's index, not the
  `Authenticate` entry's own, which upstream etcd-io/etcd#18437 also notes. Only the TTL keeper,
  and so expiry, is per member. A member refuses a token only when it has not applied the entry,
  skipped it through a snapshot, restarted, or let the token expire. All of these are refusals.
- **A lagging member is a real gap for any variant where a follower serves watches** (§3).
  - Watch creation, like a serializable read, is checked against the member's own auth state,
    with no read index. Once `AuthEnable` has returned, a follower that has not applied it still
    accepts an anonymous watch of `c/` from revision 1 and streams `c/anon/d`'s put. That would
    trip `Work`'s watch check. The Go test reproduces it.
  - The driver's reads are all linearizable, `Authenticate` waits for a read index, and writes are
    checked at apply. So the watches are the only exposure.
  - The driver fix is a barrier after `SetUp` that makes every member apply past `AuthEnable`.
  - It is recorded as a non-issue: etcd does not guarantee that `AuthEnable` takes effect on every
    member when it returns.
- **D22 need not come first.** `∀ hG, ⊢ authSchemaSrv` is one hypothesis, used once per member's
  `NewServer`, so it adds no new hypothesis.
- **Estimate:** A1 takes 4 to 6 agent-days. A2 takes 5 to 9 days more and needs one new
  server-side law. B takes several weeks.

## 1. Goal

**`etcd_auth3_safe` (A1).** Every real execution of `n` steps of `auth3`'s initialization followed
by `Main()`, from a fresh state with one thread, has:
- no stuck thread;
- no thread ended in a panic;
- a main-thread result, if any, of `0`, `1` or `2`.

`Main()` starts three etcd members of one new cluster, each with auth on (the simple token
provider, TTL 300 s). It then serves member 1's gRPC API and, through member 1, runs authkv's
set-up, its four principals' workloads, the history check and u's watch check. The hypotheses are
`etcd_putget3_safe`'s at auth3's configuration, plus D22's `authSchemaSrv`, as in
`etcd_auth_safe`.

In plain words, A1 says: with a three-member cluster, whose followers apply every admin and
`Authenticate` entry with auth on, member 1 never lets a principal do what the auth state forbids.
It also never applies a write the auth state forbids, as seen in the history check, which is a
cluster-wide fact: every member applies the log.

**A2: `etcd_auth3_safe` strengthened.** Every member serves gRPC. Each principal's client has one
member: u on member 2, v on member 3, anon, bad and root on member 1, for example. After `SetUp`,
a barrier makes each member apply past `AuthEnable`. The checks are unchanged. A2 adds that every
member, not only the one that took the admin requests, enforces the auth state on reads, watches
and writes.

**B: `etcd_auth_partition_safe` (later).** Partition's cluster (bridges, the partitioner, clients
of every bridge), with auth on, and authkv's checks in place of porcupine. A mended member may be
caught up by a snapshot that carries the auth buckets, and a client may use a token at a member
other than the one that issued it.

**Recommendation: A first (A1, then A2), B after.**
- A1 is mostly a recombination of two finished proofs: putget3's start and authkv's body.
- A2's one new law, the barrier giving each member's published auth state (§3), is also what B
  needs.
- B also needs the token fact lifted to the cluster level (§2.2), the client's re-authentication
  across members, and the snapshot schedules. None of these is in A.

## 2. What changes

### 2.1 The auth state on three members

**Today (one member).**
- The cluster allocation is already generic in the peers: `srvClusterBootOn_alloc ps ctxs boot …`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/NewServerAllocOn.lean:56`, exported as
  `server_cluster_alloc_on`, `etcdserver/Results.lean:2166`) takes `ps : List w64`. authkv calls
  it at `[id]` (`examples/etcd/auth/MainAlloc.lean:60`).
- The cluster-level auth state lives in the mode-on KV invariant: `kvInvOn`
  (`KVAuthModel.lean:900`) holds the requested log `srvRLog γ L`, the model state at `L` and half
  of the auth history `admStates γk st₀ L`. The client's view is the other half, `authHistView`
  (`KVAuthModel.lean:832`).
- Each member's store has its own names, `γa : auth.AuthNames` (`auth/Model.lean:361`: its
  history, cap, token map, published index, readiness, …). These are allocated by that member's
  `NewServer.specM true` (its post gives `γa`: `examples/etcd/auth/Main.lean:159`).
- The member's history is tied to the log it has applied by the server's tie (H5, `AuthTie.lean`:
  "the store's history is the applied log's (`srvHist A`)"; `AuthApplyRes.lean:61-66`, "What ties
  the apply thread's auth state to the model's (`kvRunOn`'s)").

**So the per-member stores already "agree by applying the same log".** Each member's store
history is `srvHist` of that member's applied prefix of the one log. The invariant is already
indexed by the apply position. What is missing for three members:

1. **`alloc3On`** (A1): `etcdstart.alloc3` (`lib/etcdstart/Alloc3.lean:311`) with the mode-on
   allocators. That is `srvClusterBootOn_alloc` at the three sorted peers in place of
   `srvClusterBoot_alloc`, and `srvMemberBootOn_alloc` three times, as `ak_alloc` does once, with
   `memberBootOn` per member. About 350 lines, mostly a copy. **Risk to probe first (S0):** that
   the mode-on member allocation composes three times, with nothing in the mode-on server
   assuming a single member. Reading found no such assumption in `ServerOn`, `KVApplyOn`,
   `AuthTie`, `AuthTieRead` or `NewServerAllocOn`: no `vs = [_]`, and each member's cap is its
   own `γa.cap`. But only a build shows it.
2. **Followers apply auth entries proposed elsewhere** (A1). Their `Authenticate` entries assign
   the token at each member's own `γa.tok`, with the per-member fresh right (`auth/Tokens.lean`
   header). Since the token is `simpleTok pre idx` with `idx` unique per entry (§2.2), each
   member's map is consistent. **Probe item:** that the `tokPrefixOk pre` premise of `tokShape`
   reaches a follower's apply from the log (the entry's decoded fact), not from the proposer's
   local `GenTokenPrefix`.
3. **Each member's published state after `SetUp`** (A2, not A1). authkv's checks run under
   `akAuthFixed γa ρ Lset n` (`examples/etcd/auth/WorkEnv.lean:84`). Its first row,
   `auth.authPubLb γa n`, says the member's store has published the history up to the set-up's
   last state. For member 1, `SetUp`'s post gives it, because the member applies its own
   `AuthEnable` before replying. For a follower, nothing gives it today. A2 needs a server law
   that produces it at member k: §3.

### 2.2 The token contract across members (the correction to the auth Scope §5)

**Confirmed at `2eaeb872b`** (code reading, plus a test of the part below the consistent index):

- The receiving member makes the prefix and puts it in the entry:
  `st, err := s.AuthStore().GenTokenPrefix()`, then
  `InternalAuthenticateRequest{Name: r.Name, SimpleToken: st}`, proposed by `raftRequest`
  (`server/etcdserver/v3_server.go:865-877`).
- Every member's apply passes the prefix and its consistent index to the store
  (`server/etcdserver/apply/backend.go:157-158`: `context.WithValue(… AuthenticateParamIndex{},
  a.options.ConsistentIndex.ConsistentIndex()), AuthenticateParamSimpleTokenPrefix{},
  r.SimpleToken)`). `authStore.Authenticate` calls `tokenProvider.assign`
  (`server/auth/store.go:353`), which makes `fmt.Sprintf("%s.%d", prefix, index)` and maps it to
  the user (`server/auth/simple_token.go:212-218`, `assignSimpleTokenToUser` `:125-144`).
- **The consistent index there is the same on every member: the previous entry's index.**
  - `applyEntryNormal`'s deferred step sets it to each entry's index when the entry is done
    (`server/etcdserver/server.go:1970-1980`).
  - The other way it moves is the batch transaction's in-apply hook (`server.go:2478-2485`, run
    by `LockInsideApply`). `Authenticate` reaches only a read transaction
    (`storage/schema/auth_users.go:25-30`, `GetUser`).
  - So at the `Authenticate` entry `n`, every member reads `n-1`, whether it applied `n-1`
    normally, at replay after a restart (`index ≥ n-1`, `< n`), or through a snapshot at `n-1`.
  - The token's number is not the entry's own index. That is etcd-io/etcd#18437 (closed;
    documented upstream as a known issue of simple tokens): `isValidSimpleToken` waits only for
    `n-1`, so a member that has applied `n-1` but not `n` passes the wait, misses the map, and
    refuses.
- **What is per member:** the map itself, and the TTL keeper (`simple_token.go:46-100`; 300 s idle
  expiry). `Recover` keeps the provider's map and does not rebuild it from the snapshot
  (`store.go:399-418`), and a restart starts empty. So a member refuses a valid token in four
  cases: it has not applied the entry yet (the wait, then the miss); it skipped the entry through
  a snapshot; it restarted; or the token expired there. Every case is `ErrInvalidAuthToken`, a
  refusal. The client then refreshes and retries (`client/v3/retry_interceptor.go:89-99, 157-171`:
  `shouldRefreshToken` on `ErrInvalidAuthToken` and `ErrAuthOldRevision`, and on `ErrUserEmpty`
  with a user name).
- **Test:** `notes/auth3-scope/zz_auth3_token_replicated_test.go` (copy into `server/auth`;
  `GOWORK=off go test ./auth/ -run TestAuth3 -v` passes). Three stores on separate backends apply
  the same set-up and `Authenticate` entry. Two of them assign the same token `pfx.42` to `root`,
  and `AuthInfoFromCtx` gives `root` on both. The third, which has not applied the entry, refuses
  it (`ErrInvalidAuthToken`). A store restarted on the first one's backend keeps the users and the
  enabled flag but refuses the token. The test takes the common consistent index as given; the
  code reading above shows it is common.
- Recorded: here, and as a correction in `notes/snapshot-auth-on-plan.md` (its sentence about
  "simple tokens are each member's own"). The auth Scope's §5 (`/shared/tmp/auth-safe/scope.md`,
  not in the repository) is superseded on this point by this section.

**What it means for the proof.**
- **A1 and A2: no change to the token contract.** Each client sends its token only to the member
  it authenticated at, and `clientv3.New` with one endpoint never fails over. That member
  proposed the `Authenticate` entry and replied after its own apply. So the client's token fact,
  `auth.tokIssued γa t u` at that member's `γa` (`auth/Tokens.lean:80`; authkv's
  `client.authTokReg_of … γa`, `Main.lean:282-315`), is the right one, and `info` at that member
  is checked against the same `γa.tok`.
- **B: the token fact must become cluster-level.** A client of every bridge uses a token at
  members other than its issuer's.
  - The natural form is a persistent fact read off the log: `tokIssuedC γk (simpleTok pre i) u`
    holds when the entry after index `i` is `Authenticate{Name = u, SimpleToken = pre}`. It is
    derived from `kvInvOn`'s log, and each member's `info` then yields `tokIssued γa_k t u'` with
    `tokIssuedC`, so `u = u'`.
  - That changes `NewServer.specM true`'s post, or the server's token clause in it, and the
    client's `authTokReg`. These are exported statements: a B-stage hard stop.
  - The client's refresh path is already proved (`Client__shouldRefreshToken.lean`,
    `Client__refreshToken.lean`, `Client__getToken.lean`).

### 2.3 Stale tokens and `ErrAuthOldRevision`: refusals only, so safe

- Writes are checked at apply, on every member, by the apply-time auth state, with the user and
  auth revision the receiving member put in the header (`v3_server.go:1073-1079`;
  `apply/auth.go:74`, `IsPutPermitted`). The checks are `isOpPermitted`'s: auth off allows
  everything, an empty user is `ErrUserEmpty`, and a header revision below the store's is
  `ErrAuthOldRevision` (`server/auth/store.go:862-901`). `AuthEnable` is before every workload
  entry in the log, so every member makes the same decision as the model (`kvModelOn`). A lagging
  receiving member that still has auth off sends an empty user, and the apply refuses it.
- Reads: `doSerialize` refuses with `ErrAuthOldRevision` if the revision moved during the read
  (`v3_server.go:1053-1055`).
- authkv makes no admin change after `SetUp`, and its frozen history (`authHistFrozen`) pins the
  state. So after the barrier no `ErrAuthOldRevision` arises at all. Before it, or in B, any that
  arises is a refusal, and authkv's `refused` admits any error (`Results.lean`'s docstring, "a
  refusal is any error").
- **No change to the statement.** The docstring keeps its "not exercised" line for role changes
  during the workload.

### 2.4 Snapshots with auth on

- **A's schedules send no snapshot.** putget3's members use `NoSnapCount`/`NoSnapCatchUp = 1 << 48`
  (`examples/lib/etcdstart/common.go:44-50`: "a leader never has to send a follower a snapshot"),
  and A copies them. A slow member is always caught up by entries.
- **B's do.** Partition's settings, `SnapCount = 1, SnapCatchUp = 1`
  (`examples/etcd/partition/linkv3p.go`, "a member a cut kept behind is caught up, once mended,
  by a snapshot"), send a snapshot carrying the auth buckets to a mended member.
- **How much of `notes/snapshot-auth-on-plan.md` is left: none of the install.**
  - Its Prove phase is done: `applySnapshot.specSnapM` and `applyAll.specSnapM` are proved
    (`ApplyAllSnapOn.lean`), and `run.wp_proofOn` and `applyAll.wp_proofOn` have no `sorry` (the
    plan's change log, P6). The sender's side (#7-on) is proved over `authBkLend`. The trust
    baseline has no snapshot sorry (`etc/tcb-baseline.txt`: four typed-points-to sorries only).
  - The install premises hold for partition's members: no compactor with auth on (`srvKVInvsOn`'s
    `E.cmp = false`, from `NewServer.specG`'s compactor premise). Partition's members have none:
    `etcdstart.NewMember` passes retention `0` (`common.go:163`).
  - The fork carries the fix for `issues/etcd-auth-snapshot-closed-backend-panic.md`
    (blocks-proof yes; `d52eec43e`).
- What B adds:
  - the token map not being in the snapshot, which is refusals only (§2.2);
  - the closed theorem resting, for the first time on a schedule that reaches it, on
    `authSchemaSrv`'s snapshot half (`authSchemaSnap`, `AuthSnapKit.lean`);
  - the plan's own suggested example ("An example after the Prove phase", 2026-11-02): a fixed cut
    that forces one install. It could be B's first step (§5).
- **Option for A (decision Q3):** run A with partition's snapshot settings instead of
  `NoSnapCatchUp`. Then a follower that falls behind under load may be caught up by a snapshot,
  so the install is reached at no new proof cost, if the probe confirms `NewServer.specM true`
  and `Start` compose at those settings (they are already generic in `snapCount`/`catchUp`:
  `common.go:44`, "NewServer's spec allows any values since 2026-10-30"). The Go test would report
  whether an install happened, as `linkv3p_test.go` does. Recommended no for A1, to keep its scope
  to recombination. Revisit for A2.

### 2.5 `authSchemaSrv` per member (the D22 question)

- `etcd_auth_safe` takes `hD22 : ∀ hG, ⊢ authSchemaSrv (GF := putgetGF) …`
  (`examples/etcd/auth/Results.lean`, `etcd_auth_safe`; `etcdserver/AuthSrv.lean`, the premise
  of `NewServer.specM true`). It is a closed proposition, quantified inside over the backend and
  names. Each member's `NewServer` uses it, so three members use the same hypothesis three
  times.
- **So D22 does not have to come first.** A carries exactly authkv's trust plus putget3's
  three-member start axioms (`EtcdServer.RaftHandler`, `http.Serve`), all already in the baseline.
- Two caveats:
  - B reaches `authSchemaSnap` on real schedules. Before B's closed theorem, re-run the axiom
    review of the snapshot half: S0 of the auth Scope refuted the whole text once (F1-F4, fixed by
    auth-schema-fix and re-reviewed 2026-11-13).
  - The open follow-ups of `notes/auth-unknown-fields-nested.md` stay open; they apply equally to
    one member and to three. One is (a): the persistent `↦□` on the nested `Options` and
    permission messages fixes `sizeCache`, which protobuf-go's `Marshal` writes. The other is (b):
    the client `send`'s `wireLen` bound.
- **Recommendation:** keep D22 a separate track. Do the snapshot-half review as B's S0, not
  before A.

## 3. Lagging members

**The driver.**
- Every read in `authkv.go` is linearizable. `Work`'s three `cli.Get`s (`authkv.go:209, 218, 222`)
  carry no `WithSerializable`. Every transaction writes, so it goes through raft. No helper in
  `examples/lib/etcdstart` uses `WithSerializable`.
- A linearizable `Range` calls `LinearizableReadNotify` before its check (`v3_server.go:138-149`).
  So at any member it waits until that member has applied past the leader's commit index at the
  read, which is past `AuthEnable` once `SetUp` returned. It never sees auth off.
- `Authenticate` also waits for a read index (`v3_server.go:838`). So `newUserClient` at a lagging
  member does not get `ErrAuthNotEnabled`, which `clientv3`'s `getToken` would take as "no token"
  (`client/v3/client.go:297-302`). It waits instead. The test checks this.
- Writes are checked at apply (§2.3).

**The watches are not covered.**
- `serverWatchStream.isWatchPermitted` (`server/etcdserver/api/v3rpc/watch.go:239-248`, called at
  creation `:289`) checks the member's own store, with no read index.
- So a follower that has not applied `AuthEnable` yet accepts:
  - the anonymous and bad principals' and v's watches of `c/` from revision 1 (`authkv.go:272`),
    which report the set-up's puts `c/<who>/d` and trip `Work`'s "watch outside [a, b) reported
    an event" panic;
  - root's history watch and u's watch (`:434`, `:445`), harmlessly: both are permitted anyway.
- The watch is not re-checked when the member later applies `AuthEnable`.
- The test, `nonissues/etcd-watch-lagging-member-auth-off/lagging_member_watch_test.go`
  (`tests/integration`; passes 3 of 3 at `2eaeb872b`), runs this sequence:
  1. A 3-member cluster puts `secret`.
  2. A follower is cut off (`InjectPartition`).
  3. Root is set up and auth is enabled through the leader.
  4. Through the follower, an anonymous watch of `secret` from revision 1 reports the put, and a
     serializable `Get` returns it.
  5. Through the leader, the anonymous `Get` is refused, and `Authenticate` through the follower
     times out instead of answering `ErrAuthNotEnabled`.

**Per variant.**
- **A1:** no exposure. Only member 1 serves, and it applied `AuthEnable` before replying to it
  (`raftRequest` waits for the proposer's own apply).
- **A2 and B:** exposed unless the driver closes it. **The driver fix:** after `SetUp`, for each
  member k, root's successful `Authenticate` (an explicit `root_k.Auth.Authenticate`, with
  `resp.Token != ""` checked) or a successful linearizable `Get` through a client of member k.
  Either way, `Failed` if it fails. After it, member k has applied past `AuthEnable`. The applied
  index only grows, an install only moves it forward, and nothing disables auth. So every later
  watch creation at member k sees `setupSt`.
- **What the proof needs from the barrier:** `auth.authPubLb γa_k n` at member k, the first row of
  `akAuthFixed` at k's names. The rest of `akAuthFixed` is cluster-level and already member-free:
  the frozen history, `srvReqLogLb`, and the read law `authStateAt_setup`, `AuthTieRead.lean`.
  Two routes:
  - (i) **Authenticate barrier:** if the server's `Authenticate` post, at the proposer, gives the
    store's publication after its own apply, as `SetUp`'s admin steps do, this is reuse. Then
    root's explicit `Authenticate` at member k gives `authPubLb γa_k (≥ n)`.
  - (ii) **Read barrier:** a new server law, "a read index served at member k, past the log
    position of entry i, gives `authPubLb γa_k` of the history up to i". It goes over the read
    loop's applied lower bound (`appliedAtLeast`) and the tie. It is cluster-general, B needs it
    for watch resumption at another member, and it touches `AuthTieRead.lean`, `ReqOn.lean` and
    the read specs.

  Recommend probing (i) first in S0. It needs no server change if the post already carries the
  publication.
- **An etcd issue?** No. Watch creation and serializable reads are documented local reads, and
  nothing promises that `AuthEnable` is in force on every member when it returns. Upstream treats
  the related simple-token behavior the same way (etcd-io/etcd#18437, documented as known).
  Recorded as `nonissues/etcd-watch-lagging-member-auth-off.md` (blocks-proof: no, since the
  driver avoids it), with the test.

## 4. Overlap with ongoing work

| Work | Files it touches | Overlap with auth3 | Order |
|---|---|---|---|
| **restart B2** (`/shared/etcd-grove-rs56`, `restart-s56`; `NewServer.wp_proofR`) | `etcdserver/NewServerR.lean` (new), `etcdserver/AuthSrv.lean` (widens `authStoreKit`'s pre), `etcdserver/InvRestart.lean` (`bootOkR`, landed), `notes/restart-s56-handoff.md` | A1 calls `server_new_auth_on` three times, exactly as authkv's `startServer` does once (`examples/etcd/auth/startServer.lean`, `Results.lean`'s `authkv_startServer`). If B2 changes `NewServer.specM true`'s statement or `authSchemaSrv`, auth3's start adapts the same way authkv's does. No shared file. | Independent. Whichever lands second rebases mechanically. No need to wait. |
| **k8s 7f** (`/shared/etcd-grove-k8s7f`, `k8s-7f5`; next the 7f-3b v3rpc part, then the 7f-3c client part) | v3rpc: `serverWatchStream__recvLoop.lean`, `serverWatchStream__sendLoop.lean`, `WatchApi.lean` (`wrespIs`, `watchReqOkP` in `upOk`, the stopgap `wrespRO`), `IsCreateEvent`; client watch: `client.rawRespOkP`, `notes/k8s-7f3a-draft.md` §5 | authkv's watch proofs (`RootWatch.lean`, `Work.lean`'s refused watch, `etcdstart.Collect`) consume these specs. 7f adapts authkv when it lands, and auth3 reuses authkv's lemmas, so it inherits the adaptation. A2's barrier needs no v3rpc change on route (i). Route (ii) touches the read side (`ReqOn`, read specs), not the watch files. | A1's Go and alloc can start now. Start A1's `Main` proof after 7f-3b's v3rpc part lands (it is next for 7f), or rebase onto it. A2 after 7f-3c if 7f-3c restates the client watch specs authkv uses. |
| **D22** (discharge of `authSchemaSrv`; not started) | `etcdserver/AuthSrv.lean`, `AuthSnapKit.lean`, schema's auth backend, `InvAuth.lean`'s contracts | None for A: the same hypothesis. For B: the snapshot-half review (§2.5). | A does not wait. B's S0 re-reviews the snapshot half. |
| **out_size C2, WAL, crash rung 3** | collections and `etcd_adequate_members`' signature | auth3's new collection `etc/tcb-collections/auth3.txt` and its adequacy copy follow whatever they do to putget3's. | Mechanical. |

## 5. Stages, hard stops, estimates

**S0: probe (0.5 to 1 day, Lean in a scratch file, unlinked, not landed).**
- `alloc3On` composes: `srvClusterBootOn_alloc` at three peers and `srvMemberBootOn_alloc` three
  times. Elaborate the statement and the first steps.
- A follower's apply of an `Authenticate` entry gets `tokPrefixOk` from the log (§2.1, item 2).
- For A2: does the server's `Authenticate` (the proposer's reply) give `authPubLb γa` (route (i),
  §3)?
- **CP0:** the findings. Stop if any fails.

**S1: A1 (4 to 6 days).**
1. Go, about 150 lines: `examples/etcd/auth3/auth3.go`.
   - `startMember` with auth on: `etcdstart.NewMember`'s configuration plus
     `AuthToken: "simple", TokenTTL: 300`, the peer listener and `RaftHandler`, `Start`. This
     could be a new `etcdstart.StartMemberAuth`; recommend auth3's own function, so that
     `etcdstart`'s proved specs do not move.
   - `Main`: three members, `Serve` on member 1, then authkv's body. It imports `SetUp`, `Work`,
     `CheckHistory`, `LastIn`, `Principals` and `Permitted` from package `auth`, and copies the
     unexported `newUserClient` (10 lines).
   - A Go test in the style of `authkv_test.go`.
   - Addresses that no other example uses.
   - Goose (`etc/goose.py`, the examples project), `etc/gen-init.py`, the package table.
2. Lean:
   - `lib/etcdstart/Alloc3On.lean` (about 350 lines);
   - `auth3/startMember.lean`, authkv's `startServer` proof with putget3's peer serving
     (about 250);
   - `auth3/Main.lean`, putget3's start then authkv's body (about 300). To make this cheap,
     factor authkv's `Main.wp_proof` after the start (from `etcdstart.Serve` on) into a lemma
     over the served member's resources. That is an internal refactor of
     `examples/etcd/auth/Main.lean`, form only, with no statement change;
   - `Adequacy.lean`, a copy of putget3's (167 lines) with `hD22` and authkv's pure premises;
   - `Results.lean`, with `#print axioms`;
   - the collection `etc/tcb-collections/auth3.txt`;
   - the link input.
3. **CP1 (hard stop: a new closed statement):** the statement, the docstring's "What the result
   does not say" (authkv's list, plus: the followers serve no request; no snapshot), and the
   collection diff. Expected: authkv's axioms ∪ putget3's, no sorry, no new axiom.

**S2: A2 (5 to 9 days, after S1 lands and after 7f-3b).**
1. Go: `Serve` on every member, each principal's client on its member, and the barrier (§3; root
   per member).
2. Lean:
   - route (i), reuse; or route (ii), the new read-barrier law (a server-level internal lemma,
     2 to 4 days of the estimate);
   - per-member `akAuthFixed`;
   - `Work` at member k's `srv`/`E`/`γa`. `Work`'s spec is already parameterized by them:
     `Main.lean:383`, `wp_Work _ _ (akV R) srv E ρ cid mid γa …`.
3. **CP2:** any statement change on a server result (route (ii) adds a law, not a change), then
   the closed statement.

**S3: B (several weeks; Scope it again after S2).** In order:
1. the snapshot-half review of `authSchemaSrv` (axiom skill);
2. the cluster-level token fact `tokIssuedC` and the restated `NewServer.specM true` post (hard
   stop: an exported statement);
3. the client's re-authentication across members;
4. a fixed-cut example that forces one install (the snapshot plan's 2026-11-02 example), as a
   cheap first closed theorem with snapshots and auth;
5. the partition schedules with authkv's checks.

**Hard stops in this plan:**
- CP0, if a probe fails;
- CP1, a new closed statement;
- S2, any server statement change;
- B, the exported token contract and the snapshot-half review.

No axiom or trusted text is planned for A.

## 6. Decisions needed

- **Q1: the variant order.**
  - (A) A1, then A2, then B.
  - (B) Go straight to A2.
  - (C) B first.

  **Recommend A.** A1 is cheap recombination and the base of A2. A2 isolates the one new law. B
  needs that law and three more pieces.
- **Q2: A2's barrier.**
  - (i) root's explicit `Authenticate` per member, if S0 shows it gives `authPubLb`.
  - (ii) a linearizable `Get` per member, with the new read-barrier law.

  **Recommend (i) if the probe confirms it, else (ii).** (ii) is needed for B anyway.
- **Q3: snapshot settings in A.** `NoSnapCatchUp` (no installs), or partition's (installs may
  happen, with no new proof expected). **Recommend `NoSnapCatchUp` for A1**, and reconsider for A2.
- **Q4: D22 order.** **Recommend:** not before A. Before B, a re-review of `authSchemaSnap`.
  Discharging it stays its own track.
- **Q5: the start in Go.** auth3's own `startMember`, or a shared `etcdstart.StartMemberAuth`.
  **Recommend auth3's own**, keeping `etcdstart`'s specs and the other examples untouched.
- **Q6: reuse of authkv's proof.** Factor authkv's `Main.wp_proof` body after the start into a
  lemma (internal, form only, so decided by the agent and listed at CP1), or copy it. **Recommend
  factoring.**
- **Q7: the non-issue.** `nonissues/etcd-watch-lagging-member-auth-off.md` is committed with this
  Scope, blocks-proof no. Confirm the classification. A filing upstream would be a documentation
  request at most, in the vein of etcd-io/etcd#18437.

## 7. Evidence index

- Token replication: `notes/auth3-scope/zz_auth3_token_replicated_test.go`; code at `2eaeb872b`:
  `server/etcdserver/v3_server.go:865-877`, `apply/backend.go:157-158`, `server/auth/store.go:337-363,
  399-418`, `simple_token.go:125-144, 212-246`, `server.go:1970-1980, 2477-2484`,
  `storage/schema/auth_users.go:25-30`; upstream etcd-io/etcd#18437.
- Lagging member: `nonissues/etcd-watch-lagging-member-auth-off.md` and its test;
  `v3rpc/watch.go:239-248, 289`, `v3_server.go:138-149, 838, 1035-1057`, `client/v3/client.go:285-307`.
- Writes at apply: `v3_server.go:1073-1079`, `apply/auth.go:74`, `server/auth/store.go:862-901`.
- The proof's names: `NewServerAllocOn.lean:56`, `Results.lean:2166`, `MainAlloc.lean:60`,
  `KVAuthModel.lean:832, 900`, `auth/Model.lean:361`, `auth/Tokens.lean:80`, `WorkEnv.lean:84`,
  `AuthTieRead.lean` (header), `Alloc3.lean:311`, `common.go:44-50, 163`.
